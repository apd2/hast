{-# LANGUAGE RecordWildCards, TemplateHaskell, FlexibleContexts, ScopedTypeVariables, ConstraintKinds #-}

module HAST.BDD(compileBDD, compileBDD') where

import Control.Monad.State
import Control.Monad.ST
import Data.Bits
import Debug.Trace
import Control.Monad.Morph
import qualified Data.Map.Strict as Map
import Data.Map.Strict (Map)

import Util hiding (trace)
import Cudd.Imperative
import Synthesis.Interface
import Synthesis.Resource
import Synthesis.RefineCommon
import HAST.HAST

block :: (RM s u t) => 
         (STDdManager s u -> DDNode s u -> DDNode s u -> ST s (DDNode s u)) -> 
         (STDdManager s u -> DDNode s u) -> 
         STDdManager s u -> 
         [DDNode s u] -> 
         t (ST s) (DDNode s u)
block func s m nodes = do
    $rp ref (s m)
    go (s m) nodes
    where
    go accum []     = return accum
    go accum (n:ns) = do
        accum' <- $r2 (func m) accum n
        $d (deref m) accum
        $d (deref m) n
        go accum' ns

conj, disj :: (RM s u t) 
           => STDdManager s u 
           -> [DDNode s u] 
           -> t (ST s) (DDNode s u)
conj = block bAnd bOne
disj = block bOr  bZero

ccase :: (RM s u t) => STDdManager s u -> [(DDNode s u, DDNode s u)] -> t (ST s) (DDNode s u)
ccase m = go (bZero m) (bZero m)
    where
    go accum neg [] = do
        $d (deref m) neg
        return accum
    go accum neg ((cond, cas): cs) = do
        --alive == cond, cas, accum, neg
        econd  <- $r2 (bAnd m) cond (bNot neg)
        clause <- $r2 (bAnd m) econd cas
        $d (deref m) econd
        $d (deref m) cas
        --alive == cond, accum, neg, clause
        accum' <- $r2 (bOr m) clause accum
        $d (deref m) accum
        $d (deref m) clause
        --alive == cond, neg, accum'
        neg' <- $r2 (bOr m) cond neg
        $d (deref m) cond
        $d (deref m) neg
        --alive == accum', neg'
        go accum' neg' cs

compileBDD' :: forall v s u pdb. (Show v) 
           => STDdManager s u 
           -> VarOps pdb v s u 
           -> (v -> Maybe String)                          -- returns BDD variable group tag for a variable
           -> AST [DDNode s u] [DDNode s u] (DDNode s u) v 
           -> StateT pdb (ST s) (DDNode s u)
compileBDD' m vo ft ast = hoist (liftM fst . (runResource :: Monad m => InUse (DDNode s u) -> (ResourceT (DDNode s u)) m a -> m (a, InUse (DDNode s u))) Map.empty) $ (compileBDD m vo ft ast :: StateT pdb (ResourceT (DDNode s u) (ST s)) (DDNode s u))

compileBDD :: forall v s u t pdb. (Show v, RM s u t) 
           => STDdManager s u 
           -> VarOps pdb v s u 
           -> (v -> Maybe String)                          -- returns BDD variable group tag for a variable
           -> AST [DDNode s u] [DDNode s u] (DDNode s u) v 
           -> StateT pdb (t (ST s)) (DDNode s u)
compileBDD m VarOps{..} ftag = compile' where

    binOp :: forall t. RM s u t => (STDdManager s u -> DDNode s u -> DDNode s u -> ST s (DDNode s u))
          -> STDdManager s u 
          -> AST [DDNode s u] [DDNode s u] (DDNode s u) v
          -> AST [DDNode s u] [DDNode s u] (DDNode s u) v
          -> StateT pdb (t (ST s)) (DDNode s u)
    binOp func m x y = do
        x <- compile' x
        y <- compile' y
        res <- lift $ $r2 (func m) x y 
        lift $ $d (deref m) x
        lift $ $d (deref m) y
        return res

    getAVar :: forall t. RM s u t => ASTVar [DDNode s u] [DDNode s u] v -> StateT pdb (t (ST s)) [DDNode s u]
    getAVar (FVar f)       = return f
    getAVar (EVar e)       = return e
    getAVar (NVar v)       = hoist lift $ getVar v (ftag v) --TODO fix when Interface.hs uses resource monad

    withTmpMany :: forall t. RM s u t => Int -> ([DDNode s u] -> StateT pdb ((ResourceT (DDNode s u)) (ST s)) (DDNode s u)) -> StateT pdb (t (ST s)) (DDNode s u)
    withTmpMany n f = do
        (res :: DDNode s u) <- hoist lift $ withTmpMany' [] n f
        lift $ $rr $ return res
        return res

    withTmpMany' :: [DDNode s u] -> Int -> ([DDNode s u] -> StateT pdb ((ResourceT (DDNode s u)) (ST s)) (DDNode s u)) -> StateT pdb (ST s) (DDNode s u)
    withTmpMany' nodes 0 f = hoist (liftM fst . runResource Map.empty) $ f nodes
    withTmpMany' nodes n f = withTmp (\node -> withTmpMany' (node:nodes) (n-1) f)

    compile' :: forall t. RM s u t => AST [DDNode s u] [DDNode s u] (DDNode s u) v 
             -> StateT pdb (t (ST s)) (DDNode s u)

    compile' T             = do
        lift $ $rp ref $ (bOne m :: DDNode s u)
        return $ bOne m
    compile' F             = do
        lift $ $rp ref $ (bZero m :: DDNode s u)
        return $ bZero m
    compile' (Not x)       = liftM bNot $ compile' x
    compile' (And x y)     = binOp bAnd m x y
    compile' (Or x y)      = binOp bOr m x y
    compile' (XNor x y)    = binOp bXnor m x y
    compile' (Imp x y)     = binOp bimp m x y
        where
        bimp m x y = bOr m (bNot x) y
    compile' (Conj es)     = do
        es <- sequence $ map compile' es
        lift $ conj m es
    compile' (Disj es)     = do
        es <- sequence $ map compile' es
        lift $ disj m es
    compile' (Case cs)     = do
        cs <- sequence $ map func cs 
        lift $ ccase m cs
        where
        func (x, y) = do
            x <- compile' x
            y <- compile' y
            return (x, y)
    compile' (EqVar x y)   = do
        x <- getAVar x
        y <- getAVar y
        lift $ $r $ xEqY m x y --TODO reference counting
    compile' (EqConst x c) = do
        x <- getAVar x
        lift $ $r $ computeCube m x $ bitsToBoolArrBe (length x) c --TODO reference counting
    compile' (Exists w f) 
        | w <= 0    = error $ "compileBDD error: cannot quantify " ++ show w ++ " bits"
        | otherwise = withTmpMany w $ \x -> do
            res' <- compile' $ f x
            xcube <- lift $ $r $ nodesToCube m x --TODO reference counting
            res  <- lift $ $r2 (bExists m) res' xcube
            lift $ $d (deref m) xcube
            lift $ $d (deref m) res'
            return res
    compile' (NExists n w f) 
        | w <= 0    = error $ "compileBDD error: cannot quantify " ++ show w ++ " bits"
        | otherwise = withTmpMany w $ \x -> do
            res' <- compile' $ f x
            xcube <- lift $ $r $ nodesToCube m x --TODO reference counting
            res  <- lift $ $r2 (bExists m) res' xcube
            lift $ $d (deref m) xcube
            lift $ $d (deref m) res'
            return res
    compile' (Var x)       = do
        [x] <- getAVar x
        lift $ $rp ref x
        return x
    compile' (Let x f)     = do
        bind <- compile' x
        res  <- compile' (f bind)
        lift $ $d (deref m) bind
        return res
    compile' (LetLit x)    = do
        lift $ $rp ref x
        return x
