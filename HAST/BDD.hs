{-# LANGUAGE RecordWildCards #-}

module HAST.BDD(compileBDD) where

import Control.Monad.State
import Control.Monad.ST
import Data.Bits
import Debug.Trace

import Util hiding (trace)
import CuddExplicitDeref
import Interface
import HAST.HAST

block :: (STDdManager s u -> DDNode s u -> DDNode s u -> ST s (DDNode s u)) -> (STDdManager s u -> DDNode s u) -> STDdManager s u -> [DDNode s u] -> ST s (DDNode s u)
block func s m nodes = do
    ref (s m)
    go (s m) nodes
    where
    go accum []     = return accum
    go accum (n:ns) = do
        accum' <- func m accum n
        deref m accum
        deref m n
        go accum' ns

conj = block band bone
disj = block bor  bzero

ccase :: STDdManager s u -> [(DDNode s u, DDNode s u)] -> ST s (DDNode s u)
ccase m = go (bzero m) (bzero m)
    where
    go accum neg [] = do
        deref m neg
        return accum
    go accum neg ((cond, cas): cs) = do
        --alive == cond, cas, accum, neg
        econd  <- band m cond (bnot neg)
        clause <- band m econd cas
        deref m econd
        deref m cas
        --alive == cond, accum, neg, clause
        accum' <- bor m clause accum
        deref m accum
        deref m clause
        --alive == cond, neg, accum'
        neg' <- bor m cond neg
        deref m cond
        deref m neg
        --alive == accum', neg'
        go accum' neg' cs



compileBDD :: (Show v) => STDdManager s u -> VarOps pdb v s u -> AST [DDNode s u] [DDNode s u] (DDNode s u) v -> StateT pdb (ST s) (DDNode s u)
compileBDD m VarOps{..} = compile' where
    binOp func m x y = do
        x <- compile' x
        y <- compile' y
        res <- lift $ func m x y 
        lift $ deref m x
        lift $ deref m y
        return res

    getAVar (FVar f)       = return f
    getAVar (EVar e)       = return e
    getAVar (NVar v)       = getVar v

    withTmpMany n f = withTmpMany' [] n f
    withTmpMany' nodes 0 f = f nodes
    withTmpMany' nodes n f = withTmp (\node -> withTmpMany' (node:nodes) (n-1) f)

    compile' T             = do
        lift $ ref $ bone m
        return $ bone m
    compile' F             = do
        lift $ ref $ bzero m
        return $ bzero m
    compile' (Not x)       = liftM bnot $ compile' x
    compile' (And x y)     = binOp band m x y
    compile' (Or x y)      = binOp bor m x y
    compile' (XNor x y)    = binOp bxnor m x y
    compile' (Imp x y)     = binOp bimp m x y
        where
        bimp m x y = bor m (bnot x) y
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
        lift $ xeqy m x y
    compile' (EqConst x c) = do
        x <- getAVar x
        lift $ computeCube m x $ bitsToBoolArrBe (length x) c

    compile' (Exists w f) | w <= 0    = error $ "compileBDD error: cannot quantify " ++ show w ++ " bits"
                          | otherwise = withTmpMany w $ \x -> do
        res' <- compile' $ f x
--        lift $ foldM (\r v -> do res <- bexists m r v
--                                 deref m r
--                                 return res) res' x
        xcube <- lift $ nodesToCube m x
        res  <- lift $ bexists m res' xcube
        lift $ deref m xcube
        lift $ deref m res'
        return res
    compile' (NExists n w f) | w <= 0    = error $ "compileBDD error: cannot quantify " ++ show w ++ " bits"
                             | otherwise = withTmpMany w $ \x -> do
        res' <- compile' $ f x
        xcube <- lift $ nodesToCube m x
        --sz'  <- lift $ dagSize res'
        --sup  <- lift $ supportIndices m res'
        res  <- lift $ {-trace ("quantifying " ++ show n ++ " dagsize " ++ show sz' ++ " support " ++ (show (length sup))) $-} bexists m res' xcube
        --sz   <- lift $ dagSize res
        --trace ("dagsize after quantification " ++ show sz) $ return ()
        lift $ deref m xcube
        lift $ deref m res'
        return res
    compile' (Var x)       = do
        [x] <- getAVar x
        lift $ ref x
        return x
    compile' (Let x f)     = do
        bind <- compile' x
        res  <- compile' (f bind)
        lift $ deref m bind
        return res
    compile' (LetLit x)    = do
        lift $ ref x
        return x
