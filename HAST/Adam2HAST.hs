module HAST.Adam2Hast where

import Control.Arrow

import HAST.HAST as H
import AdamAbstractor.Backend as A

convert :: A.AST f v c var -> H.AST f v c var
convert A.T                     = H.T
convert A.F                     = H.F
convert (A.Not x)               = H.Not (convert x)
convert (A.And x y)             = H.And (convert x) (convert y)
convert (A.Or x y)              = H.Or (convert x) (convert y)
convert (A.Imp x y)             = H.Imp (convert x) (convert y)
convert (A.XNor x y)            = H.XNor (convert x) (convert y)
convert (A.Conj xs)             = H.Conj (map convert xs)
convert (A.Disj xs)             = H.Disj (map convert xs)
convert (A.Case xs)             = H.Case (map (convert *** convert) xs)
convert (A.EqVar (Left  x) y)   = H.EqVar (FVar x) (NVar y)
convert (A.EqVar (Right x) y)   = H.EqVar (NVar x) (NVar y)
convert (A.EqConst (Left  x) c) = H.EqConst (FVar x) c
convert (A.EqConst (Right x) c) = H.EqConst (NVar x) c
convert (A.Exists func)         = H.Exists 1 (convert . func)
convert (A.QuantLit v)          = H.Var (EVar v)
convert (A.Let x f)             = H.Let (convert x) (convert . f)
convert (A.LetLit x)            = H.LetLit x

