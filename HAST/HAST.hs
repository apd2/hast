module HAST.HAST(AST(..),
                 ASTVar(..),
                 existsMany) where


-- f   == type of anonymous free variables 
-- e   == type of variables bound by exists statements 
-- c   == type of single bit variables bound by let statements
-- var == type of free variable identifiers

data ASTVar f e v = FVar f
                  | EVar e
                  | NVar v

data AST f e c v = T
                 | F
                 | Not     (AST f e c v)
                 | And     (AST f e c v) (AST f e c v)
                 | Or      (AST f e c v) (AST f e c v)
                 | Imp     (AST f e c v) (AST f e c v)
                 | XOr     (AST f e c v) (AST f e c v)
                 | XNor    (AST f e c v) (AST f e c v)
                 | Conj    [AST f e c v]
                 | Disj    [AST f e c v]
                 | Case    [(AST f e c v, AST f e c v)]
                 | Var     (ASTVar f e v)                 -- only valid for 1-bit variables
                 | EqVar   (ASTVar f e v) (ASTVar f e v)  -- variables must have the same width
                 | EqConst (ASTVar f e v) Int
                 | Exists  Int (e -> AST f e c v)
                 | Let     (AST f e c v) (c -> AST f e c v)
                 | LetLit  c

existsMany :: [Int] -> ([e] -> AST f e c v) -> AST f e c v
existsMany ws f = existsMany' ws [] f

existsMany' :: [Int] -> [e] -> ([e] -> AST f e c v) -> AST f e c v
existsMany' []     vs f = f vs
existsMany' (w:ws) vs f = Exists w (\x -> existsMany' ws (vs++[x]) f)

--newtype TAST sp lp = TAST forall f e c . AST f e c (BAVar sp lp)
--type TASTVar sp lp = forall f e   . ASTVar f e (BAVar sp lp)


