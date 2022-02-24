module Methods where


import LambdaCalculus
import Data.List

infix  1 `alphaEq`
infix  1 `betaEq`

freeVars :: Expr -> [Symb]
freeVars (Var v)   =  [v]
freeVars (left :@ right)  = freeVars left `union` freeVars right
freeVars (Lam var expr) = freeVars expr \\ [var]

makeUnique :: Symb -> [Symb] -> [Symb] -> Symb
makeUnique s symb1 symb2 | elem s symb1 || elem s symb2 = makeUnique (s ++ ['\'']) symb1 symb2
                         | otherwise = s

subst :: Symb -> Expr -> Expr -> Expr
subst s e var@(Var v) | s == v = e
                      | otherwise = var
subst s e (left :@ right) = subst s e left :@ subst s e right
subst s e lam@(Lam var expr) | var == s = lam
                             | otherwise = if var `elem` freeVars e
                                           then Lam l (subst s e (subst var (Var l) expr))
                                           else Lam var (subst s e expr)
                                             where l = makeUnique var (freeVars e) (freeVars expr)

alphaEq :: Expr -> Expr -> Bool
alphaEq (Var v1) (Var v2) = v1 == v2
alphaEq (left1 :@ right1)  (left2 :@ right2)  = (left1 `alphaEq` left2) && (right1 `alphaEq` right2)
alphaEq (Lam v1 e1) (Lam v2 e2) | v1 == v2 = e1 `alphaEq` e2
                                | otherwise = notElem v1 (freeVars e2) && (e1 `alphaEq` subst v2 (Var v1) e2)
alphaEq _ _ = False


reduceOnce :: Expr -> Maybe Expr
reduceOnce (Var _) = Nothing
reduceOnce ((Lam v e) :@ right) = Just (subst v right e)
reduceOnce (left :@ right) = case reduceOnce left of
     Nothing -> case reduceOnce right of
          Nothing -> Nothing
          Just right' -> Just (left :@ right')
     Just left' -> Just (left' :@ right)
reduceOnce (Lam v e) = case reduceOnce e of
     Nothing -> Nothing
     Just e' -> Just (Lam v e')


nf :: Expr -> Expr
nf e = maybe e nf $ reduceOnce e

betaEq :: Expr -> Expr -> Bool
betaEq e1 e2 = nf e1 `alphaEq` nf e2