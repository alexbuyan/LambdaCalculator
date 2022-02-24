module LambdaCalculus where

infixl 2 :@

type Symb = String 

data Expr = Var Symb
          | Expr :@ Expr
          | Lam Symb Expr
          deriving (Eq)
