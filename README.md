# LambdaCalculator
Для взаимодействия с библиотекой понадобится [ghci](https://downloads.haskell.org/~ghc/9.0.1/docs/html/users_guide/ghci.html). Чтобы запустить парсер откройте терминал и введите
```bash
$ ghci Main.hs
```
Теперь вам доступны все реализованные [методы](https://github.com/alexbuyan/LambdaCalculator/blob/main/Methods.hs)

## Пример работы с библиотекой
```haskell
# substituion
GHCi> subst "y"  (Var "x")  (Lam "x" $ (Var "x") :@ (Var "y"))
\x' -> x' x

# alpha equivalence
GHCi> (Lam "x" $ Lam "y" $ Var "x") `alphaEq` (Lam "y" $ Lam "x" $ Var "y")
True

# beta reduction
GHCi> reduceOnce $ Lam "x" $ Lam "y" $ Var "x"
Nothing
GHCi> reduceOnce $ Lam "x" $ Lam "y" $ (Lam "z" $ Var "z") :@ Var "x"
Just \x -> \y -> x
GHCi> let omega = Lam "x" $ Var "x" :@ Var "x" in reduceOnce $ omega :@ omega
Just (\x -> x x) (\x -> x x)

# reduction to NF
GHCi> nf (fac :@ three) `alphaEq` six
True

# beta equivalence
GHCi> fac :@ three `betaEq` six
True
```

Тип данных `Expr` является представителем `Show` и `Read` и строковое представление всегда является валидным лямбда-термом
```haskell
GHCi> show $ Lam "x" (Var "x" :@ Var "y")
"\\x -> x y"
GHCi> cY = let {x = Var "x"; f = Var "f"; fxx = Lam "x" $ f :@ (x :@ x)} in Lam "f" $ fxx :@ fxx
GHCi> show cY
"\\f -> (\\x -> f (x x)) (\\x -> f (x x))"
GHCi> cY
\f -> (\x -> f (x x)) (\x -> f (x x))
```