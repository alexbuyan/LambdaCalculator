module Parser where

import LambdaCalculus
import Text.ParserCombinators.Parsec

instance Show Expr where
    show (Var v) = v
    show (Var v1 :@ Var v2) = v1 ++ " " ++ v2
    show (Var v :@ e) = v ++ " (" ++ show e ++ ")"
    show (e1 :@ e2) = "(" ++ show e1 ++ ") (" ++ show e2 ++ ")"
    show (Lam v e) = "\\" ++ v ++ " -> " ++ show e

instance Read Expr where
    readsPrec _ s = case parseStr s of
        Left _  -> undefined
        Right v -> [(v, "")]

parseStr :: String -> Either ParseError Expr
parseStr = parse (do
    expr <- parseExpr
    eof
    return expr) ""

parseId :: Parser String
parseId = do
    l <- letter
    dig <- many alphaNum
    _ <- spaces
    return (l : dig)

parseVar :: Parser Expr
parseVar = Var <$> parseId

parseExprInBrackets :: Parser Expr
parseExprInBrackets = do
    _ <- char '(' >> spaces
    expr <- parseExpr
    _ <- char ')' >> spaces
    return expr

parseExpr :: Parser Expr
parseExpr = try parseTerm <|> try parseAtom

parseAtom :: Parser Expr
parseAtom = try parseLam <|> try parseVar <|> try parseExprInBrackets

parseTerm :: Parser Expr
parseTerm = parseAtom `chainl1` return (:@)

parseLam :: Parser Expr
parseLam = do
    _ <- char '\\' >> spaces
    ids <- many1 parseId
    _ <- string "->" >> spaces
    expr <- parseExpr
    return $ foldr Lam expr ids

{-
(read "\\x1 x2 -> x1 x2 x2" :: Expr) == Lam "x1" (Lam "x2" (Var "x1" :@ Var "x2" :@ Var "x2"))

cY = let {x = Var "x"; f = Var "f"; fxx = Lam "x" $ f :@ (x :@ x)} in Lam "f" $ fxx :@ fxx
read (show cY) == cY
-}