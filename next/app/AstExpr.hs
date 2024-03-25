module AstExpr (
  Expr(..),
  parse
) where

import Data.Bifunctor
import Ewe
import Sexpr

data Expr =
    Var String
  | Lam String Expr
  | App Expr Expr
  | Pi String Expr Expr
  | Eq Expr Expr Expr
  | LZero
  | LSucc Expr
  | LMax Expr Expr
  | Level Integer
  | Type Integer Expr
  | LetEq String String Expr Expr  -- let x, x_eq = e in e
  | Ann Expr Expr
  deriving Show

data ParseError =
    InvalidExpr Sexpr
  | InvalidVar Sexpr
  | InvalidBind Sexpr
  | InvalidLevel Sexpr
  | InvalidSexpr String

instance Show ParseError where
  show (InvalidExpr s) = concat ["Invalid Expression: `", show s, "`"]
  show (InvalidVar s) = concat ["Invalid Variable: `", show s, "`"]
  show (InvalidBind s) = concat ["Invalid Bind: `", show s, "`"]
  show (InvalidLevel s) = concat ["Invalid Level: `", show s, "`"]
  show (InvalidSexpr s) = concat ["Invalid S-Expression: `", s, "`"]

parse :: String -> Either String Expr
parse s =
    either
      (Left . show)
      Right
      (maybe
        (Left (InvalidSexpr s))
        parseExpr
        (runParser sexprP s))

parseExpr :: Sexpr -> Either ParseError Expr
parseExpr (Atom x) = Var <$> parseVar (Atom x)
parseExpr (List (Atom "λ" : l@(_ : _ : _))) = do
  let (xs, b) = manyThen l
  xs <- mapM (parseVar) xs
  b <- parseExpr b
  pure (foldr Lam b xs)
parseExpr (List (Atom "->" : l@(_ : _ : _))) = do
  let (xs, b) = manyThen l
  xs <- mapM parseBind xs
  b <- parseExpr b
  pure (foldr (uncurry Pi) b xs)
parseExpr (List [Atom "=", t, a, b]) =
  Eq <$> parseExpr t <*> parseExpr a <*> parseExpr b
parseExpr (List [Atom "Level", n]) = Level <$> parseLevel n
parseExpr (List [Atom "lzero"]) = pure LZero
parseExpr (List [Atom "lsucc", e]) = LSucc <$> parseExpr e
parseExpr (List [Atom "lmax", l, r]) = LMax <$> parseExpr l <*> parseExpr r
parseExpr (List [Atom "Type", n, e]) = Type <$> parseLevel n <*> parseExpr e
parseExpr (List [e, Atom ":", t]) = Ann <$> parseExpr e <*> parseExpr t
parseExpr (List (f : args)) = foldl App <$> parseExpr f <*> mapM parseExpr args
parseExpr s = Left (InvalidExpr s)

isVariable :: String -> Bool
isVariable =
  not .
  flip elem
    ["λ", "->", "=", "β=", "Level", "lzero", "lsucc", "Type", ":"]

parseVar :: Sexpr -> Either ParseError String
parseVar (Atom x) | isVariable x = pure x
parseVar s = Left (InvalidVar s)

parseBind :: Sexpr -> Either ParseError (String, Expr)
parseBind (List [x, Atom ":", t]) = (,) <$> parseVar x <*> parseExpr t
parseBind s = Left (InvalidBind s)

parseLevel :: Sexpr -> Either ParseError Integer
parseLevel (Atom n) = maybe (Left (InvalidLevel (Atom n))) pure (readMaybe n)
parseLevel s = Left (InvalidLevel s)

manyThen :: [Sexpr] -> ([Sexpr], Sexpr)
manyThen [x] = ([], x)
manyThen (hd : tl) = first (hd :) (manyThen tl)

readMaybe :: Read a => String -> Maybe a
readMaybe = foldr (\(a, _) _ -> Just a) Nothing . reads
