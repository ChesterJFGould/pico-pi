module Syntax where

import Control.Applicative
import Ewe
import Sexpr
import Symbol

data Theory = Theory [Stmt]

data Stmt =
    Cons Symbol ConsType
  | Dest Symbol DestType
  | Sort Symbol SortType
  | Let Symbol Expr Expr

data Params a = Params [(Symbol, a)]

data ConsType = ConsType (Params MetaType) (Params MetaType) Expr

data DestType = DestType (Params MetaType) (Params Expr) (Params MetaType) Expr

data SortType = SortType (Params MetaType)

data MetaType = MetaType (Params Expr) Expr

data Expr =
    Var Symbol
  | App Symbol [Binding]
  | Ann Expr Expr

data Binding =
    Binding [Symbol] Expr
  | BindingExpr Expr

data ParseError =
    InvalidStmt Sexpr
  | InvalidParams Sexpr
  | InvalidParam Sexpr
  | InvalidIdent Sexpr
  | InvalidExpr Sexpr
  deriving Show

type Parse a = Either ParseError a

parseError :: ParseError -> Parse a
parseError err = Left err

parseTheory :: String -> Either String Theory
parseTheory s = maybe (Left "sexpr parse error") (either (Left . show) Right . parseTheory') (runParser (many (whitespace *> sexprP <* whitespace) <* eof) s)

parseTheory' :: [Sexpr] -> Parse Theory
parseTheory' s = Theory <$> traverse parseStmt s

parseStmt :: Sexpr -> Parse Stmt
parseStmt (List [Atom "constructor", x, impls, args, codom]) =
  Cons <$> parseIdent x <*>
    ( ConsType
      <$> parseParams parseMetaType impls
      <*> parseParams parseMetaType args
      <*> parseExpr codom
    )
parseStmt (List [Atom "destructor", x, impls, subjs, args, codom]) =
  Dest <$> parseIdent x <*>
    ( DestType
      <$> parseParams parseMetaType impls
      <*> parseParams parseExpr subjs
      <*> parseParams parseMetaType args
      <*> parseExpr codom
    )
parseStmt (List [Atom "sort", x, args]) =
  Sort <$> parseIdent x <*>
    ( SortType
      <$> parseParams parseMetaType args
    )
parseStmt (List [Atom "let", x, Atom ":", t, e]) =
  Let <$> parseIdent x <*> parseExpr t <*> parseExpr e
parseStmt s = parseError (InvalidStmt s)

parseParams :: (Sexpr -> Parse a) -> Sexpr -> Parse (Params a)
parseParams tP (List l) = Params <$> traverse (parseParam tP) l
parseParams _ s = parseError (InvalidParams s)

parseParam :: (Sexpr -> Parse a) -> Sexpr -> Parse (Symbol, a)
parseParam tP (List [x, t]) = (\x' t' -> (x', t')) <$> parseIdent x <*> tP t
parseParam _ s = parseError (InvalidParam s)

parseMetaType :: Sexpr -> Parse MetaType
parseMetaType (List [List args, codom]) = MetaType <$> parseParams parseExpr (List args) <*> parseExpr codom
parseMetaType s = MetaType (Params []) <$> parseExpr s

parseExpr :: Sexpr -> Parse Expr
parseExpr (Atom x) = pure (Var (Symbol x))
parseExpr (List [e, Atom ":", t]) = Ann <$> parseExpr e <*> parseExpr t
parseExpr (List (x : args)) = App <$> parseIdent x <*> traverse parseBinding args
parseExpr s = parseError (InvalidExpr s)

parseBinding :: Sexpr -> Parse Binding
parseBinding (List [List params, body]) = Binding <$> traverse parseIdent params <*> parseExpr body
parseBinding s = BindingExpr <$> parseExpr s

parseIdent :: Sexpr -> Parse Symbol
parseIdent (Atom x) = pure (Symbol x)
parseIdent s = parseError (InvalidIdent s)
