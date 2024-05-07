module Ast

import Ewe
import Sexpr

import Data.String

public export
data Ast =
    Var String
  | App Ast Ast
  | Ann Ast Ast
  | Typ Nat
  | Lam String Ast
  | Pi Ast Ast

export
data ParseError =
    InvalidVariable String
  | InvalidLevel String
  | InvalidExpr Sexpr

export
Show ParseError where
  show (InvalidVariable x) = "Invalid Variable: `" ++ x ++ "`"
  show (InvalidLevel l) = "Invalid Level: `" ++ l ++ "`"
  show (InvalidExpr s) = "Invalid Expression: `" ++ show s ++ "`"

total
isVar : String -> Bool
isVar s = (s /= "λ") && (s /= "->") && (s /= ":")

mutual
  export total
  parseAst : Sexpr -> Either ParseError Ast
  parseAst (Atom x) with (isVar x)
    _ | True = pure (Var x)
    _ | False = Left (InvalidVariable x)
  parseAst (List [Atom "Type", Atom n]) with (the (Maybe Nat) (parsePositive n))
    _ | Nothing = Left (InvalidLevel n)
    _ | Just l = pure (Typ l)
  parseAst (List [Atom "λ", Atom x, b]) with (isVar x)
    _ | True = Lam x <$> parseAst b
    _ | False = Left (InvalidVariable x)
  parseAst (List [e, Atom ":", t]) = Ann <$> parseAst e <*> parseAst t
  parseAst (List [Atom "->", d, c]) = Pi <$> parseAst d <*> parseAst c
  parseAst (List (f :: a :: as)) = parseApp !(parseAst f) (a :: as)
  parseAst e = Left (InvalidExpr e)

  total
  parseApp : Ast -> List Sexpr -> Either ParseError Ast
  parseApp f [] = pure f
  parseApp f (a :: as) = parseApp (App f !(parseAst a)) as

unparseAst : Ast -> Sexpr
unparseAst (Var x) = Atom x
unparseAst (App f a) = List [unparseAst f, unparseAst a]
unparseAst (Ann e t) = List [unparseAst e, Atom ":", unparseAst t]
unparseAst (Typ l) = List [Atom "Type", Atom (show l)]
unparseAst (Lam x b) = List [Atom "λ", Atom x, unparseAst b]
unparseAst (Pi d c) = List [Atom "->", unparseAst d, unparseAst c]

export
Show Ast where
  show = show . unparseAst
