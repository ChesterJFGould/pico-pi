module Sexpr

import Ewe

import Data.List

public export
data Sexpr = Atom String | List (List Sexpr)

mutual
  showSexpr : Sexpr -> String
  showSexpr (Atom s) = s
  showSexpr (List l) = "(" ++ concat (intersperse " " (showSexprs l)) ++ ")"

  showSexprs : List Sexpr -> List String
  showSexprs [] = []
  showSexprs (hd :: tl) = showSexpr hd :: showSexprs tl

export
Show Sexpr where
  show = showSexpr

isAtomChar : Char -> Bool
isAtomChar c = not (isSpace c) && c /= '(' && c /= ')'

atomP : Parser String Char Sexpr
atomP = ann "S-Expression Atom" ((Atom . pack) <$> some (is isAtomChar))

mutual
  export
  sexprP : Parser String Char Sexpr
  sexprP = atomP <|> listP

  listP : Parser String Char Sexpr
  listP = ann "S-Expression List" (List <$> (char '(' *> many (whitespace *> sexprP) <* whitespace <* char ')'))
