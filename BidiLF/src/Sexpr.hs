{-# LANGUAGE ApplicativeDo #-}

module Sexpr (
  Sexpr(Atom, List),
  sexprP,
)where

import Control.Applicative
import Data.Char
import Data.List
import Ewe

data Sexpr = Atom String | List [Sexpr]

instance Show Sexpr where
  show (Atom a) = a
  show (List l) = "(" ++ intercalate " " (map show l) ++ ")"

sexprP :: Parser Char Sexpr
sexprP = listP '(' ')' <|> listP '[' ']' <|> atomP

isAtom :: Char -> Bool
isAtom c = not (isSpace c || elem c ['(', ')', '[', ']'])

atomP :: Parser Char Sexpr
atomP = Atom <$> some (is isAtom)

listP :: Char -> Char -> Parser Char Sexpr
listP b e = do
  tok b
  whitespace
  elems <- many (whitespace *> sexprP)
  whitespace
  tok e
  pure (List elems)
