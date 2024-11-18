module Main where

import Expr qualified as E
import Symbol
import Syntax
import System.IO

main :: IO ()
main = do
  input <- hGetContents' stdin
  case parseTheory input >>= E.checkTheory of
    Left err -> putStrLn ("Error: " ++ err)
    Right _ -> putStrLn "Theory Good"

theory :: Theory
theory =
  Theory [
      Sort (Symbol "Nat") (SortType (Params []))
    , Cons (Symbol "Z") (ConsType (Params []) (Params []) (Var (Symbol "Nat")))
    , Cons (Symbol "S") (ConsType (Params []) (Params [(Symbol "n", (MetaType (Params []) (Var (Symbol "Nat"))))]) (Var (Symbol "Nat")))
    , Let (Symbol "two") (Var (Symbol "Nat")) (App (Symbol "S") [BindingExpr (App (Symbol "S") [BindingExpr (Var (Symbol "Z"))])])
    , Let (Symbol "four") (Var (Symbol "Nat")) (App (Symbol "S") [BindingExpr (App (Symbol "S") [BindingExpr (Var (Symbol "two"))])])
  ]
