module Repl

import Ast
import Core
import Ewe
import Sexpr
import TypeCheck

import System.REPL

TC (Either TypeError) where
  pure_tc = pure
  bind_tc = (>>=)
  throw = Left

partial
typeRepl : String -> String
typeRepl s =
  either id id
    (do
     s' <- runParser "expr" s sexprP
     e <- mapFst show (parseAst s')
     (e', _) <- mapFst showTypeError (synth {env = emptyEnv} e)
     pure (showSynthNF (synthNF {Σ = []} {Σ' = []} Nil e'))) ++ "\n"

{- Variable Capture Example:
 - ((λ x (((λ y (λ x y)) : (-> (Type 0) (λ _ (-> (Type 0) (λ _ (Type 0)))))) x)) : (-> (Type 0) (λ _ (-> (Type 0) (λ _ (Type 0))))))
 -}

partial
main : IO ()
main = repl "λ> " typeRepl
