module SyntaxNbE

import Data.String

data Exp : Type where
  Var : String -> Exp
  Lam : String -> Exp -> Exp
  App : Exp -> Exp -> Exp

mutual
  data Env : Type where
    Lin : Env
    (:<) : Env -> (String, Val) -> Env

  data Nf : Type where
    LamN : String -> Exp -> Env -> Nf

  data Ne : Type where
    VarN : String -> Ne
    AppN : Ne -> Val -> Ne
  
  data Val : Type where
    NfV : Nf -> Val
    NeV : Ne -> Val

{- I want to decide the following equations:
 - App (Lam x b) a = b[a/x]
 -}

partial
lookupEnv : String -> Env -> Val
lookupEnv x (env :< (x', v)) with (x == x')
  _ | True = v
  _ | False = lookupEnv x env

inList : Eq a => a -> List a -> Bool
inList _ [] = False
inList x (x' :: xs) with (x == x')
  _ | True = True
  _ | False = inList x xs

gensym : String -> List String -> String
gensym x l with (inList x l)
  _ | True = gensym (x ++ "'") l
  _ | False = x

partial
eval : Exp -> Env -> Val
eval (Var x) env = lookupEnv x env
eval (Lam x b) env = NfV (LamN x b env)
eval (App f a) env with (eval f env)
  _ | NfV (LamN x b env') = eval b (env :< (x, (eval a env)))
  _ | NeV n = NeV (AppN n (eval a env))

mutual
  partial
  quoteNf : Nf -> List String -> Exp
  quoteNf (LamN x b env) s with (gensym x s)
    _ | x' = Lam x' (quote (eval b (env :< (x, NeV (VarN x')))) (x' :: s))

  partial
  quoteNe : Ne -> List String -> Exp
  quoteNe (VarN x) _ = Var x
  quoteNe (AppN f a) s = App (quoteNe f s) (quote a s)

  partial
  quote : Val -> List String -> Exp
  quote (NfV nf) = quoteNf nf
  quote (NeV ne) = quoteNe ne

partial
norm : Exp -> Exp
norm e = quote (eval e Lin) []
