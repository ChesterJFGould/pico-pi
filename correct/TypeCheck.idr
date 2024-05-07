module TypeCheck

import Ast
import Core

public export
record Env where
  constructor MkEnv
  Σ : Scope
  Γ : Ctxt Σ
  Δ : Sub Σ Σ

public export
emptyEnv : Env
emptyEnv = MkEnv [] EmptyCtxt Nil

export
data TypeError : Type where
  UndefinedVariable : String -> TypeError
  CheckMismatch : {env : Env} -> Ast -> CheckNF env.Σ -> TypeError
  WrongType : {env : Env} -> Ast -> CheckNF env.Σ -> CheckNF env.Σ -> TypeError
  ExpectedFunction : {env : Env} -> Ast -> CheckNF env.Σ -> TypeError
  ExpectedType : Ast -> TypeError
  ExpectedTypeButIs : {env : Env} -> Ast -> CheckNF env.Σ -> TypeError
  CannotSynth : Ast -> TypeError
  ExpectedTypeFamily : {env : Env} -> Ast -> CheckNF env.Σ -> CheckNF env.Σ -> TypeError

strConcat : List String -> String
strConcat = foldr (++) ""

export
showTypeError : TypeError -> String
showTypeError (UndefinedVariable x) = "Undefined Variable: " ++ x
showTypeError (CheckMismatch e t) = strConcat ["Expected `", show e, "` to be a `", showCheckNF t, "`"]
showTypeError (WrongType e t t') = strConcat ["Expected `", show e, "` to be a `", showCheckNF t, "` but is a `", showCheckNF t', "`"]
showTypeError (ExpectedFunction e t) = strConcat ["Expected `", show e, "` to be a function, but is a `", showCheckNF t, "`"]
showTypeError (ExpectedType e) = strConcat ["Expected `", show e, "` to be a type"]
showTypeError (ExpectedTypeButIs e t) = strConcat ["Expected `", show e, "` to be a type, but is a `", showCheckNF t, "`"]
showTypeError (CannotSynth e) = strConcat ["Cannot synthesize type for `", show e, "`"]
showTypeError (ExpectedTypeFamily e i t) = strConcat ["Expected `", show e, "` to be a type family indexed by `", showCheckNF i, "` but is a `", showCheckNF t, "`"]

public export
interface TC (0 m : Type -> Type) where
  pure_tc : a -> m a
  bind_tc : m a -> (a -> m b) -> m b
  throw : TypeError -> m a

TC m => Functor m where
  map f a = bind_tc a (pure_tc . f)

TC m => Applicative m where
  pure = pure_tc
  f <*> a = bind_tc f (\f => bind_tc a (\a => pure_tc (f a)))

TC m => Monad m where
  (>>=) = bind_tc

mutual
  partial
  check : TC tc => {auto env : Env} -> Ast -> CheckNF env.Σ -> tc (Check env.Σ)
  check (Typ l) (CConsNF (TypNF l')) with (l < l')
    _ | True = pure (Typ l)
    _ | False = throw (CheckMismatch {env} (Typ l) (CConsNF (TypNF l')))
  check (Typ l) t = throw (CheckMismatch (Typ l) t)
  check (Lam x b) (CConsNF (PiNF d c)) = do
    b' <-
      check
        {env =
          MkEnv
            (cast x :: env.Σ)
            (VarCtxt d env.Γ)
            (Cons (cast x) (SElimNF (VarNF (Keep (discAll _)))) (weakenSub env.Δ (Disc (keepAll _))))
        }
        b
        (appTypeFamilyNF (weakenChkNF (Disc (keepAll _)) c) (SElimNF (VarNF (Keep (discAll _)))))
    pure (Lam (cast x) b')
  check (Lam x b) t = throw (CheckMismatch (Lam x b) t)
  check (Pi d c) (CConsNF (TypNF l)) = do
    d' <- check d (CConsNF (TypNF l))
    let dNF = checkNF env.Δ d'
    c' <- check c (CConsNF (PiNF dNF (CConsNF (LamNF "_" (Typ l) Nil))))
    pure (Pi d' c')
  check (Pi d c) t = throw (CheckMismatch (Pi d c) t)
  check e t = do
    (e', t') <- synth e
    case typeEq env.Γ t t' of
      True => pure (Syn e')
      False => throw (WrongType e t t')
  
  export partial
  synth : TC tc => {auto env : Env} -> Ast -> tc (Synth env.Σ, CheckNF env.Σ)
  synth (Var x) with (getVar env.Σ env.Γ (cast x))
    _ | Nothing = (throw (UndefinedVariable x))
    _ | Just (x', t') = pure (Var x', t')
  synth (App f a) = do
    (f', CConsNF (PiNF d c)) <- synth f
      | (f', t) => throw (ExpectedFunction f t)
    a' <- check a d
    pure (App f' a', appTypeFamilyNF c (checkSynth (checkNF env.Δ a') d))
  synth (Ann e t) = do
    t' <- checkType t
    let tNF = checkNF env.Δ t'
    e' <- check e tNF
    pure (Ann e' t', tNF)
  synth e = throw (CannotSynth e)
  
  partial
  checkType : TC tc => (env : Env) => Ast -> tc (Check env.Σ)
  checkType (Typ l) = pure (Typ l)
  checkType (Lam x b) = throw (ExpectedType (Lam x b))
  checkType (Pi d c) = do
    d' <- checkType d
    c' <- checkTypeFamily c (checkNF env.Δ d')
    pure (Pi d' c')
  checkType e = do
    (e', CConsNF (TypNF _)) <- synth e
      | (e', t) => throw (ExpectedTypeButIs e t)
    pure (Syn e')
  
  partial
  checkTypeFamily : TC tc => (env : Env) => Ast -> CheckNF env.Σ -> tc (Check env.Σ)
  checkTypeFamily (Lam x b) i = do
    b' <-
      checkType
        {env =
          MkEnv
            (cast x :: env.Σ)
            (VarCtxt i env.Γ)
            (Cons (cast x) (SElimNF (VarNF (Keep (discAll _)))) (weakenSub env.Δ (Disc (keepAll _))))
        }
        b
    pure (Lam (cast x) b')
  checkTypeFamily e i = do
    (e', CConsNF (PiNF i' (CConsNF (TypNF l)))) <- synth e
      | (_, t) => throw (ExpectedTypeFamily e i t)
    case typeEq env.Γ i i' of
      True => pure (Syn e')
      False => throw (ExpectedTypeFamily e i (CConsNF (PiNF i' (CConsNF (TypNF l)))))
