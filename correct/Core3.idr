module Core3

import Thinning

Name : Type
Name = String

Scope : Type
Scope = List Name

data Expr : Scope -> Type where
  Var : {0 Σ : Scope} -> Thinning Σ [x] -> Expr Σ
  Typ : {0 Σ : Scope} -> Nat -> Expr Σ
  Lam : {0 Σ : Scope} -> (x : Name) -> Expr (x :: Σ) -> Expr Σ
  App : {0 Σ : Scope} -> Expr Σ -> Expr Σ -> Expr Σ
  Pi : {0 Σ : Scope} -> Expr Σ -> Expr Σ -> Expr Σ
  Ann : {0 Σ : Scope} -> Expr Σ -> Expr Σ -> Expr Σ

data Ctxt : Scope -> Type where
  Lin : Ctxt []
  (:<) : {0 Σ : Scope} -> Ctxt Σ -> Expr Σ -> Ctxt (x :: Σ)

data CtxtSel : {0 Σ, Σ' : Scope} -> Ctxt Σ -> Thinning Σ [x] -> Expr Σ -> Type where

interface Weaken (0 scoped : Scope -> Type) where
  weaken : {0 Σ, Σ' : Scope} -> Thinning Σ' Σ -> scoped Σ -> scoped Σ'

Weaken Expr where
  weaken = ?we

mutual
  data Check : {0 Σ : Scope} -> Ctxt Σ -> Expr Σ -> Expr Σ -> Type where
    TypCheck : {0 Σ : Scope} -> {0 Γ : Ctxt Σ} ->
               Check Γ (Typ l) (Typ (S l))
    LamCheck : {0 Σ : Scope} -> {0 Γ : Ctxt Σ} -> {0 b : Expr (x :: Σ)} -> {0 d, c : Expr Σ} ->
               Check (Γ :< d) b (App (weaken (Disc (keepAll _)) c) (Var (Keep (discAll _)))) ->
               Check Γ (Lam x b) (Pi d c)
    PiCheck : {0 Σ : Scope} -> {0 Γ : Ctxt Σ} -> {0 d, c : Expr Σ} ->
              Check Γ d (Typ l) -> Check Γ c (Pi d (Lam "_" (Typ l))) ->
              Check Γ (Pi d c) (Typ l)
    SynthCheck : {0 Σ : Scope} -> {0 Γ : Ctxt Σ} -> {0 e, t, t' : Expr Σ} ->
                 Synth Γ e t' -> TypeEq Γ t t' ->
                 Check Γ e t

  data Synth : {0 Σ : Scope} -> Ctxt Σ -> Expr Σ -> Expr Σ -> Type where
    VarSynth : {0 Σ : Scope} -> {0 Γ : Ctxt Σ} -> {0 x : Thinning Σ [n]} -> {0 t : Expr Σ} ->
               CtxtSel Γ x t ->
               Synth Γ (Var x) t
    AppSynth : {0 Σ : Scope} -> {0 Γ : Ctxt Σ} -> {0 f, a, d, c : Expr Σ} ->
               Synth Γ f (Pi d c) -> Check Γ a d ->
               Synth Γ (App f a) (App c a)
    AnnSynth : {0 Σ : Scope} -> {0 Γ : Ctxt Σ} -> {0 e, t : Expr Σ} ->
               IsType Γ t -> Check Γ e t ->
               Synth Γ (Ann e t) t

  data IsType : {0 Σ : Scope} -> Ctxt Σ -> Expr Σ -> Type where
    TypIsType : {0 Σ : Scope} -> {0 Γ : Ctxt Σ} ->
                IsType Γ (Typ l)
    AppIsType : {0 Σ : Scope} -> {0 Γ : Ctxt Σ} -> {0 a, i, tf : Expr Σ} ->
                Synth Γ a i -> IsTypeFamily Γ tf i ->
                IsType Γ (App tf a)
    PiIsType : {0 Σ : Scope} -> {0 Γ : Ctxt Σ} -> {0 d, c : Expr Σ} ->
               IsType Γ d -> IsTypeFamily Γ c d ->
               IsType Γ (Pi d c)
    SynthIsType : {0 Σ : Scope} -> {0 Γ : Ctxt Σ} -> {0 t : Expr Σ} ->
                  Synth Γ t (Typ l) ->
                  IsType Γ t

  data IsTypeFamily : {0 Σ : Scope} -> Ctxt Σ -> Expr Σ -> Expr Σ -> Type where
    LamIsTypeFamily : {0 Σ : Scope} -> {0 Γ : Ctxt Σ} -> {0 b : Expr (x :: Σ)} -> {0 i : Expr Σ} ->
                      IsType (Γ :< i) b ->
                      IsTypeFamily Γ (Lam x b) i
    SynthIsTypeFamily : {0 Σ : Scope} -> {0 Γ : Ctxt Σ} -> {0 tf, i : Expr Σ} ->
                        Synth Γ tf (Pi i (Lam "_" (Typ l))) ->
                        IsTypeFamily Γ tf i

  data ExprEq : {0 Σ : Scope} -> Ctxt Σ -> Expr Σ -> Expr Σ -> Expr Σ -> Type where
    VarEq : {0 Σ : Scope} -> {0 Γ : Ctxt Σ} -> {0 x : Thinning Σ [n]} -> {0 t : Expr Σ} ->
            CtxtSel Γ x t ->
            ExprEq Γ (Var x) (Var x) t
    TypEq : {0 Σ : Scope} -> {0 Γ : Ctxt Σ} ->
            ExprEq Γ (Typ l) (Typ l) (Typ (S l))
    LamEq : {0 Σ : Scope} -> {0 Γ : Ctxt Σ} -> {0 b, b' : Expr (x :: Σ)} -> {0 d, c : Expr Σ} ->
            ExprEq (Γ :< d) b b' (App (weaken (Disc (keepAll _)) c) (Var (Keep (discAll _)))) ->
            ExprEq Γ (Lam x b) (Lam x b') (Pi d c)
    AppEq : {0 Σ : Scope} -> {0 Γ : Ctxt Σ} -> {0 a, a', f, f', d, c : Expr Σ} ->
            ExprEq Γ f f' (Pi d c) -> ExprEq Γ a a' d ->
            ExprEq Γ (App f a) (App f' a') (App c a)
    PiEq : {0 Σ : Scope} -> {0 Γ : Ctxt Σ} -> {0 d, d', c, c' : Expr Σ} ->
           ExprEq Γ d d' (Typ l) -> ExprEq Γ c c' (Pi d (Lam "_" (Typ l))) ->
           ExprEq Γ (Pi d c) (Pi d' c') (Typ l)
    AnnEq : {0 Σ : Scope} -> {0 Γ : Ctxt Σ} -> {0 e, e', t : Expr Σ} ->
            ExprEq Γ e e' t ->
            ExprEq Γ (Ann e t) e' t

  data TypeEq : {0 Σ : Scope} -> Ctxt Σ -> Expr Σ -> Expr Σ -> Type where

mutual
  check : {0 Σ : Scope} -> {Γ : Ctxt Σ} -> (e : Expr Σ) -> (t : Expr Σ) -> (0 tT : IsType Γ t) -> Dec (Check Γ e t)

  synth : {0 Σ : Scope} -> {Γ : Ctxt Σ} -> (e : Expr Σ) -> (t : Expr Σ) -> Dec (t : Expr Σ ** Synth Γ e t)
