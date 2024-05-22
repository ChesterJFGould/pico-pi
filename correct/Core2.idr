module Core2

import Thinning
import Data.DPair

public export
Name : Type
Name = String

public export
Scope : Type
Scope = List Name

mutual
  public export
  data Synth : (0 Σ : Scope) -> Type where
    SElim : {0 Σ : Scope} -> Elim Σ -> Synth Σ
    SCons : {0 Σ : Scope} -> Cons Σ -> Check Σ -> Synth Σ

  public export
  data Check : (0 Σ : Scope) -> Type where
    CCons : {0 Σ : Scope} -> Cons Σ -> Check Σ
    CElim : {0 Σ : Scope} -> Elim Σ -> Check Σ

  public export
  data Elim : (0 Σ : Scope) -> Type where
    Var : {0 Σ : Scope} -> Thinning Σ [x] -> Elim Σ
    App : {0 Σ : Scope} -> Synth Σ -> Check Σ -> Elim Σ

  public export
  data Cons : (0 Σ : Scope) -> Type where
    Typ : {0 Σ : Scope} -> Nat -> Cons Σ
    Lam : {0 Σ : Scope} -> (x : Name) -> Check (x :: Σ) -> Cons Σ
    Pi : {0 Σ : Scope} -> Check Σ -> Check Σ -> Cons Σ

export
Cast (Check s) (Check s -> Synth s) where
  cast (CCons e) t = SCons e t
  cast (CElim e) _ = SElim e

mutual
  public export
  data SynthNF : {0 Σ : Scope} -> Synth Σ -> Type where
    SElimNF : ElimNF e -> SynthNF (SElim e)
    SConsNF : ConsNF e -> CheckNF t -> SynthNF (SCons e t)

  public export
  data CheckNF : {0 Σ : Scope} -> Check Σ -> Type where
    CConsNF : ConsNF e -> CheckNF (CCons e)
    CElimNF : ElimNF e -> CheckNF (CElim e)

  public export
  data ElimNF : {0 Σ : Scope} -> Elim Σ -> Type where
    VarNF : ElimNF (Var x)
    AppNF : ElimNF f -> CheckNF a -> ElimNF (App (SElim f) a)

  public export
  data ConsNF : {0 Σ : Scope} -> Cons Σ -> Type where
    TypNF : ConsNF (Typ l)
    LamNF : CheckNF b -> ConsNF (Lam x b)
    PiNF : CheckNF d -> CheckNF c -> ConsNF (Pi d c)

public export
interface Weaken (0 scoped : (0 Σ : Scope) -> Type) where
  weaken : {0 Σ, Σ' : Scope} -> Thinning Σ' Σ -> scoped Σ -> scoped Σ'

export
Weaken Check where
  weaken = ?wc

mutual
  public export
  data Ctxt : Scope -> Type where
    Lin : Ctxt []
    (:<) : {0 Σ : Scope} -> {0 x : Name} -> (Γ : Ctxt Σ) -> (t : Check Σ ** (CheckNF t, CheckType Γ t)) -> Ctxt (x :: Σ)

  public export
  data CtxtSel : {0 Σ, Σ' : Scope} -> Thinning Σ [x] -> Ctxt Σ -> Thinning Σ Σ' -> (t : Check Σ') -> Type where
    This : {0 Σ : Scope} -> {0 Γ : Ctxt Σ} -> {0 thin : Thinning Σ []} -> {0 t : Check Σ} -> {0 nft : (CheckNF t, CheckType Γ t)} ->
           CtxtSel (Keep thin) (Γ :< (t ** nft)) (Disc (keepAll _)) t
    Next : {0 Σ, Σ' : Scope} -> {0 Γ : Ctxt Σ} ->
           {0 thin : Thinning Σ [x]} -> {0 thin' : Thinning Σ Σ'} ->
           {0 t : Check Σ'} -> {0 t' : (t : Check Σ ** (CheckNF t, CheckType Γ t))} ->
           CtxtSel thin Γ thin' t -> CtxtSel (Disc thin) (Γ :< t') (Disc thin') t

  public export
  data CheckType : {0 Σ : Scope} -> Ctxt Σ -> Check Σ -> Type where
    CConsType : {0 Σ : Scope} -> {0 Γ : Ctxt Σ} -> {0 t : Cons Σ} ->
                ConsType Γ t -> CheckType Γ (CCons t)
    CElimType : {0 Σ : Scope} -> {0 Γ : Ctxt Σ} -> {0 t : Elim Σ} ->
                ElimTyped Γ t (CCons (Typ l)) -> CheckType Γ (CElim t)

  public export
  data ConsType : {0 Σ : Scope} -> Ctxt Σ -> Cons Σ -> Type where
    TypType : {0 Σ : Scope} -> {0 Γ : Ctxt Σ} ->
              ConsType Γ (Typ l)
    PiType : {0 Σ : Scope} -> {0 Γ : Ctxt Σ} -> {0 d, c : Check Σ} ->
             CheckType Γ d -> CheckTypeFamily Γ c d -> ConsType Γ (Pi d c)

  public export
  data CheckTypeFamily : {0 Σ : Scope} -> Ctxt Σ -> Check Σ -> Check Σ -> Type where
    CConsTypeFamily : {0 Σ : Scope} -> {0 Γ : Ctxt Σ} -> {0 t : Cons Σ} -> {0 i : Check Σ} ->
                      ConsTypeFamily Γ t i -> CheckTypeFamily Γ (CCons t) i
    CElimTypeFamily : {0 Σ : Scope} -> {0 Γ : Ctxt Σ} -> {0 t : Elim Σ} -> {0 i : Check Σ} ->
                      ElimTyped Γ t (CCons (Pi i (CCons (Typ l)))) -> CheckTypeFamily Γ (CElim t) i

  public export
  data ConsTypeFamily : {0 Σ : Scope} -> Ctxt Σ -> Cons Σ -> Check Σ -> Type where
    LamTypeFamily : {0 Σ : Scope} -> {0 Γ : Ctxt Σ} -> {0 i : Check Σ} -> {0 b : Check (x :: Σ)} ->
                    {iNF : CheckNF i} -> {iT : CheckType Γ i} ->
                    CheckType (Γ :< (i ** (iNF, iT))) b -> ConsTypeFamily Γ (Lam x b) i

  public export
  data SynthTyped : {0 Σ : Scope} -> Ctxt Σ -> Synth Σ -> Check Σ -> Type where
    SElimTyped : {0 Σ : Scope} -> {0 Γ : Ctxt Σ} -> {0 e : Elim Σ} -> {0 t : Check Σ} ->
                 ElimTyped Γ e t -> SynthTyped Γ (SElim e) t
    SConsTyped : {0 Σ : Scope} -> {0 Γ : Ctxt Σ} -> {0 e : Cons Σ} -> {0 t : Check Σ} ->
                 ConsTyped Γ e t -> SynthTyped Γ (SCons e t) t

  public export
  data CheckTyped : {0 Σ : Scope} -> Ctxt Σ -> Check Σ -> Check Σ -> Type where
    CConsTyped : {0 Σ : Scope} -> {0 Γ : Ctxt Σ} ->
                 {0 e : Cons Σ} -> {0 t : Check Σ} ->
                 ConsTyped Γ e t -> CheckTyped Γ (CCons e) t
    CElimTyped : {0 Σ : Scope} -> {0 Γ : Ctxt Σ} ->
                 {0 e : Elim Σ} -> {0 t : Check Σ} ->
                 ElimTyped Γ e t -> CheckTyped Γ (CElim e) t

  public export
  data ElimTyped : {0 Σ : Scope} -> Ctxt Σ -> Elim Σ -> Check Σ -> Type where
    VarTyped : {0 Σ, Σ' : Scope} -> {0 Γ : Ctxt Σ} -> {0 x : Thinning Σ [name]} ->
               {0 thin : Thinning Σ Σ'} -> {0 t : Check Σ'} ->
               CtxtSel x Γ thin t -> ElimTyped Γ (Var x) (weaken thin t)
    AppTyped : {0 Σ : Scope} -> {0 Γ : Ctxt Σ} ->
               {0 f : Synth Σ} -> {0 a, d, c : Check Σ} ->
               SynthTyped Γ f (CCons (Pi d c)) -> CheckTyped Γ a d ->
               ElimTyped Γ (App f a) (CElim (App (cast c (CCons (Pi d (CCons (Typ l))))) a))

  public export
  data ConsTyped : {0 Σ : Scope} -> Ctxt Σ -> Cons Σ -> Check Σ -> Type where
    TypTyped : {0 Σ : Scope} -> {0 Γ : Ctxt Σ} ->
               ConsTyped Γ (Typ l) (CCons (Typ (S l)))
    LamTyped : {0 Σ : Scope} -> {0 Γ : Ctxt Σ} ->
               {0 b : Check (x :: Σ)} -> {0 d, c : Check Σ} ->
               {0 dNF : CheckNF d} -> {0 dT : CheckType Γ d} ->
               CheckTyped (Γ :< (d ** (dNF, dT))) b (weaken (Disc (keepAll _)) c) ->
               ConsTyped Γ (Lam x b) (CCons (Pi d c))
    PiTyped : {0 Σ : Scope} -> {0 Γ : Ctxt Σ} ->
              {0 d : Check Σ} -> {0 c : Check Σ} ->
              CheckTyped Γ d (CCons (Typ l)) -> CheckTyped Γ c (CCons (Pi d (CCons (Typ l)))) ->
              ConsTyped Γ (Pi d c) (CCons (Typ l))

Sub : Scope -> Scope -> Type
Sub from to = IList (\_ => Synth to) from

interface Substitute (0 scoped : (0 Σ : Scope) -> Type) where
  sub : {0 Σ, Σ' : Scope} -> Sub Σ Σ' -> scoped Σ -> scoped Σ'

Substitute Check where
  sub = ?sc

mutual
  -- SynthEq a b t meaning a is the same t as b
  data SynthEq : {0 Σ : Scope} -> Synth Σ -> Synth Σ -> Check Σ -> Type where
    SElimEq : {0 Σ : Scope} -> ElimEq a b t -> SynthEq (SElim a) (SElim b) t
    SConsEq : {0 Σ : Scope} -> ConsEq a b t -> SynthEq (SCons a t) (SCons b t) t

  data CheckEq : {0 Σ : Scope} -> Check Σ -> Check Σ -> Check Σ -> Type where
    CConsEq : {0 Σ : Scope} -> ConsEq a b t -> CheckEq (CCons a) (CCons b) t
    CElimEq : {0 Σ : Scope} -> ElimEq a b t -> CheckEq (CElim a) (CElim b) t
    CBetaEq : {0 Σ : Scope} ->
              {0 b : Check (x :: Σ)} -> {0 a, c, d : Check Σ} ->
              CheckEq
                (CElim (App (SCons (Lam x b) (CCons (Pi d c))) a))
                (sub ?s b)
                (CElim (App (cast c (CCons (Pi d (CCons (Typ l))))) a))

  data ElimEq : {0 Σ : Scope} -> Elim Σ -> Elim Σ -> Check Σ -> Type where
    VarEq : {0 Σ : Scope} -> ElimEq (Var x) (Var x) t
    AppEq : {0 Σ : Scope} ->
            {0 d, c, a, a' : Check Σ} -> {0 f, f' : Synth Σ} ->
            SynthEq f f' (CCons (Pi d c)) -> CheckEq a a' d ->
            ElimEq (App f a) (App f' a') (CElim (App (cast c (CCons (Pi d (CCons (Typ l))))) a))

  data ConsEq : {0 Σ : Scope} -> Cons Σ -> Cons Σ -> Check Σ -> Type where

  data CheckTypeEq : {0 Σ : Scope} -> Check Σ -> Check Σ -> Type where

  data ConsTypeEq : {0 Σ : Scope} -> Check Σ -> Check Σ -> Type where

  -- CheckTypeFamilyEq a b i meaning a is the same type family indexed by i as b
  data CheckTypeFamilyEq : {0 Σ : Scope} -> Check Σ -> Check Σ -> Check Σ -> Type where

  data ConsTypeFamilyEq : {0 Σ : Scope} -> Cons Σ -> Cons Σ -> Check Σ -> Type where

decTypeCheckEq : {0 Σ : Scope} -> {0 Γ : Ctxt Σ} -> (t : Check Σ) -> (t' : Check Σ) -> {0 tT : CheckType Γ t} -> {0 tT' : CheckType Γ t'} -> Dec (CheckTypeEq t t')
