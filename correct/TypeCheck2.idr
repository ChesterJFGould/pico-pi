module TypeCheck2

import Core2
import Decidable.Equality

record CheckNFT {0 Σ : Scope} (0 Γ : Ctxt Σ) where
  constructor MkCheckNFT
  e : Check Σ
  0 nf : CheckNF e
  0 t : CheckType Γ e

mutual
  check : {0 Σ : Scope} -> {Γ : Ctxt Σ} -> (e : Check Σ) -> (t : CheckNFT Γ) -> Dec (CheckTyped Γ e t.e)

  checkCons : {0 Σ : Scope} -> {Γ : Ctxt Σ} -> (e : Cons Σ) -> (t : CheckNFT Γ) -> Dec (ConsTyped Γ e t.e)
  checkCons (Typ l) (MkCheckNFT t _ _) with (decEq (CCons (Typ (S l))) t)
    checkCons (Typ l) (MkCheckNFT (CCons (Typ (S l))) _ _) | Yes Refl = Yes TypTyped
    _ | No bad = No (\TypTyped => bad Refl)
  checkCons _ _ = ?cc
