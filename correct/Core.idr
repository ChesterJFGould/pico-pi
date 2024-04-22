module Core

data Thinning : List a -> List a -> Type where
  Empty : Thinning Nil Nil
  Keep : Thinning as bs -> Thinning (a :: as) (a :: bs)
  Disc : Thinning as bs -> Thinning (a :: as) bs

keepAll : (l : List a) -> Thinning l l
keepAll [] = Empty
keepAll (a :: as) = Keep (keepAll as)

discAll : (l : List a) -> Thinning l []
discAll [] = Empty
discAll (a :: as) = Disc (discAll as)

thinComp : Thinning b c -> Thinning a b -> Thinning a c
thinComp Empty ab = ab
thinComp (Keep bc) (Keep ab) = Keep (thinComp bc ab)
thinComp (Keep bc) (Disc ab) = Disc (thinComp (Keep bc) ab)
thinComp (Disc bc) (Keep ab) = Disc (thinComp bc ab)
thinComp (Disc bc) (Disc ab) = Disc (thinComp (Disc bc) ab)

thinningEq : Thinning a b -> Thinning a c -> Bool
thinningEq Empty Empty = True
thinningEq (Keep a) (Keep b) = thinningEq a b
thinningEq (Disc a) (Disc b) = thinningEq a b
thinningEq _ _ = False

Name : Type
Name = String

Scope : Type
Scope = List Name

mutual
  data Synth : Scope -> Type where
    Var : {0 Γ : Scope} -> Thinning Γ [x] -> Synth Γ
    App : {0 Γ : Scope} -> Synth Γ -> Check Γ -> Synth Γ
    Ann : {0 Γ : Scope} -> Check Γ -> Check Γ -> Synth Γ
  
  data Check : Scope -> Type where
    Typ : {0 Γ : Scope} -> Nat -> Check Γ
    Lam : {0 Γ : Scope} -> (x : Name) -> Check (x :: Γ) -> Check Γ
    Pi : {0 Γ : Scope} -> Check Γ -> Check Γ -> Check Γ
    Syn : {0 Γ : Scope} -> Synth Γ -> Check Γ

data IList : {a : Type} -> (a -> Type) -> List a -> Type where
  Nil : {0 f : a -> Type} -> IList f []
  Cons : {0 f : a -> Type} -> (0 x : a) -> (f x) -> IList f xs -> IList f (x :: xs)

reindexIList : {0 a : Type} -> {0 l : List a} -> {0 f : a -> Type} -> {0 g : a -> Type} ->
               ((0 x : a) -> f x -> g x) -> IList f l -> IList g l
reindexIList f Nil = Nil
reindexIList f (Cons x a as) = Cons x (f x a) (reindexIList f as)

data IThinning : {xs, ys : List a} -> IList f xs -> IList f ys -> Type where
  IEmpty : IThinning Nil Nil
  IKeep : {0 a : Type} -> {0 f : a -> Type} -> {0 y : a} -> {x : f y} ->
          {0 xis, yis : List a} -> {0 xs : IList f xis} -> {0 ys : IList f yis} ->
          IThinning xs ys -> IThinning {xs = (y :: xis)} {ys = (y :: yis)} (Cons y x xs) (Cons y x ys)
  IDisc : {0 a : Type} -> {0 f : a -> Type} -> {0 y : a} -> {x : f y} ->
          {0 xis, yis : List a} -> {0 xs : IList f xis} -> {0 ys : IList f yis} ->
          IThinning xs ys -> IThinning {xs = (y :: xis)} {ys = yis} (Cons y x xs) ys

indexThinning : (il : IList f l) -> Thinning l l' -> (il' : IList f l' ** IThinning il il')
indexThinning [] Empty = ([] ** IEmpty)
indexThinning (Cons x a as) (Keep t) =
  let (il' ** t') = indexThinning as t
  in ((Cons x a il') ** (IKeep t'))
indexThinning (Cons _ _ as) (Disc t) =
  let (il' ** t') = indexThinning as t
  in (il' ** IDisc t')

mutual
  Sub : Scope -> Scope -> Type
  Sub from to = IList (\_ => SynthNF to) from

  data SynthNF : Scope -> Type where
    SElimNF : {0 Σ : Scope} -> ElimNF Σ -> SynthNF Σ
    SConsNF : {0 Σ : Scope} -> ConsNF Σ -> CheckNF Σ -> SynthNF Σ

  data CheckNF : Scope -> Type where
    CConsNF : {0 Σ : Scope} -> ConsNF Σ -> CheckNF Σ
    CElimNF : {0 Σ : Scope} -> ElimNF Σ -> CheckNF Σ

  data ElimNF : Scope -> Type where
    VarNF : {0 Γ : Scope} -> Thinning Γ [x] -> ElimNF Γ
    AppNF : {0 Γ : Scope} -> ElimNF Γ -> CheckNF Γ -> ElimNF Γ

  data ConsNF : Scope -> Type where
    TypNF : {0 Γ : Scope} -> Nat -> ConsNF Γ
    LamNF : {0 Γ, Γ' : Scope} -> (x : Name) -> Check (x :: Γ') -> Sub Γ' Γ -> ConsNF Γ
    PiNF : {0 Γ : Scope} -> CheckNF Γ -> CheckNF Γ -> ConsNF Γ

mutual
  weakenSub : {0 Σ, Σ', Σ'' : Scope} -> Sub Σ Σ' -> Thinning Σ'' Σ' -> Sub Σ Σ''
  weakenSub s t = reindexIList (\_, e => weakenSynNF t e) s

  weakenSynNF : {0 Σ, Σ' : Scope} -> Thinning Σ' Σ -> SynthNF Σ -> SynthNF Σ'
  weakenSynNF t (SElimNF e) = SElimNF (weakenElimNF t e)
  weakenSynNF t (SConsNF e e_t) = SConsNF (weakenConsNF t e) (weakenChkNF t e_t)

  weakenChkNF : {0 Σ, Σ' : Scope} -> Thinning Σ' Σ -> CheckNF Σ -> CheckNF Σ'
  weakenChkNF t (CConsNF e) = CConsNF (weakenConsNF t e)
  weakenChkNF t (CElimNF e) = CElimNF (weakenElimNF t e)

  weakenConsNF : {0 Σ, Σ' : Scope} -> Thinning Σ' Σ -> ConsNF Σ -> ConsNF Σ'
  weakenConsNF t (TypNF l) = TypNF l
  weakenConsNF t (LamNF x b sub) = LamNF x b (weakenSub sub t)
  weakenConsNF t (PiNF d c) = PiNF (weakenChkNF t d) (weakenChkNF t c)

  weakenElimNF : {0 Σ, Σ' : Scope} -> Thinning Σ' Σ -> ElimNF Σ -> ElimNF Σ'
  weakenElimNF t (VarNF x) = VarNF (thinComp x t)
  weakenElimNF t (AppNF f a) = AppNF (weakenElimNF t f) (weakenChkNF t a)

keepSub : (Σ : Scope) -> Sub Σ Σ
keepSub [] = Nil
keepSub (x :: xs) = Cons x (SElimNF (VarNF (Keep (discAll (xs))))) (weakenSub (keepSub xs) (Disc (keepAll _)))

checkSynth : {0 Σ : Scope} -> CheckNF Σ -> CheckNF Σ -> SynthNF Σ
checkSynth (CConsNF e) t = SConsNF e t
checkSynth (CElimNF e) _ = SElimNF e

synthCheck : {0 Σ : Scope} -> SynthNF Σ -> CheckNF Σ
synthCheck (SElimNF e) = CElimNF e
synthCheck (SConsNF e _) = CConsNF e

mutual
  synthNF : {0 Σ, Σ' : Scope} -> (Sub Σ Σ') -> Synth Σ -> SynthNF Σ'
  synthNF sub (Var x) =
    let ((Cons _ e _) ** _) = indexThinning sub x
    in e
  synthNF sub (App f a) = appNF (synthNF sub f) (checkNF sub a)
  synthNF sub (Ann e t) = annNF (checkNF sub e) (checkNF sub t)

  appNF : {0 Σ : Scope} -> SynthNF Σ -> CheckNF Σ -> SynthNF Σ
  appNF (SConsNF (LamNF x b sub) (CConsNF (PiNF d c))) a =
    checkSynth (checkNF (Cons x (checkSynth a d) sub) b) (appTypeFamilyNF c (checkSynth a d))
  appNF (SElimNF f) a = SElimNF (AppNF f a)
  -- TODO: We should never reach this case, either prove it or handle the error
  appNF f _ = f

  appTypeFamilyNF : {0 Σ : Scope} -> CheckNF Σ -> SynthNF Σ -> CheckNF Σ
  appTypeFamilyNF (CConsNF (LamNF x b sub)) a = checkNF (Cons x a sub) b
  appTypeFamilyNF (CElimNF f) a = CElimNF (AppNF f (synthCheck a))
  -- TODO: Same as appNF
  appTypeFamilyNF f _ = f

  annNF : {0 Σ : Scope} -> CheckNF Σ -> CheckNF Σ -> SynthNF Σ
  annNF (CConsNF e) t = SConsNF e t
  annNF (CElimNF e) _ = SElimNF e

  checkNF : {0 Σ, Σ' : Scope} -> Sub Σ Σ' -> Check Σ -> CheckNF Σ'
  checkNF sub (Typ l) = CConsNF (TypNF l)
  checkNF sub (Lam x e) = CConsNF (LamNF x e sub)
  checkNF sub (Pi d c) = CConsNF (PiNF (checkNF sub d) (checkNF sub c))
  checkNF sub (Syn e) = synthCheck (synthNF sub e)

data Ctxt : Scope -> Type where
  EmptyCtxt : Ctxt []
  VarCtxt : {0 Σ : Scope} -> {0 x : Name} -> CheckNF Σ -> Ctxt Σ -> Ctxt (x :: Σ)

keepAllCtxt : {0 Σ : Scope} -> Ctxt Σ -> Thinning Σ Σ
keepAllCtxt EmptyCtxt = Empty
keepAllCtxt (VarCtxt _ ctxt) = Keep (keepAllCtxt ctxt)

discAllCtxt : {0 Σ : Scope} -> Ctxt Σ -> Thinning Σ []
discAllCtxt EmptyCtxt = Empty
discAllCtxt (VarCtxt _ ctxt) = Disc (discAllCtxt ctxt)

ctxtLookup : {0 Σ : Scope} -> Ctxt Σ -> Thinning Σ [x] -> CheckNF Σ
ctxtLookup EmptyCtxt _ impossible
ctxtLookup (VarCtxt t ctxt) (Keep _) = weakenChkNF (Disc (keepAllCtxt ctxt)) t
ctxtLookup (VarCtxt _ ctxt) (Disc x) = weakenChkNF (Disc (keepAllCtxt ctxt)) (ctxtLookup ctxt x)

partial
elimType : {0 Σ : Scope} -> {auto Γ : Ctxt Σ} -> ElimNF Σ -> CheckNF Σ
elimType (VarNF x) = ctxtLookup Γ x
elimType (AppNF f a) =
  case elimType f of
    CConsNF (PiNF d c) => appTypeFamilyNF c (checkSynth a d)

partial
synthType : {0 Σ : Scope} -> {auto _ : Ctxt Σ} -> SynthNF Σ -> CheckNF Σ
synthType (SElimNF e) = elimType e
synthType (SConsNF _ t) = t

irrelevant : {0 Σ : Scope} -> CheckNF Σ -> Bool

mutual
  partial
  synNFEq : {0 Σ : Scope} -> Ctxt Σ => SynthNF Σ -> SynthNF Σ -> Bool
  synNFEq (SElimNF a) (SElimNF b) = elimNFEq a b || irrelevant (elimType a)
  synNFEq (SConsNF a t) (SConsNF b _) = consNFEq a b t
  synNFEq _ _ = False

  partial
  chkNFEq : {0 Σ : Scope} -> {auto Γ : Ctxt Σ} -> CheckNF Σ -> CheckNF Σ -> CheckNF Σ -> Bool
  chkNFEq (CConsNF a) (CConsNF b) t = consNFEq a b t
  chkNFEq (CElimNF a) (CElimNF b) _ = elimNFEq a b || irrelevant (elimType a)
  chkNFEq _ _ _ = False

  partial
  elimNFEq : {0 Σ : Scope} -> Ctxt Σ => ElimNF Σ -> ElimNF Σ -> Bool
  elimNFEq (VarNF a) (VarNF b) = thinningEq a b
  elimNFEq (AppNF f_a a_a) (AppNF f_b a_b) =
    elimNFEq f_a f_b &&
    (let (CConsNF (PiNF d _)) = elimType f_a
     in chkNFEq a_a a_b d)
  elimNFEq _ _ = False

  partial
  consNFEq : {0 Σ : Scope} -> {auto Γ : Ctxt Σ} -> ConsNF Σ -> ConsNF Σ -> CheckNF Σ -> Bool
  consNFEq (TypNF a) (TypNF b) (CConsNF (TypNF _)) = a == b
  consNFEq (LamNF x_a a sub_a) (LamNF x_b b sub_b) (CConsNF (PiNF d c)) =
    let ctxt' : Ctxt (x_a :: Σ)
        ctxt' = VarCtxt d Γ
    in
      chkNFEq {Σ = (x_a :: Σ)} {Γ = ctxt'}
        (checkNF (Cons x_a (SElimNF (VarNF (Keep (discAllCtxt _)))) ?as) a)
        (checkNF (Cons x_b (SElimNF (VarNF (Keep (discAllCtxt _)))) ?bs) b)
        ?t
  consNFEq _ _ _ = ?cn
