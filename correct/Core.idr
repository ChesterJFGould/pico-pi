module Core

import Ast

import Data.List.Elem
import Data.Singleton
import Decidable.Equality

public export
data Thinning : List a -> List a -> Type where
  Empty : Thinning Nil Nil
  Keep : Thinning as bs -> Thinning (a :: as) (a :: bs)
  Disc : Thinning as bs -> Thinning (a :: as) bs

export
keepAll : (l : List a) -> Thinning l l
keepAll [] = Empty
keepAll (a :: as) = Keep (keepAll as)

export
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

thinningGet : (l : List a) -> Thinning l [x] -> Singleton x
thinningGet (x :: _) (Keep _) = pure x
thinningGet (_ :: xs) (Disc t) = thinningGet xs t

export
Name : Type
Name = String

export
Cast String Name where
  cast = id

export
FromString Name where
  fromString = id

public export
Scope : Type
Scope = List Name

mutual
  public export
  data Synth : Scope -> Type where
    Var : {0 Γ : Scope} -> Thinning Γ [x] -> Synth Γ
    App : {0 Γ : Scope} -> Synth Γ -> Check Γ -> Synth Γ
    Ann : {0 Γ : Scope} -> Check Γ -> Check Γ -> Synth Γ
  
  public export
  data Check : Scope -> Type where
    Typ : {0 Γ : Scope} -> Nat -> Check Γ
    Lam : {0 Γ : Scope} -> (x : Name) -> Check (x :: Γ) -> Check Γ
    Pi : {0 Γ : Scope} -> Check Γ -> Check Γ -> Check Γ
    Syn : {0 Γ : Scope} -> Synth Γ -> Check Γ

public export
data IList : {a : Type} -> (a -> Type) -> List a -> Type where
  Nil : {0 f : a -> Type} -> IList f []
  Cons : {0 f : a -> Type} -> (0 x : a) -> (f x) -> IList f xs -> IList f (x :: xs)

reindexIList : {0 a : Type} -> {0 l : List a} -> {0 f : a -> Type} -> {0 g : a -> Type} ->
               ((0 x : a) -> f x -> g x) -> IList f l -> IList g l
reindexIList f Nil = Nil
reindexIList f (Cons x a as) = Cons x (f x a) (reindexIList f as)

public export
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

Renaming : Scope -> Type
Renaming s = IList (const String) s

fresh : {0 Σ : Scope} -> Renaming Σ -> String -> String
fresh Nil s = s
fresh (Cons _ s rest) s' with (decEq s s')
  _ | Yes _ = fresh rest (s ++ "'")
  _ | No _ = fresh rest s'

mutual
  astSynth : {Σ : Scope} -> Renaming Σ -> Synth Σ -> Ast
  astSynth vars (Var x) with (indexThinning vars x)
    _ | ((Cons _ x' _) ** _) = Var x'
  astSynth vars (App f a) = App (astSynth vars f) (astCheck vars a)
  astSynth vars (Ann e t) = Ann (astCheck vars e) (astCheck vars t)

  astCheck : {Σ : Scope} -> Renaming Σ -> Check Σ -> Ast
  astCheck vars (Typ l) = Typ l
  astCheck vars (Lam x b) with (fresh vars x)
    _ | x' = Lam x' (astCheck (Cons x x' vars) b)
  astCheck vars (Pi d c) = Pi (astCheck vars d) (astCheck vars c)
  astCheck vars (Syn e) = astSynth vars e

makeRenaming : (Σ : Scope) -> Renaming Σ
makeRenaming [] = Nil
makeRenaming (x :: xs) with (makeRenaming xs)
  _ | r with (fresh r x)
    _ | x' = Cons x x' r

export
showSynth : {Σ : Scope} -> Synth Σ -> String
showSynth = show . astSynth (makeRenaming Σ)

export
showCheck : {Σ : Scope} -> Check Σ -> String
showCheck = show . astCheck (makeRenaming Σ)

mutual
  public export
  Sub : Scope -> Scope -> Type
  Sub from to = IList (\_ => SynthNF to) from

  public export
  data SynthNF : Scope -> Type where
    SElimNF : {0 Σ : Scope} -> ElimNF Σ -> SynthNF Σ
    SConsNF : {0 Σ : Scope} -> ConsNF Σ -> CheckNF Σ -> SynthNF Σ

  public export
  data CheckNF : Scope -> Type where
    CConsNF : {0 Σ : Scope} -> ConsNF Σ -> CheckNF Σ
    CElimNF : {0 Σ : Scope} -> ElimNF Σ -> CheckNF Σ

  public export
  data ElimNF : Scope -> Type where
    VarNF : {0 Γ : Scope} -> Thinning Γ [x] -> ElimNF Γ
    AppNF : {0 Γ : Scope} -> ElimNF Γ -> CheckNF Γ -> ElimNF Γ

  public export
  data ConsNF : Scope -> Type where
    TypNF : {0 Γ : Scope} -> Nat -> ConsNF Γ
    LamNF : {0 Γ, Γ' : Scope} -> (x : Name) -> Check (x :: Γ') -> Sub Γ' Γ -> ConsNF Γ
    PiNF : {0 Γ : Scope} -> CheckNF Γ -> CheckNF Γ -> ConsNF Γ

mutual
  export
  weakenSub : {0 Σ, Σ', Σ'' : Scope} -> Sub Σ Σ' -> Thinning Σ'' Σ' -> Sub Σ Σ''
  weakenSub s t = reindexIList (\_, e => weakenSynNF t e) s

  weakenSynNF : {0 Σ, Σ' : Scope} -> Thinning Σ' Σ -> SynthNF Σ -> SynthNF Σ'
  weakenSynNF t (SElimNF e) = SElimNF (weakenElimNF t e)
  weakenSynNF t (SConsNF e e_t) = SConsNF (weakenConsNF t e) (weakenChkNF t e_t)

  export
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

export
keepSub : (Σ : Scope) -> Sub Σ Σ
keepSub [] = Nil
keepSub (x :: xs) = Cons x (SElimNF (VarNF (Keep (discAll (xs))))) (weakenSub (keepSub xs) (Disc (keepAll _)))

export
checkSynth : {0 Σ : Scope} -> CheckNF Σ -> CheckNF Σ -> SynthNF Σ
checkSynth (CConsNF e) t = SConsNF e t
checkSynth (CElimNF e) _ = SElimNF e

synthCheck : {0 Σ : Scope} -> SynthNF Σ -> CheckNF Σ
synthCheck (SElimNF e) = CElimNF e
synthCheck (SConsNF e _) = CConsNF e

mutual
  export
  synthNF : {0 Σ, Σ' : Scope} -> (Sub Σ Σ') -> Synth Σ -> SynthNF Σ'
  synthNF sub (Var x) =
    let ((Cons _ e _) ** _) = indexThinning sub x
    in e
  synthNF sub (App f a) = appNF (synthNF sub f) (checkNF sub a)
  synthNF sub (Ann e t) = annNF (checkNF sub e) (checkNF sub t)

  partial
  appNF : {0 Σ : Scope} -> SynthNF Σ -> CheckNF Σ -> SynthNF Σ
  appNF (SConsNF (LamNF x b sub) (CConsNF (PiNF d c))) a =
    checkSynth (checkNF (Cons x (checkSynth a d) sub) b) (appTypeFamilyNF c (checkSynth a d))
  appNF (SElimNF f) a = SElimNF (AppNF f a)

  export partial
  appTypeFamilyNF : {0 Σ : Scope} -> CheckNF Σ -> SynthNF Σ -> CheckNF Σ
  appTypeFamilyNF (CConsNF (LamNF x b sub)) a = checkNF (Cons x a sub) b
  appTypeFamilyNF (CElimNF f) a = CElimNF (AppNF f (synthCheck a))

  annNF : {0 Σ : Scope} -> CheckNF Σ -> CheckNF Σ -> SynthNF Σ
  annNF (CConsNF e) t = SConsNF e t
  annNF (CElimNF e) _ = SElimNF e

  export
  checkNF : {0 Σ, Σ' : Scope} -> Sub Σ Σ' -> Check Σ -> CheckNF Σ'
  checkNF sub (Typ l) = CConsNF (TypNF l)
  checkNF sub (Lam x e) = CConsNF (LamNF x e sub)
  checkNF sub (Pi d c) = CConsNF (PiNF (checkNF sub d) (checkNF sub c))
  checkNF sub (Syn e) = synthCheck (synthNF sub e)

public export
data Ctxt : Scope -> Type where
  EmptyCtxt : Ctxt []
  VarCtxt : {0 Σ : Scope} -> {0 x : Name} -> CheckNF Σ -> Ctxt Σ -> Ctxt (x :: Σ)

export
getVar : (Σ : Scope) -> Ctxt Σ -> (x : Name) -> Maybe (Thinning Σ [x], CheckNF Σ)
getVar [] EmptyCtxt _ = Nothing
getVar (x :: xs) (VarCtxt t ts) x' with (decEq x x')
  getVar (x :: xs) (VarCtxt t ts) x | Yes Refl = Just (the (Thinning (x :: xs) [x]) (Keep (discAll xs)), weakenChkNF (Disc (keepAll _)) t)
  _ | No _ = do
    (x, t) <- getVar xs ts x'
    pure (thinComp x (Disc (keepAll _)), weakenChkNF (Disc (keepAll _)) t)

keepAllCtxt : {0 Σ : Scope} -> Ctxt Σ -> Thinning Σ Σ
keepAllCtxt EmptyCtxt = Empty
keepAllCtxt (VarCtxt _ ctxt) = Keep (keepAllCtxt ctxt)

discAllCtxt : {0 Σ : Scope} -> Ctxt Σ -> Thinning Σ []
discAllCtxt EmptyCtxt = Empty
discAllCtxt (VarCtxt _ ctxt) = Disc (discAllCtxt ctxt)

export
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

mutual
  partial
  irrelevantConsNF : {Σ : Scope} -> ConsNF Σ -> Bool
  irrelevantConsNF (TypNF _) = False
  irrelevantConsNF (PiNF d c) = irrelevantChkNF (appTypeFamilyNF (weakenChkNF (the (Thinning ("x" :: Σ) Σ) (Disc (keepAll Σ))) c) (SElimNF (VarNF (Keep (discAll _)))))
  
  partial
  irrelevantChkNF : {Σ : Scope} -> CheckNF Σ -> Bool
  irrelevantChkNF (CConsNF a) = irrelevantConsNF a
  irrelevantChkNF (CElimNF _) = False

mutual
  partial
  synNFEq : {Σ : Scope} -> Ctxt Σ => SynthNF Σ -> SynthNF Σ -> Bool
  synNFEq (SElimNF a) (SElimNF b) = elimNFEq a b || irrelevantChkNF (elimType a)
  synNFEq (SConsNF a t) (SConsNF b _) = consNFEq a b t
  synNFEq _ _ = False

  partial
  chkNFEq : {Σ : Scope} -> {auto Γ : Ctxt Σ} -> CheckNF Σ -> CheckNF Σ -> CheckNF Σ -> Bool
  chkNFEq (CConsNF a) (CConsNF b) t = consNFEq a b t
  chkNFEq (CElimNF a) (CElimNF b) _ = elimNFEq a b || irrelevantChkNF (elimType a)
  chkNFEq _ _ _ = False

  partial
  elimNFEq : {Σ : Scope} -> Ctxt Σ => ElimNF Σ -> ElimNF Σ -> Bool
  elimNFEq (VarNF a) (VarNF b) = thinningEq a b
  elimNFEq (AppNF f_a a_a) (AppNF f_b a_b) =
    elimNFEq f_a f_b &&
    (let (CConsNF (PiNF d _)) = elimType f_a
     in chkNFEq a_a a_b d)
  elimNFEq _ _ = False

  partial
  consNFEq : {Σ : Scope} -> {auto Γ : Ctxt Σ} -> ConsNF Σ -> ConsNF Σ -> CheckNF Σ -> Bool
  consNFEq (TypNF a) (TypNF b) (CConsNF (TypNF _)) = a == b
  consNFEq (LamNF x_a a sub_a) (LamNF x_b b sub_b) (CConsNF (PiNF d c)) =
    let ctxt' : Ctxt (x_a :: Σ)
        ctxt' = VarCtxt d Γ
        weaken : CheckNF Σ -> CheckNF (x_a :: Σ)
        weaken = weakenChkNF (Disc (keepAll _))
    in
      chkNFEq {Σ = (x_a :: Σ)} {Γ = ctxt'}
        (checkNF (Cons x_a (SElimNF (VarNF (Keep (discAllCtxt Γ)))) (weakenSub sub_a (Disc (keepAll _)))) a)
        (checkNF (Cons x_b (SElimNF (VarNF (Keep (discAllCtxt Γ)))) (weakenSub sub_b (Disc (keepAll _)))) b)
        (appTypeFamilyNF (weaken c) (SElimNF (VarNF (Keep (discAll _)))))
  consNFEq (PiNF d_a c_a) (PiNF d_b c_b) (CConsNF (TypNF l)) =
    let weaken : CheckNF Σ -> CheckNF ("x" :: Σ)
        weaken = weakenChkNF (Disc (keepAll _))
        ctxt' : Ctxt ("x" :: Σ)
        ctxt' = VarCtxt d_a Γ
    in
    chkNFEq d_a d_b (CConsNF (TypNF l)) &&
    chkNFEq {Γ = ctxt'} (weaken c_a) (weaken c_b) (CConsNF (TypNF l))
  consNFEq _ _ _ = False

mutual
  partial
  typeConsEq : {Σ : Scope} -> Ctxt Σ -> ConsNF Σ -> ConsNF Σ -> Bool
  typeConsEq _ (TypNF a) (TypNF b) = a == b
  typeConsEq ctxt (PiNF d_a c_a) (PiNF d_b c_b) = typeEq ctxt d_a d_b && typeFamilyEq ctxt c_a c_b d_a
  typeConsEq _ _ _ = False
  
  export partial
  typeEq : {Σ : Scope} -> Ctxt Σ -> CheckNF Σ -> CheckNF Σ -> Bool
  typeEq ctxt (CConsNF a) (CConsNF b) = typeConsEq ctxt a b
  typeEq _ (CElimNF a) (CElimNF b) = elimNFEq a b
  typeEq _ _ _ = False

  partial
  typeFamilyEq : {Σ : Scope} -> Ctxt Σ -> CheckNF Σ -> CheckNF Σ -> CheckNF Σ -> Bool
  typeFamilyEq ctxt (CConsNF a) (CConsNF b) i = typeFamilyConsEq ctxt a b i
  typeFamilyEq _ (CElimNF a) (CElimNF b) _ = elimNFEq a b
  typeFamilyEq _ _ _ _ = False

  partial
  typeFamilyConsEq : {Σ : Scope} -> Ctxt Σ -> ConsNF Σ -> ConsNF Σ -> CheckNF Σ -> Bool
  typeFamilyConsEq ctxt (LamNF x_a a sub_a) (LamNF x_b b sub_b) i =
    let ctxt' : Ctxt (x_a :: Σ)
        ctxt' = VarCtxt i ctxt
        weaken : CheckNF Σ -> CheckNF (x_a :: Σ)
        weaken = weakenChkNF (Disc (keepAll _))
    in
      typeEq ctxt'
        (checkNF (Cons x_a (SElimNF (VarNF (Keep (discAllCtxt ctxt)))) (weakenSub sub_a (Disc (keepAll _)))) a)
        (checkNF (Cons x_b (SElimNF (VarNF (Keep (discAllCtxt ctxt)))) (weakenSub sub_b (Disc (keepAll _)))) b)

mutual
  partial
  quoteSynth : {Σ : Scope} -> SynthNF Σ -> Synth Σ
  quoteSynth (SElimNF e) = quoteElim e
  quoteSynth (SConsNF e t) = Ann (quoteCons e) (quoteCheck t)

  partial
  quoteCheck : {Σ : Scope} -> CheckNF Σ -> Check Σ
  quoteCheck (CConsNF e) = quoteCons e
  quoteCheck (CElimNF e) = Syn (quoteElim e)

  partial
  quoteElim : {Σ : Scope} -> ElimNF Σ -> Synth Σ
  quoteElim (VarNF x) = Var x
  quoteElim (AppNF a f) = App (quoteElim a) (quoteCheck f)

  partial
  quoteCons : {Σ : Scope} -> ConsNF Σ -> Check Σ
  quoteCons (TypNF l) = Typ l
  quoteCons (LamNF x b sub) = Lam x (quoteCheck (checkNF (Cons x (SElimNF (VarNF (Keep (discAll _)))) (weakenSub sub (Disc (keepAll _)))) b))
  quoteCons (PiNF d c) = Pi (quoteCheck d) (quoteCheck c)

export
showSynthNF : {Σ : Scope} -> SynthNF Σ -> String
showSynthNF = showSynth . quoteSynth

export
showCheckNF : {Σ : Scope} -> CheckNF Σ -> String
showCheckNF = showCheck . quoteCheck
