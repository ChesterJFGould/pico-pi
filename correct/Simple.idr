module Simple

import Decidable.Equality
import Prelude

data Typ : Type where
  NatT : Typ
  FunT : Typ -> Typ -> Typ

Uninhabited (NatT = FunT d c) where
  uninhabited prf impossible

Uninhabited (FunT d c = NatT) where
  uninhabited prf impossible

Uninhabited (FunT d c = FunT d' c', Not (d = d')) where
  uninhabited (Refl, bad) = bad Refl

Uninhabited (FunT d c = FunT d' c', Not (c = c')) where
  uninhabited (Refl, bad) = bad Refl

decEqTyp : (a : Typ) -> (b : Typ) -> Dec (a = b)
decEqTyp NatT NatT = Yes Refl
decEqTyp (FunT a_dom a_codom) (FunT b_dom b_codom) =
  case (decEqTyp a_dom b_dom, decEqTyp a_codom b_codom) of
    (Yes Refl, Yes Refl) => Yes Refl
    (No domPrf, _) => No (\eq => absurd (eq, domPrf))
    (_, No codomPrf) => No (\eq => absurd (eq, codomPrf))
decEqTyp NatT (FunT _ _) = No absurd
decEqTyp (FunT _ _) NatT = No absurd

DecEq Typ where
  decEq = decEqTyp

{-
data IList : {a : Type} -> (a -> Type) -> List a -> Type where
  Nil : {0 f : a -> Type} -> IList f []
  Cons : {0 f : a -> Type} -> (0 x : a) -> (f x) -> IList f xs -> IList f (x :: xs)

data Thinning : {xs, ys : List a} -> IList f xs -> IList f ys -> Type where
  Empty : Thinning Nil Nil
  -- Keep : {0 a : Type} -> {0 f : a -> Type} -> {0 y : a} -> {0 as' : List a} -> (x : f y) -> Thinning as bs -> Thinning {xs = as'} (the (IList f (y :: as')) (x :: as)) (x :: bs)
  Keep : {0 a : Type} -> {0 f : a -> Type} -> {0 y : a} -> {x : f y} -> {0 xis, yis : List a} -> {0 xs : IList f xis} -> {0 ys : IList f yis} ->
         Thinning xs ys -> Thinning {xs = (y :: xis)} {ys = (y :: yis)} (Cons y x xs) (Cons y x ys)
  Disc : {0 a : Type} -> {0 f : a -> Type} -> {0 y : a} -> {x : f y} -> {0 xis, yis : List a} -> {0 xs : IList f xis} -> {0 ys : IList f yis} ->
         Thinning xs ys -> Thinning {xs = (y :: xis)} {ys = yis} (Cons y x xs) ys
-}

data Thinning : List a -> List a -> Type where
  Empty : Thinning Nil Nil
  Keep : Thinning as bs -> Thinning (a :: as) (a :: bs)
  Disc : Thinning as bs -> Thinning (a :: as) bs

ObsThinningEq : Thinning a b -> Thinning a c -> Type
ObsThinningEq Empty Empty = Unit
ObsThinningEq (Keep ab) (Keep ac) = ab ~=~ ac
ObsThinningEq (Disc ab) (Disc ac) = ab ~=~ ac
ObsThinningEq _ _ = Void

useThinningEq : {ab : Thinning a b} -> {ac : Thinning a c} -> ab ~=~ ac -> ObsThinningEq ab ac
useThinningEq {ab = Empty} {ac = Empty} _ = ()
useThinningEq {ab = (Keep ab)} {ac = (Keep ab)} Refl = Refl
useThinningEq {ab = (Disc ab)} {ac = (Disc ab)} Refl = Refl
useThinningEq {ab = (Disc ab)} {ac = (Keep ac)} prf impossible
useThinningEq {ab = (Keep ab)} {ac = (Disc ac)} prf impossible

decThinningEq : (ab : Thinning a b) -> (ac : Thinning a c) -> Dec (ab ~=~ ac)
decThinningEq Empty Empty = Yes Refl
decThinningEq (Keep ab) (Keep ac) =
  case (decThinningEq ab ac) of
    Yes Refl => Yes Refl
    No prf => No (prf . useThinningEq)
decThinningEq (Disc ab) (Disc ac) =
  case (decThinningEq ab ac) of
    Yes Refl => Yes Refl
    No prf => No (prf . useThinningEq)
decThinningEq (Keep ab) (Disc ac) = No useThinningEq
decThinningEq (Disc ab) (Keep ac) = No useThinningEq

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

Ctxt : Type
Ctxt = List Typ

mutual
  data Synth : Ctxt -> Typ -> Type where
    Var : {0 Γ : Ctxt} -> Thinning Γ [t] -> Synth Γ t
    App : {0 Γ : Ctxt} -> Synth Γ (FunT d c) -> Check Γ d -> Synth Γ c
    Rec : {0 Γ : Ctxt} -> (x : Typ) -> Check Γ x -> Check Γ (FunT x x) -> Check Γ NatT -> Synth Γ x
    Ann : {0 Γ : Ctxt} -> (x : Typ) -> Check Γ x -> Synth Γ x
  
  data Check : Ctxt -> Typ -> Type where
    Lam : {0 Γ : Ctxt} -> {d : Typ} -> String -> Check (d :: Γ) c -> Check Γ (FunT d c)
    Zer : {0 Γ : Ctxt} -> Check Γ NatT
    Suc : {0 Γ : Ctxt} -> Check Γ NatT -> Check Γ NatT
    Syn : {0 Γ : Ctxt} -> Synth Γ x -> Check Γ x

namespace Ast
  public export
  data Ast =
      Var String
    | Lam String Ast
    | App Ast Ast
    | Zer
    | Suc Ast
    | Ann Typ Ast

ElabCtxt : Type
ElabCtxt = List (String, Typ)

elabCtxt : ElabCtxt -> Ctxt
elabCtxt [] = []
elabCtxt ((_, t) :: rest) = t :: elabCtxt rest

data TypeError =
    UnboundVar String
  | CannotSynth Ast.Ast
  | ExpectedFun Ast.Ast Typ
  | CheckMismatch Ast.Ast Typ
  | Expected Ast.Ast Typ Typ

data TC : Type -> Type where
  PurTC : a -> TC a
  ErrTC : TypeError -> TC a
  MapTC : (a -> b) -> TC a -> TC b
  AppTC : TC (a -> b) -> TC a -> TC b
  SeqTC : TC a -> (a -> TC b) -> TC b

Functor TC where
  map = MapTC

Applicative TC where
  pure = PurTC
  (<*>) = AppTC

Monad TC where
  (>>=) = SeqTC

typeError : TypeError -> TC a
typeError = ErrTC

getVar : (ctxt : ElabCtxt) -> String -> Maybe (typ : Typ ** Thinning (elabCtxt ctxt) [typ])
getVar [] _ = Nothing
getVar ((x, typ) :: rest) x' =
  if x == x'
  then Just (typ ** Keep (discAll (elabCtxt rest)))
  else (\(typ ** thin) => (typ ** Disc thin)) <$> getVar rest x'

mutual
  synth : Ast.Ast -> (ctxt : ElabCtxt) -> TC (typ : Typ ** Synth (elabCtxt ctxt) typ)
  synth (Var str) ctxt = do
    (typ ** thin) <- maybe (typeError (UnboundVar str)) pure (getVar ctxt str)
    pure (typ ** Var thin)
  synth (Lam x b) _ = typeError (CannotSynth (Lam x b))
  synth (App f a) ctxt = do
    (dom ** codom ** f') <- synthFun f ctxt
    a' <- check a dom ctxt
    pure (codom ** App f' a')
  synth Zer _ = typeError (CannotSynth Zer)
  synth (Suc n) _ = typeError (CannotSynth (Suc n))
  synth (Ann t e) ctxt = do
    e' <- check e t ctxt
    pure (t ** Ann t e')
  
  synthFun : Ast.Ast -> (ctxt : ElabCtxt) -> TC (dom : Typ ** codom : Typ ** Synth (elabCtxt ctxt) (FunT dom codom))
  synthFun e ctxt = do
    (typ ** e') <- synth e ctxt
    case typ of
      FunT dom codom => pure (dom ** codom ** e')
      _ => typeError (ExpectedFun e typ)
  
  check : Ast.Ast -> (typ : Typ) -> (ctxt : ElabCtxt) -> TC (Check (elabCtxt ctxt) typ)
  check (Lam x b) (FunT dom codom) ctxt = do
    b' <- check b codom ((x, dom) :: ctxt)
    pure (Lam x b')
  check (Lam x b) typ _ = typeError (CheckMismatch (Lam x b) typ)
  check Zer NatT _ = pure Zer
  check Zer typ _ = typeError (CheckMismatch Zer typ)
  check (Suc n) NatT ctxt = Suc <$> check n NatT ctxt
  check (Suc n) typ _ = typeError (CheckMismatch (Suc n) typ)
  check e typ ctxt = do
    (typ' ** e') <- synth e ctxt
    case decEq typ typ' of
      Yes Refl => pure (Syn e')
      No _ => typeError (Expected e typ typ')

Denote : Typ -> Type
Denote NatT = Nat
Denote (FunT dom codom) = Denote dom -> Denote codom

data IList : {a : Type} -> (a -> Type) -> List a -> Type where
  Nil : {0 f : a -> Type} -> IList f []
  Cons : {0 f : a -> Type} -> (0 x : a) -> (f x) -> IList f xs -> IList f (x :: xs)

reindexIList : {0 a : Type} -> {0 l : List a} -> {0 f : a -> Type} -> {0 g : a -> Type} -> ((0 x : a) -> f x -> g x) -> IList f l -> IList g l
reindexIList f Nil = Nil
reindexIList f (Cons x a as) = Cons x (f x a) (reindexIList f as)

data IThinning : {xs, ys : List a} -> IList f xs -> IList f ys -> Type where
  IEmpty : IThinning Nil Nil
  IKeep : {0 a : Type} -> {0 f : a -> Type} -> {0 y : a} -> {x : f y} -> {0 xis, yis : List a} -> {0 xs : IList f xis} -> {0 ys : IList f yis} ->
         IThinning xs ys -> IThinning {xs = (y :: xis)} {ys = (y :: yis)} (Cons y x xs) (Cons y x ys)
  IDisc : {0 a : Type} -> {0 f : a -> Type} -> {0 y : a} -> {x : f y} -> {0 xis, yis : List a} -> {0 xs : IList f xis} -> {0 ys : IList f yis} ->
         IThinning xs ys -> IThinning {xs = (y :: xis)} {ys = yis} (Cons y x xs) ys

indexThinning : (il : IList f l) -> Thinning l l' -> (il' : IList f l' ** IThinning il il')
indexThinning [] Empty = ([] ** IEmpty)
indexThinning (Cons x a as) (Keep t) =
  let (il' ** t') = indexThinning as t
  in ((Cons x a il') ** (IKeep t'))
indexThinning (Cons _ _ as) (Disc t) =
  let (il' ** t') = indexThinning as t
  in (il' ** IDisc t')

Env : Ctxt -> Type
Env = IList Denote

mutual
  denoteSynth : {0 Γ : Ctxt} -> Synth Γ typ -> Env Γ -> Denote typ
  denoteSynth (Var x) env =
    let ((Cons _ v _) ** _) = indexThinning env x
    in v
  denoteSynth (App f a) env = denoteSynth f env (denoteCheck a env)
  denoteSynth (Rec _ z succ n) env = denoteRec (denoteCheck z env) (denoteCheck succ env) (denoteCheck n env)
  denoteSynth (Ann _ e) env = denoteCheck e env

  denoteRec : Denote x -> Denote (FunT x x) -> Denote NatT -> Denote x
  denoteRec z succ Z = z
  denoteRec z succ (S n) = succ (denoteRec z succ n)

  denoteCheck : {0 Γ : Ctxt} -> Check Γ typ -> Env Γ -> Denote typ
  denoteCheck (Lam _ b) env = \v => denoteCheck b (Cons _ v env)
  denoteCheck Zer env = 0
  denoteCheck (Suc n) env = 1 + denoteCheck n env
  denoteCheck (Syn e) env = denoteSynth e env

mutual
  weakenSyn : {0 Γ, Δ : Ctxt} -> Thinning Γ Δ -> Synth Δ t -> Synth Γ t
  weakenSyn t (Var x) = Var (thinComp x t)
  weakenSyn t (App f a) = App (weakenSyn t f) (weakenChk t a)
  weakenSyn t (Rec x z succ n) = Rec x (weakenChk t z) (weakenChk t succ) (weakenChk t n)
  weakenSyn t (Ann x e) = Ann x (weakenChk t e)
  
  weakenChk : {0 Γ, Δ : Ctxt} -> Thinning Γ Δ -> Check Δ t -> Check Γ t
  weakenChk t (Lam x b) = Lam x (weakenChk (Keep t) b)
  weakenChk t Zer = Zer
  weakenChk t (Suc n) = Suc (weakenChk t n)
  weakenChk t (Syn e) = Syn (weakenSyn t e)

Sub : Ctxt -> Ctxt -> Type
Sub from to = IList (\typ => Synth to typ) from

weakenSub : {Γ, Δ, Δ' : Ctxt} -> Sub Γ Δ -> Thinning Δ' Δ -> Sub Γ Δ'
weakenSub sub thin = reindexIList (\x, e => weakenSyn thin e) sub

keepSub : (Γ : Ctxt) -> Sub Γ Γ

mutual
  {-
  substSyn : {Γ, Γ' : Ctxt} -> Thinning (Γ ++ [t] ++ Γ') [t] -> Synth (Γ ++ Γ') t -> Synth (Γ ++ [t] ++ Γ') s -> Synth (Γ ++ Γ') s
  substSyn x v (Var x') =
    case (decThinningEq x x') of
      Yes Refl => v
      No prf => ?ssn
  substSyn x v e = ?ss

  substChk : {Γ : Ctxt} -> Synth Γ t -> Check (t :: Γ) s -> Check Γ s
  -}

  substSyn : {Γ, Δ : Ctxt} -> Synth Γ t -> Sub Γ Δ -> Synth Δ t
  substSyn (Var x) sub =
    let ((Cons _ e _) ** _) = indexThinning sub x
    in e
  substSyn (App f a) sub = App (substSyn f sub) (substChk a sub)
  substSyn (Rec x z succ n) sub = Rec x (substChk z sub) (substChk succ sub) (substChk n sub)
  substSyn (Ann x e) sub = Ann x (substChk e sub)
  
  substChk : {Γ, Δ : Ctxt} -> Check Γ t -> Sub Γ Δ -> Check Δ t
  substChk (Lam {d} x b) sub =
    Lam x
      (substChk b
        (Cons d (Var (Keep (discAll _))) (weakenSub sub (Disc (keepAll _)))))
  substChk Zer sub = Zer
  substChk (Suc n) sub = Suc (substChk n sub)
  substChk (Syn e) sub = Syn (substSyn e sub)

mutual
  data SynthEq : (Γ : Ctxt) -> (typ : Typ) -> Synth Γ typ -> Synth Γ typ -> Type where
    VarEq : {Γ : Ctxt} -> {thin : Thinning Γ [t]} ->
            SynthEq Γ t (Var thin) (Var thin)
    AppEq : {Γ : Ctxt} -> {f, f' : Synth Γ (FunT dom codom)} -> {a, a' : Check Γ dom} ->
            SynthEq Γ (FunT dom codom) f f' -> CheckEq Γ dom a a' ->
            SynthEq Γ codom (App f a) (App f' a')
    RecEq : {Γ : Ctxt} -> {z, z' : Check Γ x} -> {succ, succ' : Check Γ (FunT x x)} -> {n, n' : Check Γ NatT} ->
            CheckEq Γ x z z' -> CheckEq Γ (FunT x x) succ succ' -> CheckEq Γ NatT n n' ->
            SynthEq Γ x (Rec x z succ n) (Rec x z' succ' n')
    AnnEq : {Γ : Ctxt} -> {e, e' : Check Γ t} ->
            CheckEq Γ t e e' ->
            SynthEq Γ t (Ann t e) (Ann t e')
    BetaEq : {Γ : Ctxt} -> {b : Check (dom :: Γ) codom} -> {a : Check Γ dom} ->
             SynthEq Γ codom
               (App (Ann (FunT dom codom) (Lam x b)) a)
               (Ann codom (substChk b (Cons _ (Ann dom a) ?bes)))
    AnnSynEq : {Γ : Ctxt} -> {e : Synth Γ t} ->
               SynthEq Γ t (Ann t (Syn e)) e

  data CheckEq : (Γ : Ctxt) -> (typ : Typ) -> Check Γ typ -> Check Γ typ -> Type where
    LamEq : {Γ : Ctxt} -> {b, b' : Check (dom :: Γ) codom} ->
            CheckEq (dom :: Γ) codom b b' ->
            CheckEq Γ (FunT dom codom) (Lam x b) (Lam y b')
    ZerEq : {Γ : Ctxt} ->
            CheckEq Γ NatT Zer Zer
    SucEq : {Γ : Ctxt} -> {n, n' : Check Γ NatT} ->
            CheckEq Γ NatT n n' ->
            CheckEq Γ NatT (Suc n) (Suc n')
    SynEq : {Γ : Ctxt} -> {e, e' : Synth Γ t} ->
            SynthEq Γ t e e' ->
            CheckEq Γ t (Syn e) (Syn e')
    EtaEq : {Γ : Ctxt} -> {f : Synth Γ (FunT dom codom)} ->
            CheckEq Γ (FunT dom codom) (Syn f) (Lam x (Syn (App (weakenSyn (Disc (keepAll Γ)) f) (Syn (Var ?v)))))
    SynAnnEq : {Γ : Ctxt} -> {e : Check Γ t} ->
               CheckEq Γ t (Syn (Ann t e)) e
