module Thinning

import Data.Singleton

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

thinningApp : (l : List a) -> Thinning l l' -> Singleton l'
thinningApp [] Empty = pure []
thinningApp (x :: xs) (Keep t) = pure (x ::) <*> thinningApp xs t
thinningApp (_ :: xs) (Disc t) = thinningApp xs t

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

