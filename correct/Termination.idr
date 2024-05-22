module Termination

import Control.WellFounded
import Data.Nat

partial
quicksort : Ord a => List a -> List a
quicksort [] = []
quicksort (a :: l) = quicksort (filter (<= a) l) ++ [a] ++ quicksort (filter (> a) l)

data QuicksortCallTree : Ord a => List a -> Type where
  Empty : Ord a => QuicksortCallTree (the (List a) [])
  Cons : Ord a => {0 x : a} -> {0 l : List a} ->
         QuicksortCallTree (filter (<= x) l) -> QuicksortCallTree (filter (> x) l) ->
         QuicksortCallTree (x :: l)

total
quicksortCT : Ord a => (l : List a) -> (0 _ : QuicksortCallTree l) -> List a
quicksortCT [] Empty = []
quicksortCT (a :: l) (Cons left right) =
  concat [quicksortCT (filter (<= a) l) left, [a], quicksortCT (filter (> a) l) right]

filterLTE : (p : a -> Bool) -> (l : List a) -> LTE (length (filter p l)) (length l)
filterLTE p [] = LTEZero
filterLTE p (a :: l) with (p a)
  _ | True = LTESucc (filterLTE p l)
  _ | False = lteSuccRight (filterLTE p l)

quicksortTerminationStep : Ord a => (l : List a) -> ((l' : List a) -> Smaller l' l -> QuicksortCallTree l') -> QuicksortCallTree l
quicksortTerminationStep [] _ = Empty
quicksortTerminationStep (a :: l) ind = Cons (ind (filter (<= a) l) (LTESucc (filterLTE (<= a) l))) (ind (filter (> a) l) (LTESucc (filterLTE (> a) l)))

total
quicksortTerminates : Ord a => (l : List a) -> QuicksortCallTree l
quicksortTerminates = sizeInd quicksortTerminationStep

total
quicksort' : Ord a => List a -> List a
quicksort' l = quicksortCT l (quicksortTerminates l)
