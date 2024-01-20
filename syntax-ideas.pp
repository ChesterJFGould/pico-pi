(def Dyn (Σ [type : Type] type))

(def [dyn : Dyn]
  [A] [a]
  [elim cons] A a)

;; Above is same as:
(def [dyn : Dyn]
  [A] [a]
  (cons A a))

(def dyn-unit (dyn Unit ()))
(def dyn-bool (dyn Bool true))

(def [+ : (-> Nat Nat Nat)]
  [elim ind-Nat] lzero
  ([a : Nat] (Π [b : Nat] Nat))
  ([b] b)
  ([a] [ih : (-> Nat Nat)] [b] (s (ih b))))
