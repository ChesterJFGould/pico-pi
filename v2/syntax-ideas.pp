Σ : {A : Type} -> (-> A Type) -> Type

(def Dyn (Σ [type : Type] type))

(def [dyn : (-> [type : Type] type Dyn)]
  [A] [a]
  [apply cons]
  A a)

;; Above is same as:
(def [dyn : (-> [type : Type] type Dyn)]
  [A] [a]
  (cons A a))

(def dyn-unit (dyn Unit ()))
(def dyn-bool (dyn Bool true))

#|
+ :: Nat -> Nat -> Nat
+ Z b = b
+ (S a) b = S (+ a) b)
|#

ind-Nat :
  (-> [l : (Level 0)]
      [m : (-> Nat (Type 0 l))]
      (m zero)
      (-> [n : Nat] [ih : (m n)] (m (add1 n)))
      (-> [n : Nat] (m n)))

(def [+ : (-> Nat Nat Nat)]
  [apply ind-Nat] lzero
  ([a : Nat] (-> [b : Nat] Nat))
  ([b] b)
  ([a] [ih : (-> Nat Nat)] [b] (add1 (ih b))))
