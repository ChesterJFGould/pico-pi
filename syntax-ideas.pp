(def my-cons
  [A : Type] [B : Type] [a : A] [b : B]
  {field car a}
  {field cdr b})

(def dyn
  [A : Type] [a : A]
  {field type A}
  {field [val : type] a})

(def Dyn (Σ [type : Type] [val : type] ()))

(def dyn-unit : Dyn (dyn Unit ()))
(def dyn-bool : Dyn (dyn Bool true))

(def Σ : (-> {Dom : Type} [CoDom : (-> Dom Type)] Type)
  {Dom : Type} [CoDom : (-> Dom Type)]
  (SIGMA [x : Dom] (CoDom x)))
