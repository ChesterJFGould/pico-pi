(: mk-pair
  (->
    (A : (Type 0))
    (B : (Type 0))
    (_ : A)
    (_ : B)
    (Σ (_ : A) (_ : B))))
(def mk-pair
  (λ (_ _ a b) (σ a b)))
