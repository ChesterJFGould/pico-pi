(def [id : (Π [A : (Type 1)] (Π (_ : A) A))]
  (λ [A : (Type 1)] (λ (a : A) a)))

(id (Type 0))
