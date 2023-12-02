(def [Good : (Type 1)]
  (Π [X : (Type 0)]
    (-> (-> X X) X)))

(def [bad : Good -> Good]
  (λ bad
    (λ X (λ f (f ((bad X) f))))))

(def false
  (bad (λ X
