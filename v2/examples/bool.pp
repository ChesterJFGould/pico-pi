(def [Either : (Π [A : (Type 0 lzero)] (-> Bool (Type 0 lzero)))]
  (λ A (λ b
    (ind-Bool
      (lzero : ((Level 0) : (Type 1 lzero)))
      b
      (λ b (ind-Bool (lzero : ((Level 0) : (Type 1 lzero))) b (λ _ (Type 0 lzero)) A Unit))
