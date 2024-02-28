(def [if : (-> Bool (Type 0 lzero) (Type 0 lzero) (Type 0 lzero))]
  (λ b A B
    (ind-Bool (lsucc lzero) b
      (λ _ (Type 0 lzero))
      A
      B)))

(def [stringOrInt : (-> [b : Bool] (if b Unit Bool))]
  (λ b
    (ind-Bool lzero b
      (λ b (if b Unit Bool))
      ()
      false)))
