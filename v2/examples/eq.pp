(def
  [Prop-transfer :
    (-> (A : (Type 0 lzero))
      (-> (P : (-> A (Type 0 lzero)))
        (-> (a : A)
          (-> (b : A)
            (-> (eq : (= A a b))
              (-> (p-a : (P a))
                (P b)))))))]
  (λ A (λ P (λ a (λ b (λ eq (λ p-a (ind-= (lzero : ((Level 0) : (Type 1 lzero))) b eq (λ x (λ _ (P x))) p-a))))))))
