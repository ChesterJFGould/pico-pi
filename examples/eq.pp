(def
  [Prop-transfer :
    (-> (A : (Type 0 lzero))
      (-> (P : (-> A (Type 0 lzero)))
        (-> (a : A)
          (-> (b : A)
            (-> (eq : (= A a b))
              (-> (p-a : (P a))
                (P b)))))))]
  (λ A (λ P (λ a (λ b (λ eq (λ p-a (ind-= lzero A a b (λ x (λ _ (P x))) eq p-a))))))))
