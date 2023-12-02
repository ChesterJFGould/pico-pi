(def [Nat : (Type 1)]
  (Π [X : (Type 0)]
    (Π [zero : X]
      (Π [succ : (-> X X)]
        X))))

(def [zero : Nat]
  (λ _ (λ zero (λ succ zero))))

(def [succ : (-> Nat Nat)]
  (λ n (λ X (λ zero (λ succ (succ (((n X) zero) succ)))))))

(def [+ : (-> Nat (-> Nat Nat))]
  (λ a (λ b
    (λ X (λ zero (λ succ
      (((a X) (((b X) zero) succ)) succ)))))))

(def [* : (-> Nat (-> Nat Nat))]
  (λ a (λ b
    (λ X (λ zero (λ succ
      (((a X) zero) (λ x (((b X) x) succ)))))))))

(def one (succ zero))

(def two ((+ one) one))

(def four ((* two) two))

(def sixteen ((* four) four))
