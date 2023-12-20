(def [Nat-Arity : (-> [_ : (Bool : (Type 0 lzero))] (Type 0 lzero))]
  (λ tag
    (ind-Bool ((lsucc lzero) : ((Level 0) : (Type 1 lzero)))
      tag
      (λ _ (Type 0 lzero))
      Unit
      Empty)))

(def Nat
  (W [tag : (Bool : (Type 0 lzero))] (Nat-Arity tag)))

(def [z : Nat]
  (w
    false
    (λ e
      (ind-Empty
        (lzero : ((Level 0) : (Type 1 lzero)))
        e
        (λ _ Nat)))))

(def [s : (-> Nat Nat)]
  (λ n (w true (λ _ n))))

(def [two : Nat] (s (s z)))

#;
(def
  [ind-Nat :
    (Π [l : ((Level 0) : (Type 1 lzero))]
      (Π [m : (-> Nat (Type 0 l))]
        (Π [z-case : (m z)]
          (Π [s-case : (Π [n : Nat] (-> (m n) (m (s n))))]
            (Π [n : Nat] (m n))))))]
  (λ l (λ m (λ z-case (λ s-case (λ n
    (ind-W l n m
      (λ tag (λ d (λ ih
        ((ind-Bool l tag (λ t (Π [eq : (= (Bool : (Type 0 lzero)) t tag)] (m (w t d))))
          (λ eq
            (s-case
              (d (ind-= (lzero : ((Level 0) : (Type 1 lzero))) tag eq (λ tag (λ _ (Nat-Arity tag))) ()))
              (ih (ind-= (lzero : ((Level 0) : (Type 1 lzero))) tag eq (λ tag (λ _ (Nat-Arity tag))) ()))))
          (λ eq z-case)) Refl)))))))))))

(def
  [ind-Nat :
    (Π [l : ((Level 0) : (Type 1 lzero))]
      (Π [m : (-> Nat (Type 0 l))]
        (Π [z-case : (m z)]
          (Π [s-case : (Π [n : Nat] (-> (m n) (m (s n))))]
            (Π [n : Nat] (m n))))))]
  (λ l (λ m (λ z-case (λ s-case (λ n
    (ind-W l n m
      (λ tag (λ d (λ ih
        ((ind-Bool l tag (λ t (Π [d : (-> (Nat-Arity t) Nat)] (Π [ih : (-> [i : (Nat-Arity t)] (m (d i)))] (m (w t d)))))
          (λ d (λ ih
            (s-case
              (d ())
              (ih ()))))
          (λ d (λ ih z-case))) d ih)))))))))))

