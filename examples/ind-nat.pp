(def [Nat*-Arity : (-> [_ : (Bool : (Type 0 lzero))] (Type 0 lzero))]
  (λ tag (ind-Bool ((lsucc lzero) : ((Level 0) : (Type 1 lzero)))
      tag
      (λ _ (Type 0 lzero))
      Unit
      Empty)))

(def Nat*
  (W [tag : (Bool : (Type 0 lzero))] (Nat*-Arity tag)))

(def [z*-data : (-> (Empty : (Type 0 lzero)) Nat*)]
  (λ e
    (ind-Empty
      (lzero : ((Level 0) : (Type 1 lzero)))
      e
      (λ _ Nat*))))

(def [z* : Nat*]
  (w false z*-data))

(def [s* : (-> Nat* Nat*)]
  (λ n (w true (λ _ n))))

(def [Nat*-Canonical : (-> Nat* (Type 0 lzero))]
  (λ n
    (ind-W ((lsucc lzero) : ((Level 0) : (Type 1 lzero))) n
      (λ _ (Type 0 lzero))
      (λ tag (λ d (λ ih
        ((ind-Bool ((lsucc lzero) : ((Level 0) : (Type 1 lzero))) tag
          (λ tag (-> (-> (Nat*-Arity tag) Nat*) (-> (-> (Nat*-Arity tag) (Type 0 lzero)) (Type 0 lzero))))
          (λ d (λ ih (ih ())))
          (λ d (λ _ (= (-> (Empty : (Type 0 lzero)) Nat*) z*-data d)))) d ih)))))))

(def Nat (Σ [n : Nat*] (Nat*-Canonical n)))

(def [z : Nat] (cons z* Refl))

(def [s : (-> Nat Nat)]
  (λ nn
    (cons (w true (λ _ (first nn))) (second nn))))

(def [two : Nat] (s (s z)))

(def
  [ind-Nat :
    (Π [l : ((Level 0) : (Type 1 lzero))]
      (Π [m : (-> Nat (Type 0 l))]
        (Π [z-case : (m z)]
          (Π [s-case : (Π [n : Nat] (Π [ih : (m n)] (m (s n))))]
            (Π [n : Nat]
              (m n))))))]
  (λ l (λ m (λ z-case (λ s-case (λ n
    ((ind-W l (first n)
      (λ n (Π [n-canon : (Nat*-Canonical n)] (m (cons n n-canon))))
      (λ t
        (ind-Bool l t
          (λ t
            (Π [d : (-> (Nat*-Arity t) Nat*)]
              (Π
                [ih :
                  (Π [i : (Nat*-Arity t)]
                    (Π [n-canon : (Nat*-Canonical (d i))]
                      (m (cons (d i) n-canon))))]
                (Π [n-canon : (Nat*-Canonical (w t d))]
                  (m (cons (w t d) n-canon))))))
          (λ d (λ ih (λ n-canon
            (s-case (cons (d ()) n-canon) (ih () n-canon)))))
          (λ d (λ ih (λ n-canon
            (ind-= l d n-canon
              (λ d (λ prf (m (cons (w false d) prf))))
              z-case))))))) (second n))))))))

(def [+ : (-> Nat (-> Nat Nat))]
  (λ m (λ n
  (ind-Nat (lzero : ((Level 0) : (Type 1 lzero)))
    (λ _ Nat)
    n
    (λ _ (λ ih (s ih)))
    m))))

(def [+-zero-l : (Π [a : Nat] (= Nat (+ z a) a))]
  (λ a Refl))

(def
  [cong :
    (Π [A : (Type 0 lzero)]
      (Π [B : (Type 0 lzero)]
        (Π [f : (-> A B)]
          (Π [a : A]
            (Π [b : A]
              (Π [prf : (= A a b)]
                (= B (f a) (f b))))))))]
  (λ A (λ B (λ f (λ a (λ b (λ prf
    (ind-= (lzero : ((Level 0) : (Type 1 lzero))) b prf
      (λ b (λ _ (= B (f a) (f b))))
      Refl))))))))

(def [+-zero-r : (Π [a : Nat] (= Nat (+ a z) a))]
  (ind-Nat (lzero : ((Level 0) : (Type 1 lzero)))
    (λ a (= Nat (+ a z) a))
    Refl
    (λ a (λ ih (cong Nat Nat s (+ a z) a ih)))))
