(def [Nat*-Arity : (-> Bool (Type 0 lzero))]
  (λ tag
    (ind-Bool (lsucc lzero) tag
      (λ _ (Type 0 lzero))
      Unit
      Empty)))

(def Nat* (W [tag : Bool] (Nat*-Arity tag)))

(def [z*-data : (-> Empty Nat*)]
  (λ e
    (ind-Empty lzero e
      Nat*)))

(def [z* : Nat*]
  (w false z*-data))

(def [s* : (-> Nat* Nat*)]
  (λ n (w true (λ _ n))))

(def [Nat*-Canonical : (-> Nat* (Type 0 lzero))]
  (λ n
    (ind-W (lsucc lzero) n
      (λ _ (Type 0 lzero))
      (λ tag d ih
        ((ind-Bool (lsucc lzero) tag
          (λ tag
            (-> (-> (Nat*-Arity tag) Nat*)
                (-> (Nat*-Arity tag) (Type 0 lzero))
                (Type 0 lzero)))
          (λ d ih (ih ()))
          (λ d _ (= (-> Empty Nat*) z*-data d))) d ih)))))

(def Nat (Σ [n : Nat*] (Nat*-Canonical n)))

(def [z : Nat] (cons z* Refl))

(def [s : (-> Nat Nat)]
  (λ n
    (cons
      (w true (λ _ (first n)))
      (second n))))

(def [two : Nat] (s (s z)))

(def
  [ind-Nat :
    (Π [l : (Level 0)]
       [m : (-> Nat (Type 0 l))]
       [z-case : (m z)]
       [s-case : (Π [n : Nat] [ih : (m n)] (m (s n)))]
       [n : Nat]
       (m n))]
  (λ l m z-case s-case n
    ((ind-W l (first n)
      (λ n (Π [n-canon : (Nat*-Canonical n)] (m (cons n n-canon))))
      (λ t
        (ind-Bool l t
          (λ t
            (Π [d : (-> (Nat*-Arity t) Nat*)]
               [ih :
                 (Π [i : (Nat*-Arity t)]
                    [n-canon : (Nat*-Canonical (d i))]
                    (m (cons (d i) n-canon)))]
               [n-canon : (Nat*-Canonical (w t d))]
               (m (cons (w t d) n-canon))))
          (λ d ih n-canon
            (s-case (cons (d ()) n-canon) (ih () n-canon)))
          (λ d ih n-canon
            (ind-= l n-canon
              (λ d prf (m (cons (w false d) prf)))
              z-case))))) (second n))))

(def [+ : (-> Nat Nat Nat)]
  (λ m (λ n
  (ind-Nat lzero
    (λ _ Nat)
    n
    (λ _ (λ ih (s ih)))
    m))))

(def [eq-four : (= Nat (+ two two) (s (s (s (s z)))))] Refl)

(def [+-zero-l : (Π [a : Nat] (= Nat (+ z a) a))]
  (λ a Refl))

(def
  [cong :
    (Π [A : (Type 0 lzero)]
       [B : (Type 0 lzero)]
       [f : (-> A B)]
       [a : A]
       [b : A]
       [prf : (= A a b)]
       (= B (f a) (f b)))]
  (λ A B f a b prf
    (ind-= lzero prf
      (λ b _ (= B (f a) (f b)))
      Refl)))

(def [+-zero-r : (Π [a : Nat] (= Nat (+ a z) a))]
  (ind-Nat lzero
    (λ a (= Nat (+ a z) a))
    Refl
    (λ a ih (cong Nat Nat s (+ a z) a ih))))

(def
  [symm :
    (Π [A : (Type 0 lzero)]
       [a : A]
       [b : A]
       [prf : (= A a b)]
       (= A b a))]
  (λ A a b prf
    (ind-= lzero prf
      (λ b _ (= A b a))
      Refl)))

(def
  [trans :
    (Π [A : (Type 0 lzero)]
       [a : A]
       [b : A]
       [c : A]
       [prf-a : (= A a b)]
       [prf-b : (= A b c)]
       (= A a c))]
  (λ A a b c prf-a prf-b
    (ind-= lzero (symm A a b prf-a)
      (λ a _ (= A a c))
      prf-b)))

(def
  [lemma0 :
    (Π [a : Nat]
       [b : Nat]
       (= Nat (+ (s a) b) (+ a (s b))))]
  (ind-Nat lzero
    (λ a (Π [b : Nat] (= Nat (s (+ a b)) (+ a (s b)))))
    (λ b Refl)
    (λ a ih b (cong Nat Nat s (s (+ a b)) (+ a (s b)) (ih b)))))

(def
  [+-comm :
    (Π [a : Nat]
       [b : Nat]
       (= Nat (+ a b) (+ b a)))]
  (ind-Nat lzero
    (λ a (Π [b : Nat] (= Nat (+ a b) (+ b a))))
    (λ b (symm Nat (+ b z) b (+-zero-r b)))
    (λ a ih b
      (trans
        Nat
        (+ (s a) b)
        (+ (s b) a)
        (+ b (s a))
        (cong Nat Nat s (+ a b) (+ b a) (ih b))
        (lemma0 b a)))))
