(def Bool
  (-> [A : (Type 0 (lsucc lzero))]
    (-> A (-> A A))))

(def [true : Bool]
  (λ A (λ t (λ f t))))

(def [false : Bool]
  (λ A (λ t (λ f f))))

(def [if : (-> Bool (-> [A : (Type 0 (lsucc lzero))] (-> A (-> A A))))]
  (λ b b))

(def
  [if-true :
    (-> [A : (Type 0 (lsucc lzero))]
      (-> [t : A]
        (-> [f : A]
          (= A t (if true A t f)))))]
  (λ A (λ t (λ f Refl))))

(def
  [if-false :
    (-> [A : (Type 0 (lsucc lzero))]
      (-> [t : A]
        (-> [f : A]
          (= A f (if false A t f)))))]
  (λ A (λ t (λ f Refl))))

(def Nat
  (W [tag : Bool] (if tag (Type 0 lzero) Unit Empty)))

(def [z : Nat]
  (w
    false
    (λ e
      (ind-Empty
        ((lsucc (lsucc lzero)) : ((Level 0) : (Type 1 lzero)))
        e
        (λ _ Nat)))))

(def [s : (-> Nat Nat)]
  (λ n (w true (λ _ n))))

(def [two : Nat] (s (s z)))

(def
  [iter-Nat :
    (-> [A : (Type 0 (lsucc lzero))]
      (-> A
        (-> (-> A A)
          (-> Nat
            A))))]
  (λ A (λ z-case (λ s-case (λ n
  (ind-W ((lsucc lzero) : ((Level 0) : (Type 1 lzero))) n (λ _ A)
    (λ tag (λ _ (λ ih
      (if tag A (s-case (ih ())) z-case))))))))))
