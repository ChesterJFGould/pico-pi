(sort Ty ())
(sort Tm ([e Ty]))

(constructor = () ([A Ty] [a (Tm A)] [b (Tm A)]) Ty)
(constructor Refl ([A Ty] [a (Tm A)]) () (Tm (= A a a)))
(destructor ind-=
  ([A Ty] [a (Tm A)] [b (Tm A)])
  ([eq (Tm (= A a b))])
  ([P (([b (Tm A)] [prf (Tm (= A a b))]) Ty)]
   [refl (Tm (P a Refl))])
  (Tm (P b eq)))

(constructor Nat () () Ty)
(constructor Z () () (Tm Nat))
(constructor S
  ()
  ([n (Tm Nat)])
  (Tm Nat))
(destructor ind-Nat
  ()
  ([n (Tm Nat)])
  ([P (([n (Tm Nat)]) Ty)]
   [z (Tm (P Z))]
   [s (([n (Tm Nat)] [ih (Tm (P n))]) (Tm (P (S n))))])
  (Tm (P n)))
(destructor ind-Nat-Z
  ()
  ()
  ([P (([n (Tm Nat)]) Ty)]
   [z (Tm (P Z))]
   [s (([n (Tm Nat)] [ih (Tm (P n))]) (Tm (P (S n))))])
  (Tm (= (P Z) (ind-Nat (Z : (Tm Nat)) ([x] (P x)) z ([n ih] (s n ih))) z)))
(destructor ind-Nat-S
  ()
  ([n (Tm Nat)])
  ([P (([n (Tm Nat)]) Ty)]
   [z (Tm (P Z))]
   [s (([n (Tm Nat)] [ih (Tm (P n))]) (Tm (P (S n))))])
  (Tm
    (= (P (S n))
      (ind-Nat ((S n) : (Tm Nat)) ([x] (P x)) z ([n ih] (s n ih)))
      (s n (ind-Nat n ([x] (P x)) z ([n ih] (s n ih)))))))

(constructor -> () ([D Ty] [C (([x (Tm D)]) Ty)]) Ty)
(constructor λ ([D Ty] [C (([x (Tm D)]) Ty)]) ([b (([x (Tm D)]) (Tm (C x)))]) (Tm (-> D ([x] (C x)))))
(destructor @
  ([D Ty] [C (([x (Tm D)]) Ty)])
  ([f (Tm (-> D ([x] (C x))))])
  ([a (Tm D)])
  (Tm (C a)))

(constructor Σ () ([A Ty] [B (([a (Tm A)]) Ty)]) Ty)
(constructor cons ([A Ty] [B (([a (Tm A)]) Ty)]) ([a (Tm A)] [b (Tm (B a))]) (Tm (Σ A ([x] (B x)))))
(destructor fst
  ([A Ty] [B (([a (Tm A)]) Ty)])
  ([p (Tm (Σ A ([x] (B x))))])
  ()
  (Tm A))
(destructor snd
  ([A Ty] [B (([a (Tm A)]) Ty)])
  ([p (Tm (Σ A ([x] (B x))))])
  ()
  (Tm (B (fst p))))

(let + : (Tm (-> Nat ([_] (-> Nat ([_] Nat)))))
  (λ ([a] (λ ([b]
    (ind-Nat a ([_] Nat)
      b
      ([a a+b] (S a+b))))))))

(let Z=Z : (Tm (= Nat Z Z))
  Refl)

(let nat-id : (Tm (-> Nat ([x] Nat)))
  (λ ([x] x)))

(let four : (Tm Nat)
  (S (S (S (S Z)))))

(let four-again : (Tm Nat)
  (@ nat-id four))

(let eight : (Tm Nat)
  (ind-Nat four
    ([n] Nat)
    Z
    ([n ih] (S (S ih)))))

(let eight-again : (Tm Nat)
  (@ (@ + four) four-again))

(let the-two : (Tm (Σ Nat ([n] (= Nat n (S (S Z))))))
  (cons (S (S Z)) Refl))
