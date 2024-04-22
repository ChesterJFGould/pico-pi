(def [Person : (Type 0 lzero)]
  (Rec [name String] [age Nat]))

(def [mk-Person : (-> String Nat Person)]
  (λ name age (rec [name name] [age age])))

(def [ThreeYearOld : (Type 0 lzero)]
  (Σ [p : Person] (= Nat (! p age) (add1 (add1 (add1 zero))))))

(:: ThreeYearOld
  (cons (mk-Person "Chester Gould" (add1 (add1 (add1 zero)))) Refl)
  (:: ThreeYearOld (cons (mk-Person "Kiana Rashidi" (add1 (add1 zero))) Refl)
    (nil ThreeYearOld)))
