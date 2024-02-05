(def [Or : (-> (Type 0 lzero) (Type 0 lzero) (Type 0 lzero))]
  (λ A B
    (Σ [t : Bool]
      (ind-Bool (lsucc lzero) t (λ _ (Type 0 lzero))
        A B))))

(def [inl : (-> [A : (Type 0 lzero)] [B : (Type 0 lzero)] [a : A] (Or A B))]
  (λ A B a (cons true a)))

(def [inr : (-> [A : (Type 0 lzero)] [B : (Type 0 lzero)] [b : B] (Or A B))]
  (λ A B b (cons false b)))

(def
  [ind-Or :
    (-> [l : (Level 0)]
        [A : (Type 0 lzero)]
        [B : (Type 0 lzero)]
        [m : (-> (Or A B) (Type 0 l))]
        [left : (-> [a : A] (m (inl A B a)))]
        [right : (-> [b : B] (m (inr A B b)))]
        [t : (Or A B)]
        (m t))]
  (λ l A B m left right t
    ((ind-Bool l (first t)
      (λ f
        (-> [s : (ind-Bool (lsucc lzero) f (λ _ (Type 0 lzero)) A B)]
            (m (cons f s))))
      left
      right) (second t))))

(def [Code-Tag : (Type 0 lzero)]
  (Or Bool Bool))

(def [Code-nil-tag : Code-Tag] (inl Bool Bool true))
(def [Code-nonind-tag : Code-Tag] (inl Bool Bool false))
(def [Code-ind-tag : Code-Tag] (inr Bool Bool true))
(def [Code-choice-tag : Code-Tag] (inr Bool Bool false))

(def
  [ind-Code-Tag :
    (-> [l : (Level 0)]
        [m : (-> Code-Tag (Type 0 l))]
        [nil : (m Code-nil-tag)]
        [nonind : (m Code-nonind-tag)]
        [ind : (m Code-ind-tag)]
        [choice : (m Code-choice-tag)]
        [t : Code-Tag]
        (m t))]
  (λ l m nil nonind ind choice
    (ind-Or l Bool Bool
      m
      (λ tag
        (ind-Bool l tag
          (λ tag (m (inl Bool Bool tag)))
          nil
          nonind))
      (λ tag
        (ind-Bool l tag
          (λ tag (m (inr Bool Bool tag)))
          ind
          choice)))))

(def [Code-Data : (-> Code-Tag (Type 0 (lsucc lzero)))]
  (ind-Code-Tag (lsucc (lsucc lzero)) (λ _ (Type 0 (lsucc lzero)))
    Unit
    (Type 0 lzero)
    (Type 0 lzero)
    Unit))
    
(def [Code-Arity : (-> [t : Code-Tag] (Code-Data t) (Type 0 lzero))]
  (ind-Code-Tag (lsucc lzero)
    (λ t (-> (Code-Data t) (Type 0 lzero)))
    (λ _ Empty)
    (λ A A)
    (λ _ Unit)
    (λ _ Bool)))

(def [Code* : (Type 0 (lsucc lzero))]
  (W [t : (Σ [t : Code-Tag] (Code-Data t))]
    (Code-Arity (first t) (second t))))

(def [Code-nil-data : (-> Empty Code*)]
  (λ e (ind-Empty (lsucc lzero) e Code*)))

(def [nil* : Code*]
  (w (cons Code-nil-tag ()) Code-nil-data))

(def [nonind* : (-> [A : (Type 0 lzero)] (-> A Code*) Code*)]
  (λ A children
    (w (cons Code-nonind-tag A) children)))

(def [ind* : (-> (Type 0 lzero) Code* Code*)]
  (λ A child
    (w (cons Code-ind-tag A) (λ _ child))))

(def [choice* : (-> Code* Code* Code*)]
  (λ l r
    (w (cons Code-choice-tag ())
      (λ b
        (ind-Bool (lsucc lzero) b
          (λ _ Code*)
          l
          r)))))

(def [Code*-Canonical : (-> Code* (Type 0 (lsucc lzero)))]
  (λ c
    (ind-W (lsucc (lsucc lzero)) c
      (λ _ (Type 0 (lsucc lzero)))
      (λ tag
        ((ind-Code-Tag (lsucc (lsucc lzero))
          (λ tag
            (-> [data : (Code-Data tag)]
                (-> (Code-Arity tag data) Code*)
                (-> (Code-Arity tag data) (Type 0 (lsucc lzero)))
                (Type 0 (lsucc lzero))))
            (λ _ data ih (= (-> Empty Code*) Code-nil-data data))
            (λ A data ih (-> [a : A] (ih a)))
            (λ A data ih (ih ()))
            (λ _ data ih
              (Σ
                [canon : (-> [b : Bool] (ih b))]
                (= (-> Bool Code*)
                  (λ b
                    (ind-Bool (lsucc lzero) b
                      (λ _ Code*)
                      (data true)
                      (data false)))
                  data)
                (= (-> [b : Bool] (ih b))
                  (λ b
                    (ind-Bool (lsucc lzero) b
                      (λ b (ih b))
                      (canon true)
                      (canon false)))
                  canon))))
          (first tag) (second tag))))))

(def [Code : (Type 0 (lsucc lzero))]
  (Σ [c : Code*] (Code*-Canonical c)))

(def [nil : Code]
  (cons nil* Refl))

(def [nonind : (-> [A : (Type 0 lzero)] (-> A Code) Code)]
  (λ A children
    (cons
      (nonind* A (λ a (first (children a))))
      (λ a (second (children a))))))

(def [ind : (-> (Type 0 lzero) Code Code)]
   (λ A child
     (cons (ind* A (first child)) (second child))))

(def [choice : (-> Code Code Code)]
  (λ l r
    (cons
      (choice* (first l) (first r))
      (cons
        (λ b
          (ind-Bool (lsucc lzero) b
            (λ b
              (Code*-Canonical
                (ind-Bool (lsucc lzero) b
                  (λ _ Code*)
                  (first l)
                  (first r))))
            (second l)
            (second r)))
        (cons
          Refl
          Refl)))))

(def
  [choice-lemma :
    (->
      [data : (-> Bool Code*)]
      [canon : (Code*-Canonical (w (cons Code-choice-tag ()) data))]
      (= Code
        (choice
          (cons (data true) ((first canon) true))
          (cons (data false) ((first canon) false)))
        (cons
          (w (cons Code-choice-tag ()) data)
          canon)))]
  (λ data canon
    ((ind-= (lsucc lzero) (first (second canon))
       (λ data^ prf
         (->
           [canon : (Code*-Canonical (w (cons Code-choice-tag ()) data^))]
           [data-eq : (= (-> Bool Code*) data data^)]
           (= Code
             (choice
               (cons (data^ true) ((first canon) true))
               (cons (data^ false) ((first canon) false)))
             (cons
               (w (cons Code-choice-tag ()) data^)
               (cons
                 (first canon)
                 (cons
                   (ind-= (lsucc lzero) data-eq
                     (λ data^^ _
                       (= (-> Bool Code*)
                         (λ b
                           (ind-Bool (lsucc lzero) b
                             (λ _ Code*)
                             (data^^ true)
                             (data^^ false)))
                         data^))
                     prf)
                   (second (second canon))))))))
       (λ canon data-eq
         (ind-= (lsucc lzero) data-eq
           (λ _ prf
             (= Code
               (choice
                 (cons (data true) ((first canon) true))
                 (cons (data false) ((first canon) false)))
               (cons
                 (w
                   (cons Code-choice-tag ())
                   (λ b
                     (ind-Bool (lsucc lzero) b
                       (λ _ Code*)
                       (data true)
                       (data false))))
                 (cons (first canon) (cons Refl (second (second canon)))))))
           ((ind-= (lsucc lzero) (second (second canon))
              (λ data-canon prf
                (->
                  [data-eq :
                    (=
                      (->
                        [b : Bool]
                        (Code*-Canonical
                          (ind-Bool (lsucc lzero) b
                            (λ _ Code*)
                            (data true)
                            (data false))))
                      (first canon)
                      data-canon)]
                  (= Code
                    (choice
                      (cons (data true) (data-canon true))
                      (cons (data false) (data-canon false)))
                    (cons
                      (w
                        (cons Code-choice-tag ())
                        (λ b
                          (ind-Bool (lsucc lzero) b
                            (λ _ Code*)
                            (data true)
                            (data false))))
                      (cons
                        data-canon
                        (cons
                          Refl
                          (ind-= (lsucc lzero) data-eq
                            (λ data-canon^ _
                              (=
                                (->
                                  [b : Bool]
                                  (Code*-Canonical
                                    (ind-Bool (lsucc lzero) b
                                      (λ _ Code*)
                                      (data true)
                                      (data false))))
                                (λ b
                                  (ind-Bool (lsucc lzero) b
                                    (λ b
                                      (Code*-Canonical
                                        (ind-Bool (lsucc lzero) b
                                          (λ _ Code*)
                                          (data true)
                                          (data false))))
                                    (data-canon^ true)
                                    (data-canon^ false)))
                                data-canon))
                            prf)))))))
              ;; One more ind-=?
              (λ data-eq Refl))
             Refl))))
      canon)))

#;
(def
  [ind-Code : 
    (-> [l : (Level 0)]
        [m : (-> Code (Type 0 l))]
        [nil : (m nil)]
        [nonind :
          (-> [A : (Type 0 lzero)]
              [children : (-> A Code)]
              (-> [a : A] (m (children a)))
              (m (nonind A children)))]
        [ind :
          (-> [A : (Type 0 lzero)]
              [child : Code]
              (m child)
              (m (ind A child)))]
        [choice :
          (->
            [l : Code]
            [r : Code]
            (m l)
            (m r)
            (m (choice l r)))]
        [t : Code]
        (m t))]
  (λ l m nil nonind ind choice t
    ((ind-W (lmax (lsucc lzero) l) (first t)
       (λ code* (-> [canon : (Code*-Canonical code*)] (m (cons code* canon))))
       (λ tag
         ((ind-Code-Tag (lmax (lsucc lzero) (lmax (lsucc lzero) (lmax (lsucc lzero) l)))
            (λ tag
              (-> [tag-data : (Code-Data tag)]
                  [data : (-> (Code-Arity tag tag-data) Code*)]
                  [ih :
                    (-> [i : (Code-Arity tag tag-data)]
                        [i-canon : (Code*-Canonical (data i))]
                        (m (cons (data i) i-canon)))]
                  [canon : (Code*-Canonical (w (cons tag tag-data) data))]
                  (m (cons (w (cons tag tag-data) data) canon))))
            (λ _ data ih canon
              (ind-= l canon
                (λ data canon (m (cons (w (cons Code-nil-tag ()) data) canon)))
                nil))
            (λ A data ih canon
              (nonind A
                (λ a (cons (data a) (canon a)))
                (λ a (ih a (canon a)))))
            (λ A data ih canon
              (ind A (cons (data ()) canon) (ih () canon)))
            (λ _ data ih canon
              (choice
                (cons (data true) (canon true))
                (cons (data false) (canon false))
                (ih true (canon true))
                (ih false (canon false)))))
           (first tag) (second tag))))
      (second t))))

#|
(def [El-Data : (-> Code (Type 0 lzero))]
  (ind-Code (lsucc lzero)
    (λ _ (Type 0 lzero))
    Unit
    (λ A children ih (Σ [a : A] (ih a)))
    (λ A child ih ih)))

(def [El-Arity : (-> [c : Code] (El-Data c) (Type 0 lzero))]
  (ind-Code (lsucc lzero)
    (λ c (-> (El-Data c) (Type 0 lzero)))
    (λ _ Empty)
    (λ A children ih data (ih (first data) (second data)))
    (λ A child ih data (Or A (ih data)))))

(def [El* : (-> Code (Type 0 lzero))]
  (λ c (W [data : (El-Data c)] (El-Arity c data))))

(def [Nat*-Code : Code]
  (nonind Bool (λ b
    (ind-Bool (lsucc lzero) b
      (λ _ Code)
      nil
      (ind Unit nil)))))

(def [nil*-data : (-> [c : Code] Empty (El* c))]
  (λ c e (ind-Empty lzero e (El* c))))

(def
  [El*-Canonical^ :
    (-> [ind : Code]
        [c : Code]
        [t : (El-Data c)]
        [d : (-> (El-Arity c t) (El* ind))]
        [ih : (-> (El-Arity c t) (Type 0 lzero))]
        (Type 0 lzero))]
  (λ ind
    (ind-Code (lsucc lzero)
      (λ c
        (-> [t : (El-Data c)]
            [d : (-> (El-Arity c t) (El* ind))]
            [ih : (-> (El-Arity c t) (Type 0 lzero))]
            (Type 0 lzero)))
        (λ t d ih (= (-> Empty (El* ind)) (nil*-data ind) d))
        (λ A children children-ih t
          (children-ih (first t) (second t)))
        (λ A child child-ih t d ih
          (Σ
            (-> [a : A] (ih (inl A (El-Arity child t) a)))
            (= (-> (Or A (El-Arity child t)) (El* ind))
              (ind-Or lzero A (El-Arity child t)
                (λ _ (El* ind))
                (λ a (d (inl A (El-Arity child t) a)))
                (λ i (d (inr A (El-Arity child t) i))))
              d)
            (child-ih t
              (λ i (d (inr A (El-Arity child t) i)))
              (λ i (ih (inr A (El-Arity child t) i)))))))))

(def [El*-Canonical : (-> [c : Code] (El* c) (Type 0 lzero))]
  (λ ind el
    (ind-W (lsucc lzero) el
      (λ el (Type 0 lzero))
      (El*-Canonical^ ind ind))))

(def
  [El*-Canonical^ :
    (-> [ind : Code]
        [c : Code]
        [tag : (El-Data c)]
        [data : (-> (El-Arity c tag) (El* ind))]
        (Type 0 lzero))]
  (λ ind c tag data
    (El*-Canonical^ ind c tag data
      (λ i (El*-Canonical ind (data i))))))

(def [El : (-> Code (Type 0 lzero))]
  (λ c (Σ [el* : (El* c)] (El*-Canonical c el*))))

#|
;; This is only being kept as it triggers the VChoice bug
(def [Flattened-El^ : (-> Code Code (Type 0 lzero))]
  (λ ind
    (ind-Code (lsucc lzero)
      (λ _ (Type 0 lzero))
      Unit
      (λ A children ih (Σ [a : A] (ih a)))
      (λ A child ih (Σ (-> A (El ind)) ih)))))

(def [Flattened-El : (-> Code (Type 0 lzero))]
  (λ c (Flattened-El^ c c)))

(def [mk-Flattened-El-Type^ : (-> Code Code (Type 0 lzero))]
  (λ ind
    (ind-Code (lsucc lzero)
       (λ _ (Type 0 lzero))
       (Flattened-El ind)
       (λ A children ih (-> [a : A] (ih a)))
       (λ A child ih (-> (-> A (El ind)) ih)))))

(def [mk-Flattened-El-Type : (-> Code (Type 0 lzero))]
  (λ c (mk-Flattened-El-Type^ c c)))

(def
  [mk-Flattened-El :
    (-> [ind : Code]
        (mk-Flattened-El-Type ind))]
  (λ ind
    ((ind-Code lzero
       (λ c
         (-> (-> (Flattened-El^ ind c) (Flattened-El ind))
             (mk-Flattened-El-Type^ ind c)))
       (λ k (k ()))
       (λ A children ih k (λ a (ih a (λ rest (k (cons a rest))))))
       (λ A child ih k (λ children (ih (λ rest (k (cons children rest)))))))
      ind (λ x x))))

(def [Flattened-El-Tag^ : (-> [ind : Code] [c : Code] (Flattened-El^ ind c) (El-Data c))]
  (λ ind
    (ind-Code lzero
      (λ c (-> (Flattened-El^ ind c) (El-Data c)))
      (λ _ ())
      (λ A children ih fe (cons (first fe) (ih (first fe) (second fe))))
      (λ A child ih fe (ih (second fe))))))

(def [Flattened-El-Tag : (-> [c : Code] (Flattened-El c) (El-Data c))]
  (λ c (Flattened-El-Tag^ c c)))

(def [Flattened-El-Data : (-> [c : Code] [fe : (Flattened-El c)] (-> (El-Arity c (Flattened-El-Tag c fe)) (El c)))]
  (λ ind
    ((ind-Code lzero
       (λ c (-> [fe : (Flattened-El^ ind c)] (-> (El-Arity c (Flattened-El-Tag^ ind c fe)) (El ind))))
       (λ fe (λ e (ind-Empty lzero e (El ind))))
       (λ A children ih fe (ih (first fe) (second fe)))
       (λ A child ih fe
         (ind-Or lzero A (El-Arity child (Flattened-El-Tag^ ind child (second fe)))
           (λ _ (El ind))
           (first fe)
           (ih (second fe)))))
      ind)))

(def [Nat*-Code : Code]
  (nonind Bool (λ b
    (ind-Bool (lsucc lzero) b
      (λ _ Code)
      nil
      (ind Unit nil)))))

(def [z*-flat : (Flattened-El Nat*-Code)]
  (mk-Flattened-El Nat*-Code true))

;; TODO: This and z*-flat cause the VChoice bug
(def [s*-flat : (-> (El Nat*-Code) (Flattened-El Nat*-Code))]
  (λ n
    (mk-Flattened-El Nat*-Code false (λ _ n))))
|#

(def
  [El*-Canonical-lemma :
    (-> [c : Code]
        [t : (El-Data c)]
        [d : (-> (El-Arity c t) (El* c))]
        (= (Type 0 lzero)
          (El*-Canonical^ c c t d)
          (El*-Canonical c (w t d))))]
  (λ c t d Refl))

(def [mk-El-Type^ : (-> Code Code (Type 0 lzero))]
  (λ ind
    (ind-Code (lsucc lzero)
      (λ _ (Type 0 lzero))
      (El ind)
      (λ A children ih (-> [a : A] (ih a)))
      (λ A child ih (-> (-> A (El ind)) ih)))))

(def [mk-El-Type : (-> Code (Type 0 lzero))]
  (λ c (mk-El-Type^ c c)))

(def
  [mk-El^ :
    (-> [ind : Code]
        [c : Code]
        [k :
          (-> [tag : (El-Data c)]
              [data : (-> (El-Arity c tag) (El* ind))]
              [canon : (El*-Canonical^ ind c tag data)]
              (El ind))]
        (mk-El-Type^ ind c))]
  (λ ind
    (ind-Code lzero
      (λ c
        (-> 
          (-> [tag : (El-Data c)]
              [data : (-> (El-Arity c tag) (El* ind))]
              [canon : (El*-Canonical^ ind c tag data)]
              (El ind))
          (mk-El-Type^ ind c)))
      (λ k (k () (nil*-data ind) Refl))
      (λ A children ih k a
        (ih a (λ tag (k (cons a tag)))))
      (λ A child ih k children
        (ih
          (λ tag data canon
            (k
              tag
              (ind-Or lzero A (El-Arity child tag)
                (λ _ (El* ind))
                (λ a (first (children a)))
                data)
              (cons
                (λ a (second (children a)))
                (cons
                   Refl
                   canon)))))))))

(def [mk-El : (-> [ind : Code] (mk-El-Type ind))]
  (λ ind
    (mk-El^ ind ind
      (λ tag data canon (cons (w tag data) canon)))))

(def
  [symm :
    (->
      [A : (Type 0 lzero)]
      [from : A]
      [to : A]
      (= A from to)
      (= A to from))]
  (λ A from to eq
    (ind-= lzero eq
      (λ to _ (= A to from))
      Refl)))

(def
  [app-mk-El^ :
    (-> [ind : Code]
        [c : Code]
        [tag : (El-Data c)]
        [data : (-> (El-Arity c tag) (El* ind))]
        [canon : (El*-Canonical^ ind c tag data)]
        (mk-El-Type^ ind c)
        (El ind))]
  (λ ind
    (ind-Code lzero
      (λ c
        (->
          [tag : (El-Data c)]
          [data : (-> (El-Arity c tag) (El* ind))]
          [canon : (El*-Canonical^ ind c tag data)]
          (mk-El-Type^ ind c)
          (El ind)))
      (λ tag data canon mk mk)
      (λ A children ih tag data canon mk
        (ih
          (first tag)
          (second tag)
          data
          canon
          (mk (first tag))))
      (λ A child ih tag data canon mk
        (ih
          tag
          (λ i (data (inr A (El-Arity child tag) i)))
          (second (second canon))
          (mk
            (λ a
              (cons
                (data (inl A (El-Arity child tag) a))
                ((first canon) a))
              #;
              (cons
                ((first (second canon)) a)
                (ind-= lzero
                  (symm
                    (-> (Or A (El-Arity child tag)) (El* ind))
                    (ind-Or lzero A (El-Arity child tag)
                      (λ _ (El* ind))
                      (first (second canon))
                      (λ i (data (inr A (El-Arity child tag) i))))
                    data
                    (first (second (second canon))))
                  (λ data _
                    (El*-Canonical ind (data (inl A (El-Arity child tag) a))))
                  ((first canon) a))))))))))

(def Code-ind ind)

(def
  [app-mk-El^-lemma :
    (-> [ind : Code]
        [tag : (El-Data ind)]
        [data : (-> (El-Arity ind tag) (El* ind))]
        [canon : (El*-Canonical ind (w tag data))]
        (= (El ind)
          (cons (w tag data) canon)
          (app-mk-El^ ind ind tag data canon (mk-El ind))))]
  (λ ind tag data canon
    ((ind-Code lzero
       (λ c
         (->
           [tag : (El-Data c)]
           [data : (-> (El-Arity c tag) (El* ind))]
           [canon : (El*-Canonical^ ind c tag data)]
           [k :
             (->
               [tag : (El-Data c)]
               [data : (-> (El-Arity c tag) (El* ind))]
               [canon : (El*-Canonical^ ind c tag data)]
               (El ind))]
           (= (El ind)
             (k tag data canon)
             (app-mk-El^ ind c tag data canon (mk-El^ ind c k)))))
       (λ tag data canon k
         (ind-= lzero canon
           (λ data canon
             (= (El ind)
               (k tag data canon)
               (app-mk-El^ ind nil tag data canon (mk-El^ ind nil k))))
             Refl))
       (λ A children ih tag data canon k
         (ih
           (first tag)
           (second tag)
           data
           canon
           (λ tag^ data canon (k (cons (first tag) tag^) data canon))))
       (λ A child ih tag data canon k
         ((ind-= lzero (first (second canon))
            (λ data^ prf
              (->
                [canon : (El*-Canonical^ ind (Code-ind A child) tag data^)]
                [data-eq :
                  (= (-> (Or A (El-Arity child tag)) (El* ind))
                    data
                    data^)]
                (= (El ind)
                  (k tag data^
                    (cons (first canon)
                      (cons
                        (ind-= lzero data-eq
                          (λ data^^ _
                            (= (-> (Or A (El-Arity child tag)) (El* ind))
                              (ind-Or lzero A (El-Arity child tag)
                                (λ _ (El* ind))
                                (λ a (data^^ (inl A (El-Arity child tag) a)))
                                (λ i (data^^ (inr A (El-Arity child tag) i))))
                              data^))
                          prf)
                          (second (second canon)))))
                  (app-mk-El^
                    ind
                    child
                    tag
                    (λ i (data^ (inr A (El-Arity child tag) i)))
                    (second (second canon))
                    #;
                    (cons (first canon)
                      (cons
                        (ind-= lzero data-eq
                          (λ data^^ _
                            (= (-> (Or A (El-Arity child tag)) (El* ind))
                              (ind-Or lzero A (El-Arity child tag)
                                (λ _ (El* ind))
                                (λ a (data^^ (inl A (El-Arity child tag) a)))
                                (λ i (data^^ (inr A (El-Arity child tag) i))))
                              data^))
                          prf)
                          (second (second canon))))
                     (mk-El^ ind child
                       (λ tag^ data^^ canon^
                         (k
                           tag^
                           (ind-Or lzero A (El-Arity child tag^)
                             (λ _ (El* ind))
                             (λ a (data^ (inl A (El-Arity child tag) a)))
                             data^^)
                           (cons
                             (first canon)
                             (cons
                               (ind-= lzero data-eq
                                 (λ data^^^ _
                                   (= (-> (Or A (El-Arity child tag^)) (El* ind))
                                     (ind-Or lzero A (El-Arity child tag^)
                                       (λ _ (El* ind))
                                       (λ a (data^^^ (inl A (El-Arity child tag) a)))
                                       data^^)
                                     (ind-Or lzero A (El-Arity child tag^)
                                       (λ _ (El* ind))
                                       (λ a (data^^^ (inl A (El-Arity child tag) a)))
                                       data^^)))
                                 Refl)
                               canon^)))))
                     #;
                    (mk-El^ ind (Code-ind A child) k)))))
            (λ canon data-eq
              (ih
                tag
                (λ i (data (inr A (El-Arity child tag) i)))
                (second (second canon))
                (λ tag^ data^ canon^
                  (k
                    tag^
                    (ind-Or lzero A (El-Arity child tag^)
                      (λ _ (El* ind))
                      (λ a (data (inl A (El-Arity child tag) a)))
                      data^)
                    (cons
                      (first canon)
                      (cons
                        (ind-= lzero data-eq
                          (λ data^^ _
                            (= (-> (Or A (El-Arity child tag^)) (El* ind))
                              (ind-Or lzero A (El-Arity child tag^)
                                (λ _ (El* ind))
                                (λ a (data^^ (inl A (El-Arity child tag) a)))
                                data^)
                              (ind-Or lzero A (El-Arity child tag^)
                                (λ _ (El* ind))
                                (λ a (data^^ (inl A (El-Arity child tag) a)))
                                data^)))
                          Refl)
                        canon^)))))))
           canon Refl)))
      ind tag data canon (λ tag data canon (cons (w tag data) canon)))))

(def
  [ind-El-case-Type^ :
    (-> [l : (Level 0)]
        [ind : Code]
        [c : Code]
        [m : (-> (El ind) (Type 0 l))]
        [k : (mk-El-Type^ ind c)]
        (Type 0 l))]
  (λ l ind c m k
    ((ind-Code (lsucc l)
       (λ c
         (-> [m : (-> (El ind) (Type 0 l))]
             [k : (mk-El-Type^ ind c)]
             (Type 0 l)))
       (λ m k (m k))
       (λ A children ih m k
         (-> [a : A] (ih a m (k a))))
       (λ A child ih m k 
         (-> [d : (-> A (El ind))]
             (-> [a : A] (m (d a)))
             (ih m (k d)))))
      c m k)))

(def
  [ind-El-case-Type :
    (-> [l : (Level 0)]
        [ind : Code]
        [m : (-> (El ind) (Type 0 l))]
        (Type 0 l))]
  (λ l ind m (ind-El-case-Type^ l ind ind m (mk-El ind))))

(def
  [ind-El :
    (-> [ind : Code]
        [l : (Level 0)]
        [m : (-> (El ind) (Type 0 l))]
        (ind-El-case-Type l ind m)
        [t : (El ind)]
        (m t))]
  (λ ind l m ind-case t
    ((ind-W l (first t)
       (λ el*
         (-> [el*-canon : (El*-Canonical ind el*)]
             (ind-El-case-Type l ind m)
             (m (cons el* el*-canon))))
       (λ ind-tag ind-data ind-ih ind-canon case
         (ind-= l
           (symm
             (El ind)
             (cons (w ind-tag ind-data) ind-canon)
             (app-mk-El^ ind ind ind-tag ind-data ind-canon (mk-El ind))
             (app-mk-El^-lemma ind ind-tag ind-data ind-canon))
           (λ res _ (m res))
           ((ind-Code l
              (λ c
                (-> [k : (mk-El-Type^ ind c)]
                    [tag : (El-Data c)]
                    [data : (-> (El-Arity c tag) (El* ind))]
                    [ih :
                      (-> [a : (El-Arity c tag)]
                          [a-canon : (El*-Canonical ind (data a))]
                          (ind-El-case-Type l ind m)
                          (m (cons (data a) a-canon)))]
                    [el*-canon : (El*-Canonical^ ind c tag data)]
                    [case : (ind-El-case-Type^ l ind c m k)]
                    (m (app-mk-El^ ind c tag data el*-canon k))))
              (λ k tag data ih canon case case)
              (λ A children children-ih k tag data ih canon case
                (children-ih
                  (first tag)
                  (k (first tag))
                  (second tag)
                  data
                  ih
                  canon
                  (case (first tag))))
              (λ A child child-ih k tag data ih canon case
                (child-ih
                  (k
                    (λ a
                      (cons
                        (data (inl A (El-Arity child tag) a))
                        ((first canon) a))))
                  tag
                  (λ i (data (inr A (El-Arity child tag) i)))
                  (λ i (ih (inr A (El-Arity child tag) i)))
                  (second (second canon))
                  (case
                    (λ a
                      (cons
                        (data (inl A (El-Arity child tag) a))
                        ((first canon) a)))
                    (λ a
                      (ih
                        (inl A (El-Arity child tag) a)
                        ((first canon) a)
                        ind-case)))
                  )))
             ind (mk-El ind) ind-tag ind-data ind-ih ind-canon case))))
      (second t) ind-case)))


#|
data Nat = Z | Succ (Unit -> Nat)
|#

(def [Nat-Code : Code]
  (nonind Bool (λ b
    (ind-Bool (lsucc lzero) b
      (λ _ Code)
      nil
      (ind Unit nil)))))

(def [Nat : (Type 0 lzero)] (El Nat-Code))

(def [zero : Nat]
  (mk-El Nat-Code true))

(def [add1 : (-> Nat Nat)]
  (λ n (mk-El Nat-Code false (λ _ n))))

(def [four : Nat] (add1 (add1 (add1 (add1 zero)))))

;; Commuting conversions LOL
#;
(def
  [Nat-case-Type-lemma :
    (->
      [l : (Level 0)]
      [m : (-> (El c) (Type 0 l))]
      (= (Type 0 l)
        (ind-El-case-Type l c m)
        (->
          [b : Bool]
          (m
            (ind-Bool lzero b
              (λ b (El c))
              (mk-El c true)
              (mk-El c false))))))]
  (λ l m Refl))

#;
(def
  [ind-Nat :
    (->
      [l : (Level 0)]
      [m : (-> Nat (Type 0 l))]
      [z-case : (m zero)]
      [s-case : (-> [n : Nat] [ih : (m n)] (m (add1 n)))]
      [n : Nat]
      (m n))]
  (λ l m z-case s-case
    (ind-El Nat-Code l
      m
      (λ b
        (ind-Bool l b
          (λ b
            (ind-Bool (lsucc l) b
              (λ _ (Type 0 l))
              (m zero)
              (->
                [n : (-> Unit Nat)]
                [ih : (-> Unit (m (n ())))]
                (m (add1 (n ()))))))
          z-case
          (λ n ih (s-case (n ()) (ih ()))))))))


#;
(ind-El Nat-Code lzero
  (λ _ Nat)
  (λ b
    (ind-Bool lzero b
      (λ b
        (ind-Bool (lsucc lzero) b
          (λ _ (Type 0 lzero))
          Nat
          (->
            [n : (-> Unit Nat)]
            [ih : (-> Unit Nat)]
            Nat)))
      zero
      (λ n ih (add1 (ih ()))))))
|#
