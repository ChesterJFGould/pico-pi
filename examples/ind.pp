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
  (Or Bool Unit))

(def [Code-nil-tag : Code-Tag] (inl Bool Unit true))
(def [Code-nonind-tag : Code-Tag] (inl Bool Unit false))
(def [Code-ind-tag : Code-Tag] (inr Bool Unit ()))

(def
  [ind-Code-Tag :
    (-> [l : (Level 0)]
        [m : (-> Code-Tag (Type 0 l))]
        [nil : (m Code-nil-tag)]
        [nonind : (m Code-nonind-tag)]
        [ind : (m Code-ind-tag)]
        [t : Code-Tag]
        (m t))]
  (λ l m nil nonind ind
    (ind-Or l Bool Unit
      m
      (λ tag
        (ind-Bool l tag
          (λ tag (m (inl Bool Unit tag)))
          nil
          nonind))
      (λ _ ind))))

(def [Code-Data : (-> Code-Tag (Type 0 (lsucc lzero)))]
  (ind-Code-Tag (lsucc (lsucc lzero)) (λ _ (Type 0 (lsucc lzero)))
    Unit
    (Type 0 lzero)
    (Type 0 lzero))) (def [Code-Arity : (-> [t : Code-Tag] (Code-Data t) (Type 0 lzero))]
  (ind-Code-Tag (lsucc lzero)
    (λ t (-> (Code-Data t) (Type 0 lzero)))
    (λ _ Empty)
    (λ A A)
    (λ _ Unit)))

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
            (λ A data ih (ih ())))
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
        [t : Code]
        (m t))]
  (λ l m nil nonind ind t
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
              (ind A (cons (data ()) canon) (ih () canon))))
           (first tag) (second tag))))
      (second t))))

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
            (child-ih t
              (λ i (d (inr A (El-Arity child t) i)))
              (λ i (ih (inr A (El-Arity child t) i)))))))))

(def [El*-Canonical : (-> [c : Code] (El* c) (Type 0 lzero))]
  (λ ind el
    (ind-W (lsucc lzero) el
      (λ el (Type 0 lzero))
      (El*-Canonical^ ind ind))))

#;
(def [El*-Canonical : (-> [c : Code] (El* c) (Type 0 lzero))]
  (λ ind el
    (ind-W (lsucc lzero) el
      (λ el (Type 0 lzero))
      ((ind-Code (lsucc lzero)
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
             (child-ih t
               (λ i (d (inr A (El-Arity child t) i)))
               (λ i (ih (inr A (El-Arity child t) i)))))))
        ind))))

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
  [El*-Canonical-lemma :
    (-> [c : Code]
        [t : (El-Data c)]
        [d : (-> (El-Arity c t) (El* c))]
        (= (Type 0 lzero)
          (El*-Canonical^ c c t d (λ i (El*-Canonical c (d i))))
          (El*-Canonical c (w t d))))]
  (λ c t d Refl))

(def
  [mk-El^ :
    (-> [ind : Code]
        [c : Code]
        [k :
          (-> [tag : (El-Data c)]
              [data : (-> (El-Arity c tag) (El* ind))]
              [canon :
                (El*-Canonical^ ind c tag data
                  (λ i (El*-Canonical ind (data i))))]
              (El ind))]
        (mk-El-Type^ ind c))]

(def [mk-El : (-> [c : Code] (mk-El-Type c))]
  (λ ind
    ((ind-Code lzero
       (λ c
         (->
           (->
             (Σ
               [t : (El-Data c)]
               [d : (-> (El-Arity c t) (El* ind))]
               (El*-Canonical^ ind c t d (λ i (El*-Canonical ind (d i)))))
             (El ind))
           (mk-El-Type^ ind c)))
       (λ k (k (cons () (cons (nil*-data ind) Refl))))
       (λ A children ih k
         (λ a (ih a (λ f (k (cons (cons a (first f)) (cons (first (second f)) (second (second f)))))))))
       (λ A child ih k
         (λ children
           (ih
             (λ f
               (k
                 (cons (first f)
                   (cons
                     (ind-Or lzero A (El-Arity child (first f))
                       (λ I (El* ind))
                       (λ i (first (children i)))
                       (first (second f)))
                     (cons
                       (λ i (second (children i)))
                       (second (second f)))))))))))
      ind (λ f (cons (w (first f) (first (second f))) (second (second f)))))))

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
  [app-mk-El :
    (-> [ind : Code]
        [c : Code]
        [k : (mk-El-Type^ ind c)]
        [tag : (El-Data c)]
        [data : (-> (El-Arity c tag) (El* ind))]
        [canon :
          (El*-Canonical^ ind c tag data
            (λ i (El*-Canonical ind (data i))))]
        (El ind))]
  (λ ind
    (ind-Code lzero
      (λ c
        (-> [k : (mk-El-Type^ ind c)]
            [tag : (El-Data c)]
            [data : (-> (El-Arity c tag) (El* ind))]
            [canon :
              (El*-Canonical^ ind c tag data
                (λ i (El*-Canonical ind (data i))))]
            (El ind)))
      (λ k tag data canon k)
      (λ A children ih k tag data canon
        (ih
          (first tag)
          (k (first tag))
          (second tag)
          data 
          canon))
      (λ A child ih k tag data canon
        (ih
          (k (λ i (cons (data (inl A (El-Arity child tag) i)) ((first canon) i))))
          tag
          (λ i (data (inr A (El-Arity child tag) i)))
          (second canon))))))

(def
  [app-mk-El-lemma :
    (-> [ind : Code]
        [tag : (El-Data ind)]
        [data : (-> (El-Arity ind tag) (El* ind))]
        [canon : (El*-Canonical ind (w tag data))]
        (= (El ind)
          (cons (w tag data) canon)
          (app-mk-El ind ind (mk-El ind) tag data canon)))]
  (λ ind
    (ind-Code lzero
      (λ c
        (-> [tag : (El-Data c)]
            [data : (-> (El-Arity c tag) (El* ind))]
            [canon :
              (El*-Canonical^ ind c tag data
                (λ i (El*-Canonical ind (data i))))]
            (= (El ind)

#;
(def
  [ind-El :
    (-> [ind : Code]
        [l : (Level 0)]
        [m : (-> (El ind) (Type 0 l))]
        (ind-El-case-Type l ind m)
        [t : (El ind)]
        (m t))]
  (λ ind l m case t
    ((ind-W l (first t)
       (λ el*
         (-> [el*-canon : (El*-Canonical ind el*)]
             (ind-El-case-Type l ind m)
             (m (cons el* el*-canon))))
       (λ ind-tag ind-data ind-ih ind-canon
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
                  [el*-canon :
                    (El*-Canonical^ ind c tag data
                      (λ i (El*-Canonical ind (data i))))]
                  [case : (ind-El-case-Type^ l ind c m k)]
                  (m (cons (w ind-tag ind-data) ind-canon))))
            (λ k tag data ih canon case ?)
            ?
            ?)
           ? ind-tag ind-data ind-ih ind-canon)))
      (second t) case)))


#|
data Nat = Z | Succ (Unit -> Nat)
|#

#|
(def [Nat-Code : Code]
  (nonind Bool (λ b
    (ind-Bool (lsucc lzero) b
      (λ _ Code)
      nil
      (ind Unit nil)))))

(def [Nat : (Type 0 lzero)] (El Nat-Code))

(def [z : Nat]
  (mk-El Nat-Code true))

(def [s : (-> Nat Nat)]
  (λ n (mk-El Nat-Code false (λ _ n))))

(def [four : Nat] (s (s (s (s z)))))
|#
