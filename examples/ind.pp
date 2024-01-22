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
  (ind-Code-Tag (lsucc (lsucc lzero))
    (λ _ (Type 0 (lsucc lzero)))
    Unit
    (Type 0 lzero)
    (Type 0 lzero)))

(def [Code-Arity : (-> [t : Code-Tag] (Code-Data t) (Type 0 lzero))]
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

(def [nil*-data : (-> Empty (El* nil))]
  (λ e (ind-Empty lzero e (El* nil))))

(def [El : (-> Code (Type 0 lzero))] El*)

(def [Flattened-El : (-> Code Code (Type 0 lzero))]
  (λ ind
    (ind-Code (lsucc lzero)
      (λ _ (Type 0 lzero))
      Unit
      (λ A children ih (Σ [a : A] (ih a)))
      (λ A child ih (Σ (-> A (El ind)) ih)))))

(def [mk-Flattened-El-Type : (-> Code Code (Type 0 lzero))]
  (λ ind
    (ind-Code (lsucc lzero)
       (λ _ (Type 0 lzero))
       (Flattened-El ind ind)
       (λ A children ih (-> [a : A] (ih a)))
       (λ A child ih (-> (-> A (El ind)) ih)))))

(def
  [mk-Flattened-El :
    (-> [ind : Code]
        (mk-Flattened-El-Type ind ind))]
  (λ ind
    ((ind-Code lzero
       (λ c
         (-> (-> (Flattened-El ind c) (Flattened-El ind ind))
             (mk-Flattened-El-Type ind c)))
       (λ k (k ()))
       (λ A children ih k (λ a (ih a (λ rest (k (cons a rest))))))
       (λ A child ih k (λ children (ih (λ rest (k (cons children rest)))))))
      ind (λ x x))))

(def [Nat*-Code : Code]
  (nonind Bool (λ b
    (ind-Bool (lsucc lzero) b
      (λ _ Code)
      nil
      (ind Unit nil)))))

;; TODO: This and z*-flat exposed a bug, fix it
(def [s*-flat : (-> (El Nat*-Code) (Flattened-El Nat*-Code Nat*-Code))]
  (λ n
    (mk-Flattened-El Nat*-Code false (λ _ n))))
