(sort Ty ())
(sort Tm ([t Ty]))
(sort = ([A Ty] [a (Tm A)] [b (Tm A)]))

(constructor Refl ([A Ty] [a (Tm A)]) () (= A a a))

(constructor Unit () () Ty)
(constructor unit () () (Tm Unit))
(constructor Unit-eq ([u (Tm Unit)] [v (Tm Unit)]) () (= Unit u v))

(constructor * () ([A Ty] [B Ty]) Ty)
(constructor cons ([A Ty] [B Ty]) ([a (Tm A)] [b (Tm B)]) (Tm (* A B)))
(destructor fst ([A Ty] [B Ty]) ([p (Tm (* A B))]) () (Tm A))
(destructor snd ([A Ty] [B Ty]) ([p (Tm (* A B))]) () (Tm B))
(constructor *-fst-eq ([A Ty] [B Ty] [a (Tm A)] [b (Tm B)]) () (= A (fst ((cons a b) : (Tm (* A B)))) a))
(constructor *-snd-eq ([A Ty] [B Ty] [a (Tm A)] [b (Tm B)]) () (= B (snd ((cons a b) : (Tm (* A B)))) b))

(constructor Eq () ([A Ty] [B Ty] [f (([a (Tm A)]) (Tm B))] [g (([a (Tm A)]) (Tm B))]) Ty)
(constructor eq ([A Ty] [B Ty] [f (([a (Tm A)]) (Tm B))] [g (([a (Tm A)]) (Tm B))]) ([a (Tm A)] [prf (= B (f a) (g a))]) (Tm (Eq A B ([a] (f a)) ([a] (g a)))))
(destructor Eq-val ([A Ty] [B Ty] [f (([a (Tm A)]) (Tm B))] [g (([a (Tm A)]) (Tm B))]) ([e (Tm (Eq A B ([a] (f a)) ([a] (g a))))]) () (Tm A))
(destructor Eq-prf ([A Ty] [B Ty] [f (([a (Tm A)]) (Tm B))] [g (([a (Tm A)]) (Tm B))]) ([e (Tm (Eq A B ([a] (f a)) ([a] (g a))))]) () (= B (f (Eq-val e)) (g (Eq-val e))))

(constructor -> () ([D Ty] [C Ty]) Ty)
(constructor λ ([D Ty] [C Ty]) ([f (([x (Tm D)]) (Tm C))]) (Tm (-> D C)))
(destructor @ ([D Ty] [C Ty]) ([f (Tm (-> D C))]) ([a (Tm D)]) (Tm C))

(constructor Ω () () Ty)
(constructor true () () (Tm Ω))
(destructor prop ([X Ty]) ([x (Tm X)]) ([U Ty] [f (([u (Tm U)]) (Tm X))] [mono (([u (Tm U)] [v (Tm U)] [fu=fv (= X (f u) (f v))]) (= U u v))]) (Tm Ω))
(destructor proof ([U Ty]) ([u (Tm U)]) ([X Ty] [f (([u (Tm U)]) (Tm X))] [mono (([u (Tm U)] [v (Tm U)] [fu=fv (= X (f u) (f v))]) (= U u v))]) (= Ω (prop (f u) U ([u] (f u)) ([u v p] (mono u v p))) true))

(constructor N () () Ty)
(constructor Z () () (Tm N))
(constructor S () ([n (Tm N)]) (Tm N))
(destructor ind-N () ([n (Tm N)] [X Ty]) ([z (Tm X)] [s (([x (Tm X)]) (Tm X))]) (Tm X))
(constructor ind-N-Z ([X Ty] [z (Tm X)] [s (([x (Tm X)]) (Tm X))]) () (= X (ind-N (Z : (Tm N)) X z ([x] (s x))) z))

(let eq-z : (Tm Ω)
  (prop (Z : (Tm N)) Unit ([u] Z) ([u v p] Unit-eq)))

(let z-eq-z : (= Ω (prop (Z : (Tm N)) Unit ([u] Z) ([u v p] Unit-eq)) true)
  (proof (unit : (Tm Unit)) N ([u] Z) ([u v p] Unit-eq)))
