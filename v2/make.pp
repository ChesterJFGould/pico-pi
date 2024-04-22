(def [>> : (-> (Action Unit) [B : (Type 0 lzero)] (Action B) (Action B))]
  (λ a B b
    (>>= Unit B a (λ _ b))))

(make "main"
  (++
    (*> "main"
      (>>= String Unit
        (file-contents "rules") (λ rules
          (>>
            (need rules)
            Unit
            (sh "echo" (:: String "there" (nil String)))))))
    (*> "hello"
      (sh "echo" (:: String "hello" (nil String))))))
