(def [>> : (-> (Action Unit) [B : (Type 0 lzero)] (Action B) (Action B))]
  (λ a B b
    (>>= Unit B a (λ _ b))))

(def [o-rule : (-> [dot-c : String] [dot-o : String] Rules)]
  (λ c o
    (*> o (sh "cc -c -o" (:: String o (:: String c (nil String)))))))

(def [main-rules : Rules]
  (++
    (*> "main"
      (>>
        (need "hello.o main.o")
        Unit
        (sh "cc -o main hello.o main.o" (nil String))))
    (++
      (o-rule "hello.c" "hello.o")
      (o-rule "main.c" "main.o"))))

(def [clean-rule : Rules]
  (*> "clean" (sh "rm -rf hello.o main.o main" (nil String))))

(make "main"
  (++ main-rules clean-rule))
