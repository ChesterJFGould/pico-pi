(def [mk-Person : (-> [firstN : String] [lastN : String] JSON)]
  (λ firstN lastN
    (Dict->JSON
      (dict-add Symbol JSON
        (dict-empty Symbol JSON)
        (String->Symbol "person")
        (Dict->JSON
          (dict-add Symbol JSON
            (dict-add Symbol JSON
              (dict-empty Symbol JSON)
              (String->Symbol "first")
              (String->JSON firstN))
            (String->Symbol "last")
            (String->JSON lastN)))))))

(List->JSON
  (:: JSON (mk-Person "Kiana" "Rashidi")
    (:: JSON (mk-Person "Chester" "Gould")
      (nil JSON))))
