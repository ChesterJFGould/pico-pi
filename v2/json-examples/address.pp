(def [Maybe : (-> (Type 0 lzero) (Type 0 lzero))]
  (λ X (Σ [t : Bool] (ind-Bool (lsucc lzero) t (λ _ (Type 0 lzero)) X Unit))))

(def [None : (-> [X : (Type 0 lzero)] (Maybe X))]
  (λ _ (cons false ())))

(def [Some : (-> [X : (Type 0 lzero)] X (Maybe X))]
  (λ _ x (cons true x)))

(def [not : (-> Bool Bool)]
  (λ b
    (ind-Bool lzero b
      (λ _ Bool)
      false
      true)))

(def [some? : (-> [X : (Type 0 lzero)] (Maybe X) Bool)]
  (λ X m (first m)))

(def [none? : (-> [X : (Type 0 lzero)] (Maybe X) Bool)]
  (λ X m (not (first m))))

(def [and : (-> Bool Bool Bool)]
  (λ a b
    (ind-Bool lzero a
      (λ _ Bool)
      b
      false)))

(def [=> : (-> Bool Bool Bool)]
  (λ a b
    (ind-Bool lzero a
      (λ _ Bool)
      b
      true)))

(def [AddressData : (Type 0 lzero)]
  (Rec
    [postOfficeBox (Maybe String)]
    [extendedAddress (Maybe String)]
    [streetAddress (Maybe String)]
    [locality String]
    [region String]
    [postalCode (Maybe String)]
    [countryName String]))

(def [AddressValid : (-> AddressData (Type 0 lzero))]
  (λ a
    (So
      (and
        (=> (some? String (! a postOfficeBox)) (some? String (! a streetAddress)))
        (=> (some? String (! a extendedAddress)) (some? String (! a streetAddress)))))))

(def [Address : (Type 0 lzero)]
  (SuchThat AddressData AddressValid))

((An AddressData AddressValid
   (rec
     [postOfficeBox (Some String "123")]
     [extendedAddress (None String)]
     [streetAddress (Some String "456 Main St")]
     [locality "Cityville"]
     [region "State"]
     [postalCode (Some String "12345")]
     [countryName "Country"])
   Oh)
 : Address)
