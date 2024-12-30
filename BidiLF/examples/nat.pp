(sort N ())

(constructor Z () () N)
(constructor S () ([n N]) N)

(sort + ([a N] [b N] [c N]))

(constructor +-Z ([b N]) () (+ Z b b))
(constructor +-S ([a N] [b N] [c N]) ([+-a (+ a b c)]) (+ (S a) b (S c)))

(let oneTwoThree : (+ (S Z) (S (S Z)) (S (S (S Z))))
  (+-S +-Z))
