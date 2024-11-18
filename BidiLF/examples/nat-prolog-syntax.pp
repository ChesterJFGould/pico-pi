kind(Ty, ())
kind(Tm, (t[] : Ty()))

constructor(Nat, (), (), Ty())
constructor(Z, (), (), Tm(Nat()))
constructor(S, (), (n[] : Tm(Nat())), Tm(Nat()))
destructor(ind-Nat,
  (),
  (n[] : Tm(Nat())),
  (P[n : Tm(Nat)] : Ty, z[] : P[Z], s[n : Tm(Nat), ih : P[n]] : P[S(n)])
)

let(two : Tm(Nat), S(S(Z)))
let(four : Tm(Nat),
  ind-Nat(two
    , ([n] Tm(Nat)),
    , Z
    , ([n, ih] S(S(ih))))
)
