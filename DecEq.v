Class DecEq (T : Type) :=
  {
    dec_eq : forall x y : T, {x = y} + {x <> y} ;
  }.
