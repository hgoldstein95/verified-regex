Parameter char : Type.
Parameter dec_eq_char : forall x y : char, {x = y} + {x <> y}.
Definition t := list char.