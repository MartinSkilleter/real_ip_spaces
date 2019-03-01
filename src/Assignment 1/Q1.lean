namespace hidden
inductive Natural
| zero : Natural
| succ : Natural -> Natural

open Natural

instance : has_zero Natural :=
{ zero := zero }

instance : has_one Natural :=
{ one := succ zero}

def add : Natural -> Natural -> Natural
| a zero := a
| a (succ b) := succ (add a b).

instance : has_add Natural :=
{ add := add }

def times : Natural -> Natural -> Natural
| a zero := zero
| a (succ b) := add (times a b) a

instance : has_mul Natural :=
{ mul := times}

/- The 1st argument is the base and the 2nd argument is the exponent-/
def pow : Natural -> Natural -> Natural
| a zero := (succ zero)
| a (succ b) := times (pow a b) a

instance : has_pow Natural Natural :=
{ pow := pow}

theorem add_associativity (a b c : Natural) : (a + b) + c = a + (b + c) :=
Natural.rec_on c
(show (a + b) + 0 = a + (b + 0), from calc
      (a + b) + 0 = a + b : rfl
              ... = a + (b + 0) : rfl
)
(assume c, assume ih : (a + b) + c = a + (b + c),
 show (a + b) + (c + 1) = a + (b + (c + 1)), from calc
      (a + b) + (c + 1) = ((a + b) + c) + 1 : rfl
                    ... = (a + (b + c)) + 1 : by rw ih
                    ... = a + ((b + c) + 1) : rfl
                    ... = a + (b + (c + 1)) : rfl)

lemma zero_commutativity (a : Natural) : a + 0 = 0 + a :=
Natural.rec_on a
(show zero + 0 = 0 + zero, from rfl
)
(assume a, assume ih : a + 0 = 0 + a,
 show (a + 1) + 0 = 0 + (a + 1), from calc
      (a + 1) + 0 = a + 1 : rfl
              ... = (a + 0) +1 : rfl
              ... = (0 + a) + 1 : by rw ih
              ... = 0 + (a + 1) : rfl
)

/- lemma one_commutativity (a : Natural) : add a (succ zero) = add (succ zero) a :=
Natural.rec_on a
(show add (succ zero) zero = add zero (succ zero), from zero_commutativity)
(assume a, assume ih : add a (succ zero) = add (succ zero) a,
 show add (succ a) (succ zero) = add (succ zero) (succ a), from calc
      add (succ a) (succ zero) = succ (add (succ a) zero) : by rw add
                           ... = succ (succ a) : by rw add
                           ... = succ (succ (add a zero)) : by rw add
                           ... = succ (add a (succ zero)) : by rw add
                           ... = succ (add (succ zero) a) : by rw ih
                           ... = add (succ zero) (succ a) : by rw add

)
-/

theorem distributivity (a b c : Natural) : times a (add b c) = add (times a b) (times a c) :=
Natural.rec_on c
(show times a (add b zero) = add (times a b) (times a zero), from calc
      times a (add b zero) = times a b : by rw add
                       ... = add (times a b) zero : by rw add
                       ... = add (times a b) (times a zero) : by rw add
)
(assume c, assume ih : times a (add b c) = add (times a b) (times a c),
 show

)


theorem times_commutativity (a b : Natural) : times a b = times b a :=
sorry

theorem times_associativity (a b c : Natural) : times (times a b) c = times a (times b c) :=
sorry

end hidden