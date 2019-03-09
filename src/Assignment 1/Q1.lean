namespace hidden
inductive Natural
 | zero : Natural
 | succ : Natural -> Natural

open Natural

instance : has_zero Natural :=
{ zero := zero}

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
                    ... = a + (b + (c + 1)) : rfl
)

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

lemma one_commutativity (a : Natural) : a + 1 = 1 + a :=
Natural.rec_on a
(show (0 + 1 : Natural) = 1 + 0, by rw zero_commutativity)
(assume a, assume ih : a + 1 = 1 + a,
 show (a + 1) + 1 = 1 + (a + 1), from calc
      (a + 1) + 1 = (1 + a) + 1 : by rw ih
              ... = 1 + (a + 1) : rfl
)

theorem add_commutativity (a b : Natural) : a + b = b + a :=
Natural.rec_on b
(show (a + 0 : Natural) = 0 + a, by rw zero_commutativity)
(assume b, assume ih : a + b = b + a,
 show a + (b + 1) = (b + 1) + a, from calc
      a + (b + 1) = (a + b) + 1 : by rw add_associativity
              ... = (b + a) + 1 : by rw ih
              ... = b + (a + 1) : by rw add_associativity
              ... = b + (1 + a) : by rw one_commutativity
              ... = (b + 1) + a : by rw add_associativity
)

-- Question 1a
theorem left_distributivity (a b c : Natural) : a * (b + c) = a * b + a * c :=
Natural.rec_on c
(show a * (b + 0) = a * b + a * 0, from calc
      a * (b + 0) = a * b : rfl
              ... = a * b + 0 : rfl
              ... = a * b + a * 0 : rfl
)
(assume c, assume ih : a * (b + c) = a * b + a * c,
 show a * (b + (c + 1)) = a * b + a * (c + 1), from calc
      a * (b + (c + 1)) = a * ((b + c) + 1) : by rw add_associativity
                    ... = a * (b + c) + a : rfl
                    ... = (a * b + a * c) + a : by rw ih
                    ... = a * b + (a * c + a) : by rw add_associativity
                    ... = a * b + a * (c + 1) : rfl
)

lemma times_zero (a : Natural) : 0 * a = 0 :=
Natural.rec_on a
(show (0 * 0 : Natural) = 0, by refl)
(assume a, assume ih : 0 * a = 0,
 show 0 * (a + 1) = 0, from calc
      0 * (a + 1) = 0 * a + 0 * 1 : by rw left_distributivity
              ... = 0 + 0 * 1 : by rw ih
              ... = 0 + 0 : rfl
              ... = 0 : rfl
)

theorem right_distributivity (a b c : Natural) : (a + b) * c = a * c + b * c :=
Natural.rec_on c
(show (a + b) * 0 = a * 0 + b * 0, by refl)
(assume c, assume ih : (a + b) * c = a * c + b * c,
 show (a + b) * (c + 1) = a * (c + 1) + b * (c + 1), from calc
      (a + b) * (c + 1) = ((a + b) * c) + (a + b) : rfl
                    ... = (a * c + b * c) + (a + b) : by rw ih
                    ... = ((a * c + b * c) + a) + b : by rw ← add_associativity
                    ... = (a * c + (b * c + a)) + b : by rw ← add_associativity
                    ... = (a * c + (a + b * c)) + b : by rw add_commutativity (b * c)
                    ... = ((a * c + a) + b * c) + b : by rw ← add_associativity
                    ... = (a * c + a) + (b * c + b) : by rw ← add_associativity
                    ... = a * (c + 1) + b * (c + 1) : by refl
)

lemma right_times_one (a : Natural) : a * 1 = a :=
(show a * 1 = a, from calc
      a * 1 = a * 0 + a : rfl
        ... = 0 + a : rfl
        ... = a + 0 : by rw add_commutativity
        ... = a : rfl
)

lemma left_times_one (a : Natural) : 1 * a = a :=
Natural.rec_on a
(show (1 * 0 : Natural) = 0, by refl)
(assume a, assume ih : 1 * a = a, 
 show 1 * (a + 1) = a + 1, from calc
      1 * (a + 1) = 1 * a + 1 : rfl
             ...  = a + 1 : by rw ih
)

-- Question 1b
theorem times_commutativity (a b : Natural) : a * b = b * a :=
Natural.rec_on b
(show a * 0 = 0 * a, from calc
      a * 0 = 0 : rfl
        ... = 0 * a : by rw times_zero
)
(assume b, assume ih : a * b = b * a,
 show a * (b + 1) = (b + 1) * a, from calc
      a * (b + 1) = a * b + a : rfl
              ... = b * a + a : by rw ih
              ... = a + b * a : by rw add_commutativity
              ... = 1 * a + b * a : by rw left_times_one
              ... = (1 + b) * a : by rw right_distributivity
              ... = (b + 1) * a : by rw add_commutativity
)

-- Question 1c
theorem times_associativity (a b c : Natural) : (a * b) * c = a * (b * c) :=
Natural.rec_on c
(show (a * b) * 0 = a * (b * 0), from calc
      (a * b) * 0 = 0 : rfl
              ... = a * 0 : rfl
              ... = a * (b * 0) : rfl
)
(assume c, assume ih : (a * b) * c = a * (b * c),
 show (a * b) * (c + 1) = a * (b * (c + 1)), from calc
      (a * b) * (c + 1) = (a * b) * c + a * b : rfl
                    ... = a * (b * c) + a * b : by rw ih
                    ... = a * ((b * c) + b) : by rw left_distributivity
                    ... = a * (b * (c + 1)) : rfl
)

end hidden