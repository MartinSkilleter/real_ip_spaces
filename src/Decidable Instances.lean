import tactic.norm_num

instance qux : decidable (2 ∣ 4) :=
begin
    apply decidable.is_true,
    norm_num,
end

example : decidable (2 ∣ 4) :=
begin
    apply decidable.is_true,
    dsimp [(∣)],
    refine ⟨2, _⟩,
    refl,
end

instance : decidable (2 ∣ 5) :=
begin
    apply decidable.is_false,
    norm_num,
end

def even (n : ℕ) := 2 ∣ n

def even' (n : ℕ) := n % 2 = 0

instance even'.decidable_pred : decidable_pred even' :=
λ n,
begin
    dsimp [even'],
    apply_instance,
end

lemma even_iff_even' (n : ℕ) : even n ↔ even' n :=
begin
    split,
    intros h,
    dsimp [even] at h,
    dsimp [(∣)] at h,
    sorry,
    sorry,
end

/- instance : decidable_pred even :=
λ n,
begin
    rw even_iff_even',
    apply_instance,
end -/

lemma foo (n : ℕ) (h : ¬2 ∣ n) : 2 ∣ n + 1 := sorry,

instance : decidable_pred even :=
λ n,
begin
    dsimp [even],
    induction n with n ih,
    { apply decidable.is_true,
      norm_num,
    },
    { cases ih,
      apply decidable.is_true, exact foo n ih,
      apply decidable.is_false, sorry,
    }
end

#print even'.decidable_pred

#print nat.decidable_eq

#print decidable_rel

open nat
#print decidable_prime_1
#print prime_def_lt'