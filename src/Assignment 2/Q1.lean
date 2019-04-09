import data.nat.basic

-- First definition of prime (quite "prim(e)itive")
def prime (p : ℕ) := p ≥ 2 ∧ ∀ (m < p), m ∣ p → m = 1

open nat

-- A lemma to prove that 4 is not prime
lemma two_divides_four : 2 ∣ 4 :=
begin
    dsimp [(∣)],
    use 2,
    refl,
end

-- Question 1a
theorem four_is_not_prime : ¬ (prime 4) :=
begin
    unfold prime,
    simp [not_and_distrib],
    right,
    intros h,
    have h₁ : 2 ∣ 4, by exact two_divides_four,
    have h₂ : 2 < 4, by exact dec_trivial,
    have w := h 2 h₂ h₁,
    have w' : 2 ≠ 1, by exact dec_trivial,
    contradiction,
end

-- A lemma to prove that 5 is prime; dec_trivial was not used because we can't use tactics in MathLib
lemma five_ge_two : 5 ≥ 2 :=
begin
    dsimp [(≥)],
    rw [le_iff_lt_or_eq],
    left,
    have h₁ : 3 ≠ 0, begin
        intros h,
        contradiction,
    end,
    have h₂ : 3 > 0, by exact nat.pos_of_ne_zero h₁,
    dsimp [(>)] at h₂,
    have h₃ : 1 < 4, by exact succ_lt_succ h₂,
    have h₄ : 2 < 5, by exact succ_lt_succ h₃,
    exact h₄,
end

-- This tactic gives a contradiction proof that a non-factor does not divide a number
-- I couldn't work out how to make the name n be given as an input
meta def case_bash : tactic unit :=
`[intros h, repeat {cases n, cases h, try {cases h}}]

lemma two_not_div_five (n : ℕ) : 5 ≠ 2 * n := by case_bash

lemma three_not_div_five (n : ℕ) : 5 ≠ 3 * n := by case_bash

lemma four_not_div_five (n : ℕ) : 5 ≠ 4 * n := by case_bash

-- Question 1a
theorem five_is_prime : prime 5 :=
begin
    unfold prime,
    split,
    exact five_ge_two,
    intros m h w,
    cases m,
    dsimp [(∣)] at w,
    cases w with c w,
    simp only [zero_mul] at w,
    contradiction,
    cases m,
    trivial,
    cases m,
    cases w with c w,
    have w' : 5 ≠ 2 * c, by apply two_not_div_five,
    contradiction,
    cases m,
    cases w with c w,
    have w' : 5 ≠ 3 * c, by apply three_not_div_five,
    contradiction,
    cases m,
    cases w with c w,
    have w' : 5 ≠ 4 * c, by apply four_not_div_five,
    contradiction,
    cases m,
    repeat {cases h with h h},
end

-- It is decidable that one natural number is greater than or equal to another
instance decidable_ge {a b : ℕ} : decidable (a ≥ b) :=
begin
    dsimp [(≥)],
    apply nat.decidable_le b a,
end

-- Builds up in stages that the right-hand side of the and statement in the definition of prime
-- is decidable. It begins by saying that it is decidable if a number equals 1.
-- Then it is decidable if one number divides another. Finally, a lemma from MathLib is used
-- which says that it is decidable that, if you have an upper bound for a predicate and that
-- predicate is decidable for any specific natural number then it is decidable for all natural 
-- numbers.
instance decidable_divisors {p : ℕ} : decidable (∀ (m : ℕ), m < p → m ∣ p → m = 1) :=
begin
    apply nat.decidable_ball_lt p (λ (m : ℕ) (a : m < p), m ∣ p → m = 1),    
end

-- First instance of decidability about primes. Uses and.decidable and the previous two
-- lemmas to say that the whole statement is decidable.
-- Note that haveI is used to update the instance cache after the instances are declared.
instance decidable_prime : decidable_pred prime :=
begin
    intros p,
    unfold prime,
    haveI h₁ : decidable (p ≥ 2) := decidable_ge,
    haveI h₂ : decidable (∀ (m : ℕ), m < p → m ∣ p → m = 1) := decidable_divisors,
    apply and.decidable,
end

-- A second definition of primality. We will prove that this is equivalent to the
-- first definition.
def prime' (p : ℕ) := p ≥ 2 ∧ ∀ (m ≤ p/2), m ∣ p → m = 1

-- If a natural number a is less than or equal to b/2 then it is less than b
-- Used as a lemma in prime_im_prime'
lemma lt_half_lt {a b : ℕ} : (b > 0) → a ≤ b/2 → a < b :=
begin
    intros h w,
    have h₁ : 2 > 1, by exact dec_trivial,
    have h₂ : b/2 < b, by apply div_lt_self h h₁,
    have h₃ : a < b, by apply lt_of_le_of_lt w h₂,
    exact h₃,
end

-- Essentially used to say that if p is prime then p > 0
lemma ge_two_gt_zero {p : ℕ} : p ≥ 2 → p > 0 :=
begin
    intros h,
    dsimp [(≥)] at h,
    have w₁ : 1 < p, by apply lt_of_succ_le h,
    have w₂ : 0 < 1, by exact dec_trivial,
    have w₃ : 0 < p, by apply lt_trans w₂ w₁,
    dsimp [(>)],
    exact w₃,
end

-- Non-zero factors of a number respect multiplication
lemma div_gt_zero_eq {m p k: ℕ} : m ∣ p → m > 0 → p / m = k → p = m * k :=
begin
    intros h₁ h₂ h₃,
    have h₄ : m * p / m = p := nat.mul_div_cancel_left p h₂,
    subst h₃,
    have h₅ : m * p / m = m * (p / m) := nat.mul_div_assoc m h₁,
    rw h₅ at h₄,
    exact h₄.symm,
end

-- The reciprocals of positive natural numbers behave as you would
-- expect them to under ≤
lemma dvd_pos_lt {a b c : ℕ} : c ≤ b → 0 < c → a / b ≤ a / c :=
begin
    intros h₁ h₂,
    apply (le_div_iff_mul_le (a/b) a h₂).2,
    have h₃ : a * c ≤ a * b := mul_le_mul_left a h₁,
    apply le_trans,
    swap,
    apply div_mul_le_self',
    exact b,
    apply nat.mul_le_mul_left (a/b),
    exact h₁,
end

-- The first definition prime → the second definition prime'
theorem prime_im_prime' {p : ℕ} : prime p → prime' p :=
begin
    intro h,
    unfold prime at h,
    unfold prime',
    split,
    exact h.1,
    have ge := h.1,
    have h₁ := h.2,
    intros m w₁ w₂,
    have w₃ : p > 0, by apply ge_two_gt_zero ge,
    have w₄ : m < p, by apply lt_half_lt w₃ w₁,
    have w₅ : m = 1, by apply h₁ m w₄ w₂,
    exact w₅,
end

-- The second definition prime' → the first definition prime
theorem prime'_im_prime {p : ℕ} : prime' p → prime p :=
begin
    intros w,
    unfold prime' at w,
    unfold prime,
    split,
    exact w.1,
    have ge := w.1,
    intros m w₁ w₂,
    by_cases (m ≤ p/2),
    exact w.2 m h w₂,
    simp at h,
    have two_gt_zero : 2 > 0, by exact dec_trivial,
    -- Wasn't written as a lemma because I felt it would be unwieldy to pass
    -- hypotheses around
    have one_lt_half : p / 2 ≥ 1, begin
        have le : 2 ≤ p := ge,
        have z : 2/2 ≤ p / 2 := nat.div_le_div_right le,
        have h₁ : 2 / 2 = 1 := nat.div_self two_gt_zero,
        rw [h₁] at z,
        exact z,
    end,
    -- Same as above. Relies on hypotheses.
    have h₄ : m > 0, begin
        have zero_lt_one : 0 < 1, by exact dec_trivial,
        have h₂ : 0 < p / 2, by apply lt_of_lt_of_le zero_lt_one one_lt_half,
        exact (lt_trans h₂ h),
    end,
    have m_gt_one : m > 1, by apply lt_of_le_of_lt one_lt_half h,
    have m_ge_two : m ≥ 2, by apply succ_le_of_lt m_gt_one,
    have h₁ : p / m ≤ p / 2 := dvd_pos_lt m_ge_two two_gt_zero,
    have h₂ : p / m ∣ p, by apply div_dvd_of_dvd w₂,
    have h₃ : p / m = 1, by apply w.2 (p/m) h₁ h₂,
    have h₅ : p = m * 1 := div_gt_zero_eq w₂ h₄ h₃,
    simp at h₅,
    subst h₅,
    have h₆ : p ≥ p, by exact le_refl p,
    have h₇ : ¬ (p < p), by simp,
    exact (absurd w₁ h₇),
end

-- Uses the constructor for ↔ and the above implications to give an equivalence statement
theorem prime_equiv_statement {p : ℕ} : prime p ↔ prime' p :=
⟨prime_im_prime', prime'_im_prime⟩

-- See explanation above decidable_divisors. Construction is the same but upper bound used is p/2
-- instead of p
instance decidable_divisors' {p : ℕ}: decidable (∀ (m : ℕ), m < p / 2 → m ∣ p → m = 1) :=
nat.decidable_ball_lt (p / 2) (λ (m : ℕ) (a : m < p / 2), m ∣ p → m = 1)

-- Says that it is possible to decide if a natural number is prime under prime'
instance decidable_prime' : decidable_pred prime' :=
begin
    intros p,
    unfold prime',
    haveI h₁ : decidable (p ≥ 2) := decidable_ge,
    haveI h₂ : decidable (∀ (m : ℕ), m < p / 2 → m ∣ p → m = 1) := decidable_divisors',
    apply and.decidable,
end

-- Gives a "better" instance for decidable_prime by applying the equivalence of
-- prime and prime'. It is better because you only need to check half as many natural numbers.
instance decidable_prime_v2 : decidable_pred prime :=
begin
    intros p,
    apply decidable_of_iff' (prime' p) (@prime_equiv_statement p),
end

