import data.nat.basic
import tactic.interactive

def prime (p : ℕ) := p ≥ 2 ∧ ∀ (m < p), m ∣ p → m = 1

open nat

-- A lemma to prove that 4 is not prime
lemma two_divides_four : 2 ∣ 4 :=
begin
    dsimp [(∣)],
    use 2,
    refl,
end

example {n : ℕ} : n = n := by library_search

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

meta def case_bash : tactic unit :=
`[intros h, repeat {cases n, cases h, try {cases h}}]

lemma two_not_div_five (n : ℕ) : 5 ≠ 2 * n := by case_bash

lemma three_not_div_five (n : ℕ) : 5 ≠ 3 * n := by case_bash

lemma four_not_div_five (n : ℕ) : 5 ≠ 4 * n := by case_bash

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

instance decidable_ge {a b : ℕ} : decidable (a ≥ b) :=
begin
    dsimp [(≥)],
    apply nat.decidable_le b a,
end

instance decidable_prime : decidable_pred prime :=
begin
    intros p,
    unfold prime,
    -- refine (eq.mpr _ and.decidable),
    apply_instance,
end

#print decidable_prime

def prime' (p : ℕ) := p ≥ 2 ∧ ∀ (m ≤ p/2), m ∣ p → m = 1

lemma lt_half_lt {a b : ℕ} : (b > 0) → a ≤ b/2 → a < b :=
begin
    intros h w,
    have h₁ : 2 > 1, by exact dec_trivial,
    have h₂ : b/2 < b, by apply div_lt_self h h₁,
    have h₃ : a < b, by apply lt_of_le_of_lt w h₂,
    exact h₃,
end

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

lemma div_gt_zero_eq {m p k: ℕ} : m ∣ p → m > 0 → p / m = k → p = m * k :=
begin
    intros h₁ h₂ h₃,
    have h₄ : m * p / m = p := nat.mul_div_cancel_left p h₂,
    subst h₃,
    have h₅ : m * p / m = m * (p / m) := nat.mul_div_assoc m h₁,
    rw h₅ at h₄,
    exact h₄.symm,
end

theorem prime_equiv_statement {p : ℕ} : prime p ↔ prime' p :=
begin
    split,
    -- Forwards implication
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
    -- Converse implication
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
    have h₁ : p / m ≤ p / 2, sorry,
    have h₂ : p / m ∣ p, sorry,
    have h₃ : p / m = 1, by apply w.2 (p/m) h₁ h₂,
    have h₄ : m > 0, sorry,
    have h₅ : p = m * 1 := div_gt_zero_eq w₂ h₄ h₃,
    simp at h₅,
    subst h₅,
    have h₆ : p ≥ p, by exact le_refl p,
    exfalso w₁ h₆,


    sorry,
    

    


end

instance decidable_prime' : decidable_pred prime' :=
begin
    intros p,
    sorry,
end

