import logic.basic
import data.nat.prime

open nat

lemma two_divides_four : 2 ∣ 4 :=
begin
    dsimp [(∣)],
    use 2,
    refl,
end

theorem four_is_not_prime : ¬ (prime 4) :=
begin
    have h : 2 ∣ 4, begin exact two_divides_four end,
    simp [prime, not_and_distrib],
    right,
    intros h₁,
    have h₂ := h₁ 2 h,
    cases h₂,
    {cases h₂},
    {cases h₂}
end

lemma div_leq (a b : ℕ) : a ∣ b → a ≤ b :=
begin
sorry
end

theorem five_is_prime : prime 5 :=
begin
    simp [prime],
    have h₁ : 5 ≥ 2, begin sorry end,
    split,
    exact h₁,
    intros m,
    have h₂ : m ≤ 5, begin sorry end
    sorry
    
end

#print prime