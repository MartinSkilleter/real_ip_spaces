import logic.basic
import data.nat.prime
import data.nat.modeq
import tactic.norm_num

open nat

-- A lemma to prove that 4 is not prime
lemma two_divides_four : 2 ∣ 4 :=
begin
    dsimp [(∣)],
    use 2,
    refl,
end

-- A proof that 4 is not prime
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

/-theorem five_is_prime : prime 5 :=
begin
    simp [prime_def_le_sqrt],
    split,
    exact five_geq_two,
    intros m h w,
    have h₁ : sqrt 5 = 2, by sorry,
    simp [h₁] at w,
    have h₂ : m = 2, begin
        rw le_antisymm_iff,
        split,
        exact w,
        exact h,
    end,
    simp [h₂],
    assume h₃ : 2 ∣ 5,
    dsimp [(∣)] at h₃,
    have h₄ : 5 % 2 = 1 := dec_trivial,
    have h₅ : ∀ (c : ℕ), 2*c % 2 = 0, begin
        sorry
    end,
    

    sorry
end
-/

theorem five_is_prime : prime 5 :=
begin
    simp [prime_def_lt],
    split,
    norm_num,
    intros m,
    assume h : m < 5,
    assume w : m ∣ 5,
    simp [(∣)] at w,
    cases w with c,
    cases h with h,
    {sorry},
    
    

    sorry
end


namespace hidden

instance decidable_prime : decidable_pred prime := 
begin
    intros n,
    unfold prime,
    have left_decidable : decidable (n ≥ 2), begin
        dsimp [(≥)],
        apply nat.decidable_le,
    end,
    have right_decidable : ∀ (m : ℕ), m ∣ n → m = 1 ∨ m = n, by sorry,
    sorry

end

end hidden
