import logic.basic
import data.nat.prime

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
    have h : 2 ∣ 4, by exact two_divides_four,
    simp [prime, not_and_distrib],
    right,
    intros h₁,
    have h₂ := h₁ 2 h,
    cases h₂,
    {cases h₂},
    {cases h₂}
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

lemma two_not_div_five : ∀ (n : ℕ), 5 ≠ 2 * n :=
begin
    intros n h,
    cases n,
    cases h,
    cases n,
    cases h,
    cases n,
    cases h,
    cases h,
end

lemma three_not_div_five : ∀ (n : ℕ), 5 ≠ 3 * n :=
begin
    intros n h,
    cases n,
    cases h,
    cases n,
    cases h,
    cases h,
end

lemma four_not_div_five : ∀ (n : ℕ), 5 ≠ 4 * n :=
begin
    intros n h,
    cases n,
    cases h,
    cases n,
    cases h,
    cases h,
end

theorem five_is_prime : prime 5 :=
begin
    simp [prime_def_lt],
    split,
    exact five_ge_two,
    intros m,
    assume h : m < 5,
    assume w : m ∣ 5,
    simp [(∣)] at w,
    cases w with c w,
    sorry,
    
    
end

theorem five_is_prime' : prime 5 :=
begin
    simp [prime_def_le_sqrt],
    split,
    exact five_ge_two,
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
    intros h₃,
    dsimp [(∣)] at h₃,
    have h₄ : 5 % 2 = 1 := dec_trivial,
    have h₅ : ∀ (c : ℕ), 2*c % 2 = 0, begin
        sorry
    end,
    

    sorry
end


namespace hidden

instance decidable_prime : decidable_pred prime := 
begin
    intros n,
    unfold prime,
    induction n with n ih,
    {apply decidable.is_false,
     intros h,
     cases h with hl hr,
     have h₁ : 0 < 2, begin
        
     end
    }
end

end hidden
