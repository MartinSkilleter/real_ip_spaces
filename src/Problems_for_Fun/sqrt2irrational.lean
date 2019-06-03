import data.real.basic

open rat

lemma mul_own_denom (q : ℚ) : q * q.denom = q.num :=
begin
    rw [num_denom q],
    ring,
    have k₁ : (mk (q.num) ↑(q.denom)).denom = q.denom := by sorry,
    rw [k₁],
    have k₂ : ((mk (q.num) ↑(q.denom)).num) = q.num := by sorry,
    rw [k₂],
    sorry,
end

lemma div_2_of_sqr_div_2 (a : ℤ) (h : 2 ∣ a * a) : 2 ∣ a :=
begin
    by_contradiction k,
    dsimp [(∣)] at *,
    simp at k,
    cases h with c h,
    sorry,
end

theorem sqrt2nonintegral : ∀ (z : ℤ), z^2 ≠ 2 :=
begin
    intros z,
    by_contradiction h,
    rw [ne.def, not_not] at h,
    sorry,
end

theorem sqrt2irrational : ∀ (q : ℚ), q^2 ≠ 2 :=
begin
    intros q,
    by_contradiction h,
    rw [ne.def, not_not] at h,
    have pos := q.pos,
    have cop := q.cop,
    rw [pow_two] at h,
    have h₁ := congr_arg (λ (p : ℚ), p * q.denom * q.denom) h,
    simp at h₁,
    rw [mul_comm, mul_assoc, mul_own_denom, ←mul_assoc, mul_comm _ q, 
        mul_own_denom, mul_assoc] at h₁,
    have w := dvd.intro (↑(q.denom) * ↑(q.denom)) h₁.symm,
    dsimp [(∣)] at w,
    sorry,
end