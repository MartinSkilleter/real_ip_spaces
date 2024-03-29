import inner_product_spaces.real_ip.ip_normed_space

noncomputable theory

section
variables {α : Type*}
variables [decidable_eq α] [add_comm_group α] [vector_space ℝ α] [ℝ_inner_product_space α]

open real

local attribute [instance] classical.prop_decidable

theorem ip_parallelogram_law (x y : α) : ∥x+y∥^2+∥x-y∥^2=2*∥x∥^2+2*∥y∥^2 :=
begin
    repeat {rw [sqr_norm]},
    simp,
    rw [←neg_one_smul ℝ, mul_right],
    ring,
end

class ℝ_parallelopotamus (β : Type*) [normed_space ℝ β] :=
(parallelogram_law : ∀ (x y : β), ∥x+y∥^2+∥x-y∥^2=2*∥x∥^2+2*∥y∥^2)

variables {β : Type*}
variables [decidable_eq β] [normed_space ℝ β] [ℝ_parallelopotamus β]

lemma par_law (x y : β) : ∥x+y∥^2 + ∥x-y∥^2 = 2*∥x∥^2+2*∥y∥^2 :=
by apply ℝ_parallelopotamus.parallelogram_law

lemma par_law' (x y : β) : ∥x+y∥^2 = 2*∥x∥^2 + 2*∥y∥^2 - ∥x-y∥^2 :=
begin
    rw [←add_zero (∥x+y∥^2), ←add_right_neg (∥x-y∥^2), ←add_assoc, sub_eq_add_neg _ (∥x-y∥^2)],
    apply congr_arg (λ r, r + -(∥x-y∥^2)),
    exact par_law x y,
end

instance par_has_inner_product : has_ℝ_inner_product β :=
⟨λ x y, 1/4*(∥x+y∥^2 - ∥x-y∥^2)⟩

lemma nonneg_norm {a : ℝ} {h : a ≥ 0} : ∥a∥ = a :=
by {dsimp [norm], rw [←real.sqrt_sqr_eq_abs, real.sqrt_sqr h]}

lemma neg_norm {a : ℝ} {h : a < 0} : ∥a∥ = -a :=
by {dsimp [norm],
    rw [←abs_neg],
    exact @nonneg_norm _ (le_of_lt (neg_pos_of_neg h))}

set_option class.instance_max_depth 100
lemma norm_sq_eq_norm_sqr (x : β) : ⟪x ∥ x⟫ = ∥x∥^2 :=
begin
    dsimp [inner_product],
    simp,
    have l : (1 : ℝ) + 1 = 2 := rfl,
    have h : x + x = (2 : ℝ) • x := begin
        rw [←one_smul ℝ x, ←add_smul, one_smul],
        have w : (1 : ℝ) + 1 = 2 := rfl,
        rw [w],
    end,
    have w : ((0 : ℝ) ^2) = 0 := by {rw [pow_two, mul_zero]},
    rw [w, neg_zero, zero_add, h, norm_smul, pow_two, @nonneg_norm 2 (by linarith),
    ←pow_two, mul_pow],
    have k : (2 : ℝ)^2 = (4 : ℝ) := begin
        have k₁ : 2^2 = 4 := rfl,
        have k₂ := congr_arg (λ (n : ℕ), (n : ℝ)) k₁,
        simp at k₂,
        exact k₂,
    end,
    rw [k, ←mul_assoc, inv_mul_cancel, one_mul],

    exact four_ne_zero,
end

lemma par_pos_def (x : β) (h : x ≠ (0 : β)) : ⟪x ∥ x⟫ > (0 : ℝ) :=
by {rw [norm_sq_eq_norm_sqr, pow_two],
    exact mul_pos ((norm_pos_iff x).2 h) ((norm_pos_iff x).2 h)}

lemma par_conj_symm (x y : β) : ⟪x ∥ y⟫ = ⟪y ∥ x⟫ :=
begin
    dsimp [inner_product],
    simp,
    have w : x+-y = -(y+-x) := by simp,
    rw [w, ←neg_one_smul ℝ (y+-x), norm_smul],
    have k := @neg_norm (-1) (by linarith),
    rw [neg_neg] at k,
    rw [k, one_mul],
end

-- Scott: so what's the plan here?
-- How many applications of the parallelogram axiom are required?
lemma par_add_law {x y z : β} : ∥x+y+z∥^2 = ∥x+y∥^2 + ∥x+z∥^2 + ∥y+z∥^2 - ∥x∥^2 - ∥y∥^2 - ∥z∥^2 :=
begin
    dsimp [inner_product],
    sorry
end

lemma par_add_in_fst_coord {x y z : β} : ⟪x+y ∥ z⟫ = ⟪x ∥ z⟫ + ⟪y ∥ z⟫ :=
begin
    dsimp [inner_product],
    rw [par_add_law, par_add_law, ←left_distrib],
    apply congr_arg (λ (r : ℝ), 1/4*r),
    simp,
    ring,
end

@[simp] lemma par_right_orthog_to_zero {x : β} : ⟪0 ∥ x⟫ = 0 :=
by {dsimp [inner_product], simp}

@[simp] lemma par_left_orthog_to_zero {x : β} : ⟪x ∥ 0⟫ = 0 :=
by {rw [par_conj_symm], exact par_right_orthog_to_zero}

lemma par_smul_nat (x z : β) (n : ℕ) : ⟪(n : ℝ) • x ∥ z⟫ = (n : ℝ) * ⟪x ∥ z⟫ :=
by {induction n, {simp}, {rw [nat.cast_succ, add_smul, one_smul, par_add_in_fst_coord, n_ih,
    ←one_mul ⟪x ∥ z⟫, ←mul_assoc, ←right_distrib, mul_one, one_mul]}}

lemma par_smul_neg {x z : β} : ⟪-x ∥ z⟫ = -⟪x ∥ z⟫ :=
begin
    dsimp [inner_product],
    simp,
    ring,
    have w₁ : -x-z = -(x+z) := by simp,
    rw [w₁, ←neg_one_smul ℝ (x+z), norm_smul, neg_norm, neg_neg, one_mul],
    have w₂ : ∥x + z∥ ^ 2 - ∥x - z∥ ^ 2 = -(∥z - x∥ ^ 2 - ∥x + z∥ ^ 2) := begin
        simp,
        have w₂ : x+-z = -(z+-x) := by simp,
        rw [w₂, ←neg_one_smul ℝ _, norm_smul, neg_norm, neg_neg, one_mul],
        linarith,
    end,
    rw [w₂],
    ring,
    linarith,
end

lemma par_smul_int {x z : β} (n : ℤ) : ⟪(n : ℝ) • x ∥ z⟫ = (n : ℝ) * ⟪x ∥ z⟫ :=
by {cases n, {rw [int.cast_of_nat], exact par_smul_nat x z n}, 
    {rw [int.cast_neg_succ_of_nat, neg_add_rev, ←neg_one_mul, ←neg_one_mul ↑n, 
    ←left_distrib, ←smul_smul, neg_one_smul, par_smul_neg, ←neg_one_mul, mul_assoc],
    apply congr_arg (λ (r : ℝ), (-1)*r),
    rw [←nat.cast_one, ←nat.cast_add],
    exact par_smul_nat x z (1+n)}}

lemma rat_mul_denom_eq_num (q : ℚ) : q * q.denom = q.num :=
begin
    rw [rat.num_denom q],
    sorry,
end

lemma par_smul_rat {x z : β} (r : ℚ) : ⟪(r : ℝ) • x ∥ z⟫ = (r : ℝ) * ⟪x ∥ z⟫ :=
begin
    let p := r.num,
    have ph : p = r.num := rfl,
    let q := r.denom,
    have qh : q = r.denom := rfl,
    let h := r.pos,

    rw [←qh] at h,
    have w := @par_smul_nat _ _ _ _ ((r : ℝ) • x) z q,
    have w₁ : ↑(r.denom) * ↑(rat.mk (r.num) ↑(r.denom)) = ↑r.num := sorry,
    conv at w {to_lhs, rw [rat.num_denom r, qh, ←mul_smul, w₁]},
    repeat {sorry},
end

lemma par_smul_real {x z : β} (r : ℝ) : ⟪r • x ∥ z⟫ = r * ⟪x ∥ z⟫ :=
begin
    sorry,
end

lemma par_linearity (x y z : β) (a : ℝ) : ⟪a•x+y ∥ z⟫ = a*⟪x ∥ z⟫ + ⟪y ∥ z⟫ :=
by {rw [par_add_in_fst_coord, par_smul_real]}

instance par_is_ip_space : ℝ_inner_product_space β :=
{conj_symm := par_conj_symm, linearity := par_linearity, pos_def := par_pos_def}

end
