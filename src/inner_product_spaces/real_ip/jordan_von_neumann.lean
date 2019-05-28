import inner_product_spaces.real_ip.ip_normed_space

noncomputable theory

section
variables {α : Type*}
variables [decidable_eq α] [add_comm_group α] [vector_space ℝ α] [ℝ_inner_product_space α]

open real

local attribute [instance] classical.prop_decidable

theorem ip_parallelogram_law (x y : α) : ∥x+y∥^2+∥x-y∥^2=2*∥x∥^2+2*∥y∥^2 :=
begin
    simp,
    dsimp [ip_self],
    have w : x†-y = -(x†y), begin
        rw [←neg_one_smul ℝ y, mul_in_snd_coord],
        ring,
    end,
    rw [w],
    simp,
    ring,
end

class ℝ_parallelopotamus (β : Type*) [normed_space ℝ β] :=
(parallelogram_law : ∀ (x y : β), ∥x+y∥^2+∥x-y∥^2=2*∥x∥^2+2*∥y∥^2)

variables {β : Type*}
variables [decidable_eq β] [normed_space ℝ β] [ℝ_parallelopotamus β] 

@[simp] lemma par_law (x y : β) : ∥x+y∥^2 + ∥x-y∥^2 = 2*∥x∥^2+2*∥y∥^2 :=
by apply ℝ_parallelopotamus.parallelogram_law

instance par_has_inner_product : has_ℝ_inner_product β := ⟨λ x y, 1/4*(∥x+y∥^2 - ∥x-y∥^2)⟩

lemma nonneg_norm {a : ℝ} {h : a ≥ 0} : ∥a∥ = a :=
begin
    dsimp [norm],
    rw [←real.sqrt_sqr_eq_abs, real.sqrt_sqr h],
end

lemma neg_norm {a : ℝ} {h : a < 0} : ∥a∥ = -a :=
begin
    have k := @nonneg_norm _ (le_of_lt (neg_pos_of_neg h)),
    dsimp [norm] at *,
    simp at k,
    exact k,
end

set_option class.instance_max_depth 100
lemma ip_self_eq_norm_sq (x : β) : (x†x) = ∥x∥^2 :=
begin
    dsimp [(†)],
    simp,
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

lemma par_pos_def (x : β) : x ≠ (0 : β) → x†x > (0 : ℝ) :=
begin
    intros h,
    have w : ∥x∥ > (0 : ℝ) := by exact ((norm_pos_iff x).2 h),
    have w₁ := (mul_pos w w),
    rw [←pow_two, ←ip_self_eq_norm_sq x] at w₁,
    exact w₁,
end

lemma par_conj_symm (x y : β) : x†y = y†x :=
begin
    dsimp [(†)],
    simp,
    have w : x+-y = -(y+-x) := by simp,
    rw [w, ←neg_one_smul ℝ (y+-x), norm_smul],
    have k := @neg_norm (-1) (by linarith),
    rw [neg_neg] at k,
    rw [k, one_mul],
end
.

lemma par_add_law {x y z : β} : ∥x+y+z∥^2 = ∥x+y∥^2 + ∥x+z∥^2 + ∥y+z∥^2 - ∥x∥^2 - ∥y∥^2 - ∥z∥^2 :=
begin
    sorry,
end

lemma par_add_in_fst_coord {x y z : β} : (x+y)†z = x†z + y†z :=
begin
    have w := par_law (x+z) y,
    have k := par_law (x-z) y,
    have l := congr_arg2 (λ {a c : ℝ}, a - c) w k,
    simp at l,
    dsimp [(†)],
    rw [←left_distrib],
    apply congr_arg (λ (x : ℝ), 1/4 * x),
    ring at *,
    sorry,
end

@[simp] lemma par_right_orthog_to_zero {x : β} : 0†x = 0 :=
begin
    dsimp [(†)],
    simp,
end

@[simp] lemma par_left_orthog_to_zero {x : β} : x†0 = 0 :=
by {rw [par_conj_symm], exact par_right_orthog_to_zero}

lemma par_smul_nat {x z : β} : ∀ (n : ℕ), ((n : ℝ) • x) † z = (n : ℝ) * (x † z) :=
begin
    intros n,
    induction n,

    simp,

    simp,
    rw [add_smul, one_smul, par_add_in_fst_coord, n_ih, 
    ←one_mul (x†z), ←mul_assoc, ←right_distrib, mul_one, one_mul],
end

lemma par_smul_neg {x z : β} : (-x) † z = -(x † z) :=
begin
    dsimp [(†)],
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

lemma par_smul_int {x z : β} : ∀ (n : ℤ), ((n : ℝ) • x) † z = (n : ℝ) * (x † z) :=
begin
    intros n,
    cases n,

    simp,
    exact par_smul_nat n,

    simp,
    rw [←neg_one_mul, ←neg_one_mul ↑n, ←left_distrib, ←smul_smul, neg_one_smul, par_smul_neg],
    have w := @par_smul_nat β _ _ _ x z (1+n),
    simp at w,
    rw [w, ←neg_one_mul, ←mul_assoc],
end

lemma par_smul_rat {x z : β} : ∀ (r : ℚ), ((r : ℝ) • x) † z = (r : ℝ) * (x † z) :=
begin
    intros r,
    let p := r.num,
    have ph : p = r.num := rfl,
    let q := r.denom,
    have qh : q = r.denom := rfl,
    let h := r.pos,
    
    rw [←qh] at h,
    sorry,
end

lemma par_smul_real {x z : β} : ∀ (r : ℝ), (r • x) † z = r * (x † z) :=
begin
    intros r,
    sorry,
end

lemma par_linearity (x y z : β) (a : ℝ) : (a•x+y)†z = a*(x†z) + y†z :=
begin
    rw [par_add_in_fst_coord, par_smul_real],
end

instance par_is_ip_space : ℝ_inner_product_space β :=
{conj_symm := par_conj_symm, linearity := par_linearity, pos_def := par_pos_def}

end
