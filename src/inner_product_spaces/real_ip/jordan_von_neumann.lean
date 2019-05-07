import inner_product_spaces.real_ip.ip_normed_space

noncomputable theory

variables {α : Type*}
variables [decidable_eq α] [add_comm_group α] [vector_space ℝ α] [ℝ_inner_product_space α]

open real

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

class ℝ_parallelopotamus (β : Type*) extends normed_space ℝ β :=
(parallelogram_law : ∀ (x y : β), ∥x+y∥^2+∥x-y∥^2=2*∥x∥^2+2*∥y∥^2)

variables {β : Type*}
variables [decidable_eq β] [par : ℝ_parallelopotamus β]

-- set_option trace.class_instances true
def par_inner_product (x y : β) : ℝ := 1/4*(∥x+y∥^2 - ∥x-y∥^2)

instance par_has_inner_product : has_ℝ_inner_product β := ⟨par_inner_product⟩

-- set_option pp.all true
lemma ip_self_eq_norm_sq (x : β) : (x†x) = ∥x∥^2 :=
begin
    dsimp [(†), par_inner_product],
    ring,
    have h : x + x = 2•x := begin
        have h₁ : 1 + 1 = 2 := by exact dec_trivial,
        rw [←h₁, add_smul, one_smul],
    end,
    rw [h],
    have h₁ := norm_smul (2 : ℝ) x,
    rw [h₁],
    sorry,
end

lemma par_pos_def (x : β) : x ≠ (0 : β) → x†x > (0 : ℝ) :=
begin
    intros h,
    have w : ∥x∥ > (0 : ℝ) := begin
        have w := (norm_neq_zero_iff_neq_zero x).2,
        sorry,
    end,
    have w₁ := (mul_pos w w),
    rw [←pow_two, ←ip_self_eq_norm_sq x] at w₁,
    exact w₁,
end

lemma par_conj_symm (x y : β) : x†y = y†x :=
begin
    dsimp [(†), par_inner_product],
    simp,
    have w : x+-y = -(y+-x) := by simp,
    -- rw [w, ←neg_one_smul ℝ (y+-x), norm_smul (-1)],
    sorry,
end