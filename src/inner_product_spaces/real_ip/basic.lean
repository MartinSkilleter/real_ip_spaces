import analysis.normed_space.basic
import tactic.basic

noncomputable theory

open real

variables {α : Type*} {β : Type*}

lemma awesome_mt {p q : Prop} [decidable p] [decidable q] : p → q ↔ (¬q → ¬p) :=
by {constructor, exact mt, have w := @mt ¬q ¬p, rw [not_not, not_not] at w, exact w}

class has_ℝ_inner_product (α : Type*) := (inner_product : α → α → ℝ)

export has_ℝ_inner_product (inner_product)

class ℝ_inner_product_space (α : Type*) [add_comm_group α] [vector_space ℝ α] extends has_ℝ_inner_product α :=
(conj_symm : ∀ (x y : α), inner_product x y = inner_product y x)
(linearity : ∀ (x y z : α), ∀ (a : ℝ), inner_product (a • x + y) z = a * inner_product x z + inner_product y z)
(pos_def : ∀ (x : α), x ≠ 0 → inner_product x x > 0)

variables [decidable_eq α] [add_comm_group α] [vector_space ℝ α] [ℝ_inner_product_space α]

notation `⟪` x `∥` y `⟫` := inner_product x y

section ℝ_inner_product_space

lemma conj_symm (x y : α) : ⟪x ∥ y⟫ = ⟪y ∥ x⟫ :=
by apply ℝ_inner_product_space.conj_symm

lemma linearity (x y z : α) (a : ℝ) : ⟪a • x + y ∥ z⟫ = a * ⟪x ∥ z⟫ + ⟪y ∥ z⟫ :=
by apply ℝ_inner_product_space.linearity

@[simp] lemma add_left (x y z : α) : ⟪x + y ∥ z⟫ = ⟪x ∥ z⟫ + ⟪y ∥ z⟫ :=
by {have h := linearity x y z 1,
    simp only [one_mul, one_smul] at h,
    exact h}

lemma pos_def (x : α) : x ≠ 0 → ⟪x ∥ x⟫ > 0 :=
by apply ℝ_inner_product_space.pos_def

@[simp] lemma right_orthog_to_zero (x : α) : ⟪0 ∥ x⟫ = 0 :=
by {have h := linearity 0 0 x 1,
    rw [add_zero, one_mul, smul_zero] at h,
    conv at h {to_lhs, rw [←add_zero ⟪0 ∥ x⟫]},
    exact (add_left_cancel h).symm}

@[simp] lemma left_orthog_to_zero (x : α) : ⟪x ∥ 0⟫ = 0 :=
by {rw [conj_symm],
    exact right_orthog_to_zero x}

lemma zero_of_right_orthog_to_all (y : α) (h : ∀ (x : α), ⟪x ∥ y⟫ = 0) : y = 0 :=
by {have w := mt (pos_def y),
    simp [le_iff_lt_or_eq] at w,
    exact (w (or.inr (h y)))}

lemma zero_of_left_orthog_to_all (y : α) (h : ∀ (x : α), ⟪y ∥ x⟫ = 0) : y = 0 :=
by {apply zero_of_right_orthog_to_all y, intros x, rw [conj_symm], exact h x}

@[simp] lemma mul_left (x z : α) (a : ℝ) : ⟪a•x ∥ z⟫ = a*⟪x ∥ z⟫ :=
by {rw [←add_zero (a•x), ←add_zero (a*⟪x ∥ z⟫), ←right_orthog_to_zero z],
    exact linearity x 0 z a}

lemma left_ext (x y : α) (h : ∀ (z : α), ⟪x ∥ z⟫ = ⟪y ∥ z⟫) : x = y :=
begin
    have k : ∀ (z : α), ⟪x-y ∥ z⟫ = 0 := begin
        intros z,
        simp,
        rw [←add_right_neg ⟪y ∥ z⟫, ←neg_one_mul, ←mul_left, neg_one_smul],
        apply (congr_arg (λ g, g + ⟪-y ∥ z⟫)),
        exact h z,
    end,
    have k' := zero_of_left_orthog_to_all _ k,
    exact sub_eq_zero.1 k',
end

lemma right_ext (x y : α) (h : ∀ (z : α), ⟪z ∥ x⟫ = ⟪z ∥ y⟫) : x = y :=
begin
    apply left_ext x y,
    intros z,
    rw [conj_symm, conj_symm y],
    exact h z,
end

@[reducible] def norm_sq : α → ℝ := λ x, ⟪x ∥ x⟫

@[simp] lemma norm_sq_zero : norm_sq (0 : α) = 0 := right_orthog_to_zero 0

lemma zero_of_norm_sq_zero (x : α) (h : norm_sq x = 0) : x = 0 :=
by {by_contradiction,
  exact ne_of_gt (pos_def x a) h}

lemma zero_iff_norm_sq_zero (x : α) : norm_sq x = 0 ↔ x = 0 :=
⟨zero_of_norm_sq_zero x, by { rintro rfl, simp }⟩

-- Scott:
-- If we want to PR lots of these will need to be golfed in similar ways.
lemma neq_zero_iff_norm_sq_neq_zero (x : α) : norm_sq x ≠ 0 ↔ x ≠ 0 :=
⟨by {apply mt, exact (zero_iff_norm_sq_zero x).2}, by {apply mt, exact (zero_iff_norm_sq_zero x).1}⟩

@[simp] lemma norm_sq_nonneg (x : α) : norm_sq x ≥ 0 :=
by {apply le_iff_eq_or_lt.2, by_cases (x=0), 
    {left, rw [h], exact norm_sq_zero.symm}, 
    {right, exact pos_def x h}}

@[simp] lemma add_right (x y z : α) : ⟪x ∥ y + z⟫ = ⟪x ∥ y⟫ + ⟪x ∥ z⟫ :=
by {rw [conj_symm, add_left, conj_symm, conj_symm z]}

@[simp] lemma mul_right (x y : α) (a : ℝ) : ⟪x ∥ a • y⟫ = a * ⟪x ∥ y⟫ :=
by {rw [conj_symm, mul_left, conj_symm]}

@[simp] lemma norm_sq_add (x y : α) : norm_sq (x+y) = norm_sq x + 2*⟪x ∥ y⟫ + norm_sq y :=
by {dsimp [norm_sq], simp, rw [conj_symm], ring}

@[simp] lemma norm_sq_neg_eq (x : α) : norm_sq (-x) = norm_sq x :=
by {dsimp [norm_sq],
    rw [←neg_one_smul ℝ, mul_left, mul_right,
        ←mul_assoc, ←neg_eq_neg_one_mul, neg_neg, one_mul]}

end ℝ_inner_product_space