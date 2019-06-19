import inner_product_spaces.real_ip.basic

noncomputable theory

variables {α : Type*}
variables [decidable_eq α] [add_comm_group α] [vector_space ℝ α] [ℝ_inner_product_space α]

open real

instance ip_space_has_dist : has_dist α := ⟨λ x y, sqrt (norm_sq (x-y))⟩

lemma ip_dist_self (x : α) : dist x x = 0 :=
by {dsimp [dist],
    rw [add_right_neg, norm_sq_zero, sqrt_zero]}

lemma ip_eq_of_dist_eq_zero (x y : α) (h : dist x y = 0) : x = y :=
begin
    dsimp [dist] at h,
    rw [real.sqrt_eq_zero (norm_sq_nonneg (x+-y)), zero_iff_norm_sq_zero] at h,
    exact (eq_of_sub_eq_zero h),
end

lemma ip_dist_comm (x y : α) : dist x y = dist y x :=
by {dsimp [dist],
    rw [←sub_eq_add_neg, ←sub_eq_add_neg, real.sqrt_inj (norm_sq_nonneg (x-y)) (norm_sq_nonneg (y-x)),
    ←neg_sub x y, norm_sq_neg_eq, sub_eq_add_neg]}

instance ip_space_has_norm : has_norm α := ⟨λ x, sqrt ((norm_sq x))⟩

@[simp] lemma sqr_norm {x : α} : ∥x∥^2 = (norm_sq x) := real.sqr_sqrt (norm_sq_nonneg x)

lemma ip_norm_nonneg {x : α} : ∥x∥ ≥ 0 := real.sqrt_nonneg (norm_sq x)

@[reducible] def orthog (x y : α) := ⟪x ∥ y⟫ = 0

infix `⊥` := orthog

lemma orthog_symm {x y : α} (h : x ⊥ y) : y ⊥ x :=
by {dsimp [orthog] at *,
    rw [←conj_symm x y],
    exact h}

lemma zero_of_orthog_self {x : α} : x ⊥ x → x = 0 :=
(zero_iff_norm_sq_zero x).1

lemma add_orthog {x y z : α} (hx : x ⊥ z) (hy : y ⊥ z) : (x+y)⊥z :=
by {dsimp [orthog] at *, rw [add_left, hx, hy, add_zero]}

lemma mul_orthog (x y : α) (a b : ℝ) : x ⊥ y → (a•x) ⊥ (b•y) :=
by {intros h,
    simp [orthog],
    repeat {right},
    exact h}

lemma pythagoras {x y : α} (h : x ⊥ y) : ∥x+y∥^2 = ∥x∥^2+∥y∥^2 :=
begin
    dsimp [orthog] at h,
    simp [sqr_norm, norm_sq],
    have w := @conj_symm α _ _ _ _ x y,
    rw [h] at w,
    rw [h, ←w, zero_add, zero_add],
end

lemma orthog_of_pythagoras {x y : α} (h : ∥x+y∥^2 = ∥x∥^2 + ∥y∥^2) : x ⊥ y :=
begin
    rw [sqr_norm, sqr_norm, sqr_norm, norm_sq_add, add_assoc] at h,
    conv at h {to_rhs, rw [←add_zero (norm_sq y)]},
    have w := (add_left_inj _).mp h,
    have k := congr_arg (λ (r : ℝ), 1/2 * r) w,
    simp at k,
    rw [left_distrib, ←mul_assoc, inv_mul_cancel two_ne_zero, one_mul] at k,
    conv at k {to_rhs, rw [←add_zero (2⁻¹ * norm_sq y)]},
    exact (add_left_inj _).mp k,
end

lemma pythagoras_iff_orthog {x y : α} : ∥x+y∥^2 = ∥x∥^2 + ∥y∥^2 ↔ x ⊥ y :=
⟨orthog_of_pythagoras, pythagoras⟩

-- Scott: maybe even provide the instance of `normed_group`?
-- I wonder where in mathlib this belongs. Possibly even `data.real.basic`.
instance : has_norm ℝ := ⟨abs⟩

lemma norm_leq_of_norm_sq_leq (x y : α) (h : ∥⟪x ∥ y⟫∥^2≤∥x∥^2*∥y∥^2) : ∥⟪x ∥ y⟫∥≤∥x∥*∥y∥ :=
by {have w := sqrt_le_sqrt h,
        dsimp [norm] at *,
        rw [sqrt_mul (pow_two_nonneg _), sqrt_sqr (abs_nonneg _), sqr_sqrt (norm_sq_nonneg _), sqr_sqrt (norm_sq_nonneg _)] at w,
        exact w}

lemma norm_sq_ip_eq_ip_sqr (x y : α) : ∥⟪x ∥ y⟫∥^2 = ⟪x ∥ y⟫^2 :=
by {dsimp [norm], rw [←sqrt_sqr_eq_abs, sqr_sqrt (pow_two_nonneg _)]}

@[simp] theorem cauchy_schwarz (x y : α) : ∥⟪x ∥ y⟫∥≤∥x∥*∥y∥ :=
begin
    by_cases (y=0),

    { dsimp [norm],
      rw [h],
      simp },
    apply norm_leq_of_norm_sq_leq,
    let c := ⟪x ∥ y⟫/∥y∥^2,
    have w := pow_two_nonneg (∥x-c•y∥),
    rw [sqr_norm, sqr_norm] at *,
    rw [norm_sq_ip_eq_ip_sqr],
    dsimp [norm_sq] at *,
    simp at w,
    repeat {rw [←neg_one_smul ℝ (c•y)] at w},
    repeat {rw [mul_left] at w},
    repeat {rw [mul_right] at w},
    rw [conj_symm y x] at w,
    simp at w,
    have k₁ : c = ⟪x ∥ y⟫/∥y∥^2 := by refl,
    rw [k₁] at w,
    have k₂ := (neq_zero_iff_norm_sq_neq_zero y).2 h,
    simp only [sqr_norm] at w,
    have w₁ := div_mul_cancel ⟪x ∥ y⟫ k₂,
    dsimp [norm_sq] at *,
    rw [w₁] at w,
    simp at w,
    have w₂ := le_of_sub_nonneg w,
    have w₃ : ⟪x ∥ y⟫/⟪y ∥ y⟫ = ⟪x ∥ y⟫*⟪y ∥ y⟫⁻¹ := by refl,
    rw [mul_comm, w₃, ←mul_assoc, ←pow_two] at w₂,
    have w₄ := norm_sq_nonneg y,
    dsimp [norm_sq] at w₄,
    have w₅ := mul_le_mul_of_nonneg_right w₂ w₄,
    rw [mul_assoc, inv_mul_cancel k₂, mul_one] at w₅,
    exact w₅,
end

lemma sqr_nonneg (r : ℝ) : r^2 ≥ 0 :=
by {rw [pow_two], exact mul_self_nonneg r}

lemma norm_sqr_eq_sqr (r : ℝ) : ∥r^2∥ = r^2 := abs_of_nonneg (sqr_nonneg r)

lemma sqr_pos_iff_neq_zero (r : ℝ) : r^2 > 0 ↔ r ≠ 0 :=
begin
    constructor,

    rw [awesome_mt],
    simp,
    intros k,
    rw [k, pow_two, mul_zero],

    rw [awesome_mt],
    simp,
    intros k,
    rw [le_iff_eq_or_lt] at k,
    cases k,
    exact pow_eq_zero k,

    have l := sqr_nonneg r,
    dsimp [(≥)] at l,
    rw [←not_lt] at l,
    exact absurd k l,
end

-- mul_le_mul_right_le --> mul_le_mul_of_nonneg_right

lemma norm_add_leq_of_norm_add_sqr_leq (x y : α) (h : ∥x+y∥^2≤(∥x∥+∥y∥)^2) : ∥x+y∥≤∥x∥+∥y∥ :=
by {rw [←sqrt_le (sqr_nonneg _) (sqr_nonneg _),
            sqrt_sqr (ip_norm_nonneg),
            sqrt_sqr (add_nonneg ip_norm_nonneg ip_norm_nonneg)] at h,
        exact h}

theorem triangle_ineq (x y : α) : ∥x+y∥≤∥x∥+∥y∥ :=
begin
    apply norm_add_leq_of_norm_add_sqr_leq,
    rw [sqr_norm, pow_two, left_distrib, right_distrib, right_distrib, ←pow_two,
    ←pow_two, sqr_norm, sqr_norm, norm_sq_add, add_assoc, add_assoc, add_le_add_iff_left,
    ←add_assoc, add_le_add_iff_right (norm_sq y), mul_comm ∥y∥, ←mul_two, mul_comm],
    apply mul_le_mul_of_nonneg_right,
    apply le_trans (le_abs_self ⟪x ∥ y⟫),
    exact cauchy_schwarz x y,

    rw [le_iff_eq_or_lt],
    right,
    exact two_pos,
end

lemma ip_dist_eq (x y : α) : dist x y = norm (x - y) := rfl

lemma ip_dist_triangle (x y z : α) : dist x z ≤ dist x y + dist y z :=
begin
    repeat {rw [ip_dist_eq]},
    have w : x - z = (x-y) + (y-z) := by simp,
    rw [w],
    exact triangle_ineq (x-y) (y-z),
end

def ip_space_is_metric_space : metric_space α :=
{dist_self := ip_dist_self,
 eq_of_dist_eq_zero := ip_eq_of_dist_eq_zero,
 dist_comm := ip_dist_comm,
 dist_triangle := ip_dist_triangle}

def ip_space_is_normed_group : normed_group α :=
{dist_eq := ip_dist_eq,
..ip_space_is_metric_space}

lemma sqr_abs (r : ℝ) : r^2 = (abs r)^2 :=
by rw [←sqrt_sqr_eq_abs, sqr_sqrt (pow_two_nonneg r)]

lemma ip_norm_smul : ∀ (a : ℝ) (x : α), ∥a • x∥ = ∥a∥*∥x∥:=
begin
    intros a x,
    dsimp [norm],
    have h₁ := real.sqrt_sqr (abs_nonneg a),
    have h₂ := pow_two_nonneg (abs a),
    rw [←h₁, ←real.sqrt_mul h₂],
    have h₃ := mul_nonneg h₂ (norm_sq_nonneg x),
    rw [real.sqrt_inj (norm_sq_nonneg (a•x)) h₃],
    simp only [norm_sq, mul_left, mul_right],
    rw [←mul_assoc, ←pow_two, sqr_abs],
end

def ip_space_is_normed_space : normed_space ℝ α :=
{norm_smul := ip_norm_smul,
 .. ip_space_is_normed_group}

lemma norm_neq_zero_iff_neq_zero {β : Type*} [normed_space ℝ β] (x : β) : ∥x∥ ≠ (0 : ℝ) ↔ x ≠ (0 : β) :=
⟨by {apply mt, exact (norm_eq_zero x).2}, by {apply mt, exact (norm_eq_zero x).1}⟩

lemma norm_eq_iff_norm_sq_eq {β : Type*} [normed_space ℝ β] {x y : β} : ∥x∥=∥y∥ ↔ ∥x∥^2 = ∥y∥^2 :=
⟨by {apply congr_arg (λ (r : ℝ), r^2)}, 
 by {intros h, have w := congr_arg (λ (r : ℝ), sqrt r) h, simp at w, exact w}⟩

lemma norm_sqr_leq_iff_norm_leq {β : Type*} [normed_space ℝ β] {x : β} {a : ℝ} {k : a ≥ 0}: ∥x∥^2 ≤ a^2 ↔ ∥x∥ ≤ a :=
begin
    have w := sqrt_le (mul_nonneg (norm_nonneg x) (norm_nonneg x)) (mul_nonneg k k),
    rw [←pow_two, ←pow_two, sqrt_sqr (norm_nonneg _), sqrt_sqr k] at w,
    exact w.symm,
end

-- Scott: are these abandoned? Maybe move them closer to the point of use?

lemma four_ne_zero : (4 : ℝ) ≠ 0 :=
ne.symm (ne_of_lt four_pos)

lemma leq_of_add_nonneg {a b c : ℝ} {ha : a ≥ 0} {hb : b ≥ 0} {hc : c ≥ 0} : a = b + c → b ≤ a :=
by {intros h, linarith}

