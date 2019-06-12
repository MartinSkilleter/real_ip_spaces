import inner_product_spaces.real_ip.basic

noncomputable theory

variables {α : Type*}
variables [decidable_eq α] [add_comm_group α] [vector_space ℝ α] [ℝ_inner_product_space α]

open real

lemma neg_sub_eq_sub_neg {α : Type*} [add_comm_group α] (a b : α) : a-b = -(b-a) := by simp

local notation `sqrt` := real.sqrt

instance ip_space_has_dist : has_dist α := ⟨λ x y, sqrt (ip_self (x-y))⟩

lemma ip_dist_self : ∀ x : α, dist x x = 0 :=
by {intros x,
    dsimp [dist],
    rw [add_right_neg, ip_self_zero, sqrt_zero]}

lemma ip_eq_of_dist_eq_zero : ∀ (x y : α), dist x y = 0 → x = y :=
begin
    intros x y h,
    dsimp [dist] at h,
    rw [real.sqrt_eq_zero (ip_self_nonneg (x+-y)), zero_iff_ip_self_zero] at h,
    exact (eq_of_sub_eq_zero h),
end

lemma ip_dist_comm : ∀ (x y : α), dist x y = dist y x :=
by {intros x y,
    dsimp [dist],
    rw [real.sqrt_inj (ip_self_nonneg (x+-y)) (ip_self_nonneg (y+-x)), 
    ←sub_eq_add_neg, neg_sub_eq_sub_neg, ip_self_neg_eq, sub_eq_add_neg]}

instance ip_space_has_norm : has_norm α := ⟨λ x, sqrt ((ip_self x))⟩

@[simp] lemma sqr_norm {x : α} : ∥x∥^2 = (ip_self x) := real.sqr_sqrt (ip_self_nonneg x)

lemma ip_norm_nonneg {x : α} : ∥x∥ ≥ 0 := real.sqrt_nonneg (ip_self x)

@[reducible] def orthog (x y : α) := x†y = 0

infix `⊥` := orthog

lemma orthog_symm {x y : α} : x ⊥ y → y ⊥ x :=
by {intros h,
    dsimp [orthog] at *,
    rw [←conj_symm x y],
    exact h}

lemma orthog_symm' {x y : α} : x ⊥ y → y†x = 0 :=
begin
    intros h,
    have w := orthog_symm h,
    dsimp [orthog] at w,
    exact w,
end

lemma zero_of_orthog_self {x : α} : x ⊥ x → x = 0 :=
(zero_iff_ip_self_zero x).1

lemma add_orthog {x y z : α} : x⊥z → y⊥z → (x+y)⊥z :=
by {intros hx hy, dsimp [orthog] at *, rw [add_in_fst_coord, hx, hy, add_zero]}

@[simp] lemma mul_orthog {x y : α} {a b : ℝ} : x ⊥ y → (a•x) ⊥ (b•y) :=
by {intros h,
    simp [orthog],
    repeat {right},
    exact h}

lemma pythagoras {x y : α} : x ⊥ y → ∥x+y∥^2 = ∥x∥^2+∥y∥^2 :=
begin
    intros h,
    dsimp [orthog] at h,
    simp only [sqr_norm, ip_self],
    simp,
    have w := @conj_symm α _ _ _ _ x y,
    rw [h] at w,
    rw [h, ←w, zero_add, zero_add],
end

lemma orthog_of_pythagoras {x y : α} : ∥x+y∥^2 = ∥x∥^2 + ∥y∥^2 → x ⊥ y :=
begin
    intros h,
    rw [sqr_norm, sqr_norm, sqr_norm, ip_self_add, add_assoc] at h,
    conv at h {to_rhs, rw [←add_zero (ip_self y)]},
    have w := (add_left_inj _).mp h,
    have k := congr_arg (λ (r : ℝ), 1/2 * r) w,
    simp at k,
    rw [left_distrib, ←mul_assoc, inv_mul_cancel two_ne_zero, one_mul] at k,
    conv at k {to_rhs, rw [←add_zero (2⁻¹ * ip_self y)]},
    exact (add_left_inj _).mp k,
end

lemma pythagoras_iff_orthog {x y : α} : ∥x+y∥^2 = ∥x∥^2 + ∥y∥^2 ↔ x ⊥ y :=
⟨orthog_of_pythagoras, pythagoras⟩

instance : has_norm ℝ := ⟨abs⟩ 

@[simp] theorem cauchy_schwarz (x y : α) : ∥x†y∥≤∥x∥*∥y∥ :=
begin
    by_cases (y=0),

    dsimp [norm],
    rw [h],
    simp,

    have k : ∥x†y∥^2≤∥x∥^2*∥y∥^2 → ∥x†y∥≤∥x∥*∥y∥ := begin
        intros w,
        have w₁ := sqrt_le_sqrt w,
        dsimp [norm] at *,
        rw [sqrt_mul (pow_two_nonneg _), sqrt_sqr (abs_nonneg _), sqr_sqrt (ip_self_nonneg _), sqr_sqrt (ip_self_nonneg _)] at w₁,
        exact w₁,
    end,
    apply k,
    let c := (x†y)/∥y∥^2,
    have w := pow_two_nonneg (∥x-c•y∥),
    rw [sqr_norm, sqr_norm] at *,
    dsimp [norm],
    rw [←sqrt_sqr_eq_abs, sqr_sqrt (pow_two_nonneg _)],
    dsimp [ip_self] at *,
    simp at w,
    repeat {rw [←neg_one_smul ℝ (c•y)] at w},
    repeat {rw [mul_in_fst_coord] at w},
    repeat {rw [mul_in_snd_coord] at w},
    rw [conj_symm y x] at w,
    simp at w,
    have k₁ : c = (x†y)/∥y∥^2 := by refl,
    rw [k₁] at w,
    have k₂ := (@neq_zero_iff_ip_self_neq_zero α _ _ _ _ y).2 h,
    simp only [sqr_norm] at w,
    have w₁ := div_mul_cancel (x†y) k₂,
    dsimp [ip_self] at *,
    rw [w₁] at w,
    simp at w,
    have w₂ := le_of_sub_nonneg w,
    have w₃ : (x†y)/(y†y) = (x†y)*(y†y)⁻¹ := by refl,
    rw [mul_comm, w₃, ←mul_assoc, ←pow_two] at w₂,
    have w₄ := @ip_self_nonneg α _ _ _ _ y,
    dsimp [ip_self] at w₄,
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

lemma mul_le_mul_right_le (a b c : ℝ) : c ≥ 0 → a ≤ b → a*c ≤ b*c :=
begin
    intros k w,
    by_cases (c=0),

    rw [h, mul_zero, mul_zero],

    have k' : c > 0 := begin
        dsimp [(≥)] at k,
        rw [le_iff_eq_or_lt] at k,
        cases k,

        exact absurd k.symm h,

        exact k,
    end,

    exact (mul_le_mul_right k').2 w,
end

theorem triangle_ineq (x y : α) : ∥x+y∥≤∥x∥+∥y∥ :=
begin
    have w : ∥x+y∥^2≤(∥x∥+∥y∥)^2 → ∥x+y∥≤∥x∥+∥y∥ := begin
        intros h,
        rw [←sqrt_le (sqr_nonneg _) (sqr_nonneg _),
            sqrt_sqr (ip_norm_nonneg),
            sqrt_sqr (add_nonneg ip_norm_nonneg ip_norm_nonneg)] at h,
        exact h,
    end,
    apply w,
    rw [sqr_norm, pow_two, left_distrib, right_distrib, right_distrib, ←pow_two,
    ←pow_two, sqr_norm, sqr_norm, ip_self_add, add_assoc, add_assoc, add_le_add_iff_left,
    ←add_assoc, add_le_add_iff_right (ip_self y), mul_comm ∥y∥, ←mul_two, mul_comm],
    apply mul_le_mul_of_nonneg_right,
    apply le_trans (le_abs_self (x†y)),
    exact cauchy_schwarz x y,

    rw [le_iff_eq_or_lt],
    right,
    exact two_pos,
end

lemma ip_dist_eq : ∀ (x y : α), dist x y = norm (x - y) := by {intros x y, refl}

lemma ip_dist_triangle : ∀ (x y z : α), dist x z ≤ dist x y + dist y z :=
begin
    intros x y z,
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
    have h₃ := mul_nonneg h₂ (ip_self_nonneg x),
    rw [real.sqrt_inj (ip_self_nonneg (a•x)) h₃],
    simp only [ip_self, mul_in_fst_coord, mul_in_snd_coord],
    rw [←mul_assoc, ←pow_two, sqr_abs],
end

def ip_space_is_normed_space : normed_space ℝ α :=
{norm_smul := ip_norm_smul,
 .. ip_space_is_normed_group}

lemma norm_neq_zero_iff_neq_zero {β : Type*} [normed_space ℝ β] (x : β) : ∥x∥ ≠ (0 : ℝ) ↔ x ≠ (0 : β) :=
⟨by {apply mt, exact (norm_eq_zero x).2}, by {apply mt, exact (norm_eq_zero x).1}⟩

lemma norm_eq_iff_norm_sq_eq {β : Type*} [normed_space ℝ β] {x y : β} : ∥x∥=∥y∥ ↔ ∥x∥^2 = ∥y∥^2 :=
begin
    split,

    apply congr_arg (λ (r : ℝ), r^2),

    intros h,
    have w := congr_arg (λ (r : ℝ), sqrt r) h,
    simp at w,
    exact w,
end

lemma norm_sqr_leq_iff_norm_leq {β : Type*} [normed_space ℝ β] {x : β} {a : ℝ} {k : a ≥ 0}: ∥x∥^2 ≤ a^2 ↔ ∥x∥ ≤ a :=
begin
    have w := sqrt_le (mul_nonneg (norm_nonneg x) (norm_nonneg x)) (mul_nonneg k k),
    repeat {rw [←pow_two] at w},
    rw [sqrt_sqr (norm_nonneg _), sqrt_sqr k] at w,
    exact w.symm,
end

lemma four_ne_zero : (4 : ℝ) ≠ 0 :=
ne.symm (ne_of_lt four_pos)

lemma leq_of_add_nonneg {a b c : ℝ} {ha : a ≥ 0} {hb : b ≥ 0} {hc : c ≥ 0} : a = b + c → b ≤ a :=
by {intros h, linarith}

