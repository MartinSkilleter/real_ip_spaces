import inner_product_spaces.real_ip.basic

noncomputable theory

variables {α : Type*}
variables [decidable_eq α] [add_comm_group α] [vector_space ℝ α] [ℝ_inner_product_space α]

open real

local notation `sqrt` := real.sqrt

instance ip_space_has_dist : has_dist α := ⟨λ x y, sqrt (ip_self (x-y))⟩

lemma ip_dist_self : ∀ x : α, dist x x = 0 :=
begin
    intros x,
    dsimp [dist],
    simp only [add_right_neg],
    apply real.sqrt_eq_zero'.2,
    dsimp [ip_self],
    simp only [left_orthog_to_zero],
end

lemma ip_eq_of_dist_eq_zero : ∀ (x y : α), dist x y = 0 → x = y :=
begin
    intros x y h,
    dsimp [dist] at h,
    rw [real.sqrt_eq_zero (ip_self_nonneg (x+-y)), zero_iff_ip_self_zero] at h,
    exact (eq_of_sub_eq_zero h),
end

lemma ip_dist_comm : ∀ (x y : α), dist x y = dist y x :=
begin
    intros x y,
    dsimp [dist],
    rw [real.sqrt_inj (ip_self_nonneg (x+-y)) (ip_self_nonneg (y+-x))],
    dsimp [ip_self],
    have w := @linearity α _ _ _ _ (x+-y) 0 (x+-y) (-1),
    simp [-add_in_snd_coord, -add_in_fst_coord] at w,
    have k := @mul_in_snd_coord α _ _ _ _ (y+-x) (y+-x) (-1),
    simp [-add_in_snd_coord, -add_in_fst_coord] at k,
    rw [w] at k,
    exact (neg_inj k),
end

instance ip_space_has_norm : has_norm α := ⟨λ x, sqrt ((ip_self x))⟩

@[simp] lemma sqr_norm {x : α} : ∥x∥^2 = (ip_self x) :=
begin
    dsimp [norm],
    rw [real.sqr_sqrt (ip_self_nonneg x)],
end

lemma ip_norm_nonneg {x : α} : ∥x∥ ≥ 0 :=
begin
    dsimp [norm],
    exact real.sqrt_nonneg (ip_self x),
end

def orthog (x y : α) := x†y = 0

infix `⊥` := orthog

lemma orthog_symm {x y : α} : x ⊥ y → y ⊥ x :=
begin
    intros h,
    dsimp [orthog] at h,
    have w := (@conj_symm α _ _ _ _ x y).symm,
    rw [h] at w,
    exact w,
end

lemma orthog_symm' {x y : α} : x ⊥ y → y†x = 0 :=
begin
    intros h,
    have w := orthog_symm h,
    dsimp [orthog] at w,
    exact w,
end

lemma add_orthog {x y z : α} : x⊥z → y⊥z → (x+y)⊥z :=
by {intros hx hy, dsimp [orthog] at *, rw [add_in_fst_coord, hx, hy, add_zero]}

@[simp] lemma mul_orthog {x y : α} {a b : ℝ} : x ⊥ y → (a•x) ⊥ (b•y) :=
begin
    intros h,
    dsimp [orthog],
    dsimp [orthog] at h,
    simp,
    repeat {right},
    exact h,
end

lemma pythagoras {x y : α} : x ⊥ y → ∥x+y∥^2 = ∥x∥^2+∥y∥^2 :=
begin
    intros h,
    dsimp [orthog] at h,
    simp only [sqr_norm],
    dsimp [ip_self],
    simp,
    have w := @conj_symm α _ _ _ _ x y,
    rw [h] at w,
    rw [h,←w],
    simp only [zero_add],
end
.

instance : has_norm ℝ := ⟨abs⟩ 

@[simp] theorem cauchy_schwarz {x y : α} : ∥x†y∥≤∥x∥*∥y∥ :=
begin
    by_cases (y=0),

    rw [h],
    dsimp [norm],
    simp,

    have k : ∥x†y∥^2≤∥x∥^2*∥y∥^2 → ∥x†y∥≤∥x∥*∥y∥ := begin
        intros w,
        have w₁ := sqrt_le_sqrt w,
        dsimp [norm] at *,
        rw [sqrt_mul (pow_two_nonneg _), sqrt_sqr (abs_nonneg _), sqr_sqrt (ip_self_nonneg _), sqr_sqrt (ip_self_nonneg _)] at w₁,
        exact w₁,
    end,
    apply k,
    clear k,
    let c := (x†y)/∥y∥^2,
    have w : 0≤∥x-c•y∥^2 := by exact (pow_two_nonneg ∥x-c•y∥),
    rw [sqr_norm, sqr_norm] at *,
    dsimp [norm],
    rw [←sqrt_sqr_eq_abs, sqr_sqrt (pow_two_nonneg _)],
    dsimp [ip_self] at *,
    simp at w,
    repeat {rw [←neg_one_smul ℝ (c•y)] at w},
    repeat {rw [mul_in_fst_coord] at w},
    repeat {rw [mul_in_snd_coord] at w},
    rw [@conj_symm α _ _ _ _ y x] at w,
    simp at w,
    have k : c = (x†y)/∥y∥^2 := by refl,
    rw [k] at w,
    clear k,
    have k := (@neq_zero_iff_ip_self_neq_zero α _ _ _ _ y).2 h,
    simp only [sqr_norm] at w,
    have w₁ := div_mul_cancel (x†y) k,
    dsimp [ip_self] at *,
    rw [w₁] at w,
    simp at w,
    have w₂ := le_of_sub_nonneg w,
    clear w₁ w,
    have w₃ : (x†y)/(y†y) = (x†y)*(y†y)⁻¹ := by refl,
    rw [mul_comm, w₃, ←mul_assoc, ←pow_two] at w₂,
    have w₄ := @ip_self_nonneg α _ _ _ _ y,
    dsimp [ip_self] at w₄,
    have w₅ := mul_le_mul_of_nonneg_right w₂ w₄,
    rw [mul_assoc, inv_mul_cancel k, mul_one] at w₅,
    exact w₅,
end

lemma sqr_nonneg (r : ℝ) : r^2 ≥ 0 :=
begin
    rw [pow_two],
    exact (mul_self_nonneg r),
end

theorem triangle_ineq (x y : α) : ∥x+y∥≤∥x∥+∥y∥ :=
begin
    have w : ∥x+y∥^2≤(∥x∥+∥y∥)^2 → ∥x+y∥≤∥x∥+∥y∥ := begin
        intros h,
        rw [←sqrt_le (sqr_nonneg _) (sqr_nonneg _),
            sqrt_sqr (ip_norm_nonneg),
            sqrt_sqr (add_nonneg ip_norm_nonneg ip_norm_nonneg)
        ] at h,
        exact h,
    end,
    apply w,
    ring SOP,
    rw [←pow_two],
    repeat {rw [sqr_norm]},
    rw [ip_self_add, add_assoc, add_assoc, add_le_add_iff_left (ip_self x),
    add_le_add_iff_right, mul_assoc, mul_comm ∥y∥ 2, ←mul_assoc,
    mul_comm ∥x∥ 2, mul_assoc,
    @mul_le_mul_left _ _ (x†y) _ 2 (by linarith)],
    have k' := @cauchy_schwarz α _ _ _ _ x y,
    exact le_trans (le_max_left _ _) k',
end

lemma ip_dist_eq : ∀ (x y : α), dist x y = norm (x - y) :=
begin
    intros x y,
    refl,
end

lemma ip_dist_triangle : ∀ (x y z : α), dist x z ≤ dist x y + dist y z :=
begin
    intros x y z,
    repeat {rw [ip_dist_eq]},
    have w : x - z = (x-y) + (y-z) := by simp,
    rw [w],
    exact triangle_ineq (x-y) (y-z),
end

def ip_space_is_metric_space : metric_space α :=
{dist_self := ip_dist_self, eq_of_dist_eq_zero := ip_eq_of_dist_eq_zero, 
dist_comm := ip_dist_comm, dist_triangle := ip_dist_triangle}

-- not an instance for now, causes trouble
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
    dsimp [ip_self],
    simp only [mul_in_fst_coord, mul_in_snd_coord],
    rw [←mul_assoc, ←pow_two, sqr_abs],
end

def ip_space_is_normed_space : normed_space ℝ α :=
{norm_smul := ip_norm_smul,
 .. ip_space_is_normed_group}
.

lemma norm_neq_zero_iff_neq_zero {β : Type*} [normed_space ℝ β] (x : β) : ∥x∥ ≠ (0 : ℝ) ↔ x ≠ (0 : β) :=
begin
    split,

    apply mt,
    exact (norm_eq_zero x).2,

    apply mt,
    exact (norm_eq_zero x).1,
end

lemma norm_eq_iff_norm_sq_eq {β : Type*} [normed_space ℝ β] {x y : β} : ∥x∥=∥y∥ ↔ ∥x∥^2 = ∥y∥^2 :=
begin
    split,

    intros h,
    have w := congr_arg (λ (r : ℝ), r^2) h,
    simp at w,
    exact w,

    intros h,
    have w := congr_arg (λ (r : ℝ), sqrt r) h,
    simp at w,
    exact w,
end
