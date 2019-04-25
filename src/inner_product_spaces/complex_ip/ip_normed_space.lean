import inner_product_spaces.complex_ip.basic

noncomputable theory

variables {α : Type*}
variables [decidable_eq α] [add_comm_group α] [vector_space ℂ α] [ℂ_inner_product_space α]

open complex

local notation `sqrt` := real.sqrt

instance ip_space_has_dist : has_dist α := ⟨λ x y, sqrt ((ip_self (x-y)).re)⟩

lemma ip_dist_self : ∀ x : α, dist x x = 0 :=
begin
    intros x,
    dsimp [dist],
    simp only [add_right_neg],
    apply real.sqrt_eq_zero'.2,
    dsimp [ip_self],
    simp only [zero_re, left_orthog_to_zero],
end

lemma ip_eq_of_dist_eq_zero : ∀ (x y : α), dist x y = 0 → x = y :=
begin
    intros x y h,
    dsimp [dist] at h,
    rw [real.sqrt_eq_zero (ip_self_nonneg (x+-y))] at h,
    have w := (@ext_iff (ip_self (x+-y)) 0).2,
    have k := w (and.intro h (ip_self_im_zero (x+-y))),
    rw [zero_iff_ip_self_zero] at k,
    exact eq_of_sub_eq_zero k,
end

lemma ip_dist_comm : ∀ (x y : α), dist x y = dist y x :=
begin
    intros x y,
    dsimp [dist],
    rw [real.sqrt_inj (ip_self_nonneg (x+-y)) (ip_self_nonneg (y+-x))],
    dsimp [ip_self],
    have w := linearity (x+-y) 0 (x+-y) (-1),
    simp [-add_in_snd_coord, -add_in_fst_coord] at w,
    have k := mul_in_snd_coord (y+-x) (y+-x) (-1),
    simp [-add_in_snd_coord, -add_in_fst_coord] at k,
    rw [w] at k,
    have k' := (@neg_inj ℂ _ _ _) k,
    rw [ext_iff] at k',
    cases k',
    exact k'_left,
end

instance ip_space_has_norm : has_norm α := ⟨λ x, sqrt ((ip_self x).re)⟩

@[simp] lemma sqr_norm (x : α) : ∥x∥^2 = (ip_self x).re :=
begin
    dsimp [norm],
    rw [real.sqr_sqrt (ip_self_nonneg x)],
end

lemma ip_norm_nonneg (x : α) : ∥x∥ ≥ 0 :=
begin
    dsimp [norm],
    exact real.sqrt_nonneg (ip_self x).re,
end

def orthog (x y : α) := x†y = 0

infix `⊥` := orthog

lemma orthog_symm (x y : α) : x ⊥ y → y ⊥ x :=
begin
    intros h,
    dsimp [orthog] at h,
    have w := (conj_symm x y).symm,
    rw [h, conj_eq_zero] at w,
    exact w,
end

lemma orthog_symm' (x y : α) : x ⊥ y → y†x = 0 :=
begin
    intros h,
    have w := orthog_symm x y h,
    dsimp [orthog] at w,
    exact w,
end

@[simp] lemma mul_orthog (x y : α) (a b : ℂ) : x ⊥ y → (a•x) ⊥ (b•y) :=
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
    rw [←add_re],
    have k : (ip_self (x + y)) = (ip_self x + ip_self y),
    
    dsimp [ip_self],
    simp,
    rw [h, orthog_symm' x y h],
    simp,

    apply (ext_iff.1 k).left,
end
.

-- Note that although the cases hypothesis is not used, division by ∥y∥^2 is only defined if y≠0
@[simp] theorem cauchy_schwarz (x y : α) : ∥x†y∥≤∥x∥*∥y∥ :=
begin
    by_cases (y = 0),

    rw [h],
    dsimp [norm],
    simp,
    
    have w : ∀ (t : ℂ), (ip_self (x+t•y)).re ≥ 0, by {intros t, exact (ip_self_nonneg _)},
    dsimp [ip_self] at w,
    
    sorry,
end

lemma sqr_nonneg (r : ℝ) : r^2 ≥ 0 :=
begin
    rw [pow_two],
    exact (mul_self_nonneg r),
end

lemma le_of_sqrt_sqr (r : ℝ) : r ≤ sqrt (r^2) :=
begin
    rw [le_iff_lt_or_eq],
    by_cases (r ≥ 0),

    right,
    exact (real.sqrt_sqr h).symm,

    left,
    simp at h,
    have w := real.sqrt_nonneg (r^2),
    exact lt_of_lt_of_le h w,
end

lemma re_le_norm (x y : α) : (x†y).re ≤ ∥x†y∥ :=
begin
    dsimp [norm, complex.abs, norm_sq],
    have w := le_of_sqrt_sqr (x†y).re,
    apply (le_trans w),
    rw [real.sqrt_le (sqr_nonneg (x†y).re) (add_nonneg (mul_self_nonneg _) (mul_self_nonneg _)),
    pow_two],
    simp only [add_comm, le_add_iff_nonneg_left],
    exact (mul_self_nonneg _),
end

theorem triangle_ineq (x y : α) : ∥x+y∥≤∥x∥+∥y∥ :=
begin
    have w : ∥x+y∥^2≤(∥x∥+∥y∥)^2 → ∥x+y∥≤∥x∥+∥y∥ := begin
        intros h,
        rw [←real.sqrt_le (sqr_nonneg (∥x+y∥)) (sqr_nonneg (∥x∥+∥y∥)), 
        real.sqrt_sqr (ip_norm_nonneg (x+y)), 
        real.sqrt_sqr (add_nonneg (ip_norm_nonneg x) (ip_norm_nonneg y))] at h,
        exact h,
    end,
    apply w,
    ring SOP,
    rw [←pow_two],
    repeat {rw [sqr_norm]},
    rw [ip_self_add x y, add_assoc, add_assoc, add_le_add_iff_left (ip_self x).re,
    add_le_add_iff_right, mul_assoc, mul_comm ∥y∥ 2, ←mul_assoc,
    mul_comm ∥x∥ 2, mul_assoc,
    @mul_le_mul_left _ _ (x†y).re _ 2 (by linarith)],
    have k := re_le_norm x y,
    have k' := cauchy_schwarz x y,
    exact le_trans k k',
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

instance ip_space_is_metric_space : metric_space α :=
{dist_self := ip_dist_self, eq_of_dist_eq_zero := ip_eq_of_dist_eq_zero, 
dist_comm := ip_dist_comm, dist_triangle := ip_dist_triangle}

instance ip_space_is_normed_group : normed_group α :=
{dist_eq := ip_dist_eq}

instance : has_norm ℂ := ⟨λ z, abs z⟩

lemma ip_norm_smul : ∀ (a : ℂ) (x : α), ∥a • x∥ = ∥a∥*∥x∥:=
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
    rw [←norm_sq_eq_abs, ←mul_assoc, mul_comm (conj a) a, mul_conj],
    simp,
end

instance ip_space_is_normed_space : normed_space ℂ α :=
{norm_smul := ip_norm_smul}
.

lemma norm_neq_zero_iff_neq_zero (x : α) : ∥x∥ ≠ 0 ↔ x ≠ 0 :=
begin
    split,

    apply mt,
    exact (norm_eq_zero x).2,

    apply mt,
    exact (norm_eq_zero x).1,
end


