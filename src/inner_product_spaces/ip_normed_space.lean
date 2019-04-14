import inner_product_spaces.basic

noncomputable theory

variables {α : Type*}
variables [decidable_eq α] [add_comm_group α] [vector_space ℂ α] [inner_product_space α]

-- local attribute [instance] classical.prop_decidable

open complex

instance ip_space_has_dist : has_dist α := ⟨λ x y, real.sqrt ((ip_self (x-y)).re)⟩

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
    simp [-add_in_snd_coord, -additivity] at w,
    have k := mul_in_snd_coord (y+-x) (y+-x) (-1),
    simp [-add_in_snd_coord, -additivity] at k,
    rw [w] at k,
    have k' := (@neg_inj ℂ _ _ _) k,
    rw [ext_iff] at k',
    cases k',
    exact k'_left,
end

instance ip_space_has_norm : has_norm α := ⟨λ x, real.sqrt ((ip_self x).re)⟩

def orthog (x y : α) := x†y = 0

@[simp] lemma conj_zero_of_orthog (x y : α) : orthog x y → y†x=0 :=
begin
    intros h,
    dsimp [orthog] at h,
    have w := (conj_symm x y).symm,
    rw [h, conj_eq_zero] at w,
    exact w,
end

lemma pythagoras (x y : α) : orthog x y → ∥x+y∥^2 = ∥x∥^2+∥y∥^2 :=
begin
    intros h,
    dsimp [orthog] at h,
    dsimp [norm],
    rw [real.sqr_sqrt (ip_self_nonneg (x+y)), real.sqr_sqrt (ip_self_nonneg x), real.sqr_sqrt (ip_self_nonneg y)],
    rw [←add_re],
    have k : (ip_self (x + y)) = (ip_self x + ip_self y),
    
    dsimp [ip_self],
    simp,
    rw [h, conj_zero_of_orthog x y h],
    simp,

    apply (ext_iff.1 k).left,
end

example (r s : ℝ) : r = 0 → s = 0 → r + s = 0 := by library_search

lemma ip_dist_triangle : ∀ (x y z : α), dist x z ≤ dist x y + dist y z :=
begin
    sorry,
end

instance ip_space_is_metric_space : metric_space α :=
{dist_self := ip_dist_self, eq_of_dist_eq_zero := ip_eq_of_dist_eq_zero, 
dist_comm := ip_dist_comm, dist_triangle := ip_dist_triangle}

lemma ip_dist_eq : ∀ (x y : α), dist x y = norm (x - y) :=
begin
    intros x y,
    refl,
end

instance ip_space_is_normed_group : normed_group α :=
{dist_eq := ip_dist_eq}

-- lemma ip_norm_smul : ∀ (a : ℂ) (x : α), norm (a • x) = has_norm.norm a * norm x

instance ip_space_is_normed_space : normed_space ℂ α :=
{norm_smul := sorry}