import .Q2
import analysis.normed_space.basic

noncomputable theory 

namespace quaternion

instance : has_norm ℍ := ⟨λ z, real.sqrt (norm_sq z)⟩

instance : has_dist ℍ := ⟨λ z w, ∥z-w∥⟩

lemma dist_self (z : ℍ) : dist z z = 0 :=
by {dsimp [dist], rw add_right_neg, dsimp [norm], simp}

lemma eq_of_dist_eq_zero (z w : ℍ) : dist z w = 0 → z = w :=
begin
    intros h,
    dsimp [dist, norm] at h,
    have w := (real.sqrt_eq_zero (norm_sq_nonneg (z + -w))).1 h,
    rw norm_sq_eq_zero at w,
    exact eq_of_sub_eq_zero w,
end

lemma dist_comm (z w : ℍ) : dist z w = dist w z :=
begin
    dsimp [dist, norm],
    have h₁ : norm_sq (z-w) ≥ 0 := norm_sq_nonneg (z-w),
    have h₂ : norm_sq (w-z) ≥ 0 := norm_sq_nonneg (w-z),
    apply (real.sqrt_inj h₁ h₂).2,
    dsimp [norm_sq],
    ring,
end
.

lemma le_of_eq_of_le {a b c : ℝ} : b = c → a ≤ b → a ≤ c :=
by {intros h w, rw [h] at w, exact w}

lemma norm_triangle (z w : ℍ) : ∥z+w∥ ≤ ∥z∥+∥w∥ :=
begin
    dsimp [norm],
    have h₁ := add_nonneg (real.sqrt_nonneg (norm_sq z)) (real.sqrt_nonneg (norm_sq w)),
    rw [real.sqrt_le_left h₁, pow_two],
    ring,
    rw [real.ring.right_distrib, ←pow_two, real.sqr_sqrt (norm_sq_nonneg z), real.sqr_sqrt (norm_sq_nonneg w)],
    have h₂ := real.sqrt_mul (norm_sq_nonneg w) (norm_sq z),
    have h₃ := congr_arg (λ (x : ℝ), 2 * x) h₂,
    simp at h₃,
    rw [←real.ring.mul_assoc] at h₃,
    have h₄ : norm_sq z + 2 * real.sqrt (norm_sq w) * real.sqrt (norm_sq z) + norm_sq w = norm_sq z + 2 * real.sqrt (norm_sq w * norm_sq z) + norm_sq w, by {simp, exact h₃.symm},
    apply le_of_eq_of_le h₄.symm,
    clear h₃ h₄,
    rw [norm_sq_add],
    simp,
    have zero_lt_two : (0 : ℝ) < 2 := by linarith,
    apply (@mul_le_mul_left _ _ (z.i * w.i + (z.j * w.j + (z.k * w.k + z.re * w.re))) _ 2 zero_lt_two).2,
    clear zero_lt_two,
    sorry,
end

lemma dist_triangle (x y z : ℍ) : dist x z ≤ dist x y + dist y z :=
begin
    dsimp [dist],
    have w := norm_triangle (x-y) (y-z),
    simp at w,
    exact w,
end

instance : metric_space ℍ :=
{dist := dist, dist_self := dist_self, eq_of_dist_eq_zero := eq_of_dist_eq_zero, 
    dist_comm := dist_comm, dist_triangle := dist_triangle, ..}

lemma dist_eq (x y : ℍ) : dist x y = ∥x-y∥ :=
by {dsimp [dist], refl}

instance : normed_group ℍ :=
{dist := dist, dist_eq := dist_eq, .. (by apply_instance : metric_space ℍ)}

instance : vector_space ℝ ℍ := by constructor

lemma norm_smul (r : ℝ) (z : ℍ) : ∥r • z∥ = ∥r∥ * ∥z∥ :=
begin
    dsimp [norm],
    rw ←real.sqrt_mul_self_eq_abs,
    rw ←(real.sqrt_mul' (r*r) (norm_sq_nonneg z)),
    have w := mul_nonneg (mul_self_nonneg r) (norm_sq_nonneg z),
    rw (real.sqrt_inj (norm_sq_nonneg (r • z)) w),
    dsimp [norm_sq, (•)],
    ring,
end

instance : normed_space ℝ ℍ :=
{norm_smul := norm_smul, .. (by apply_instance : vector_space ℝ ℍ)}

end quaternion

