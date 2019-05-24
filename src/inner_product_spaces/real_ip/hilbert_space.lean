import inner_product_spaces.real_ip.ip_normed_space
import linear_algebra.basic

noncomputable theory

variables {α : Type*} {β : Type*}
variables [decidable_eq α] [add_comm_group α] [vector_space ℝ α] [ℝ_inner_product_space α]
variables [decidable_eq β] [add_comm_group β] [vector_space ℝ β] [ℝ_inner_product_space β]

open real

section operator_norm

instance α_normed_space : normed_space ℝ α := ip_space_is_normed_space
instance β_normed_space : normed_space ℝ β := ip_space_is_normed_space

variables {T : α →ₗ[ℝ] β} {is_lin : is_linear_map ℝ T}

def is_lin_bound (T : α →ₗ[ℝ] β) (M : ℝ) := ∀ (x : α), ∥T x∥ ≤ M*∥x∥

def linear_bounds (T : α →ₗ[ℝ] β) : set ℝ := {M | M ≥ 0 ∧ is_lin_bound T M}

def is_lin_bounded (T : α →ₗ[ℝ] β) := ∃ (M ≥ 0), is_lin_bound T M

structure bounded_linear_operator 
(α : Type*) (β : Type*) [add_comm_group α] [vector_space ℝ α] [ℝ_inner_product_space α]
[decidable_eq α] [decidable_eq β] [add_comm_group β] [vector_space ℝ β] [ℝ_inner_product_space β]:=
(T : α →ₗ[ℝ] β)
(has_bound : is_lin_bounded T)

instance bounded_has_norm : has_norm (bounded_linear_operator α β) := ⟨λ T, Inf (linear_bounds T.T)⟩

lemma add_respects_sum {T S : α →ₗ[ℝ] β} : ∀ (x y : α), T (x + y) + S (x + y) = T x + S x + (T y + S y) :=
by {intros x y, simp}

lemma add_respects_smul {T S : α →ₗ[ℝ] β} : ∀ (c : ℝ), ∀ (x : α), T (c • x) + S (c • x) = c • (T x + S x) :=
by {intros c x, simp, rw [←smul_add]}

instance operators_has_add : has_add (α →ₗ[ℝ] β) := 
⟨λ T S, linear_map.mk (λ x, T x + S x) add_respects_sum add_respects_smul⟩

lemma add_le {a b c d : ℝ} : a ≤ b → c ≤ d → a + c ≤ b + d :=
begin
    intros h w,
    have k₁ := @add_le_add_right' ℝ _ a b c h,
    have k₂ := @add_le_add_left' ℝ _ _ _ b w,
    exact le_trans k₁ k₂,
end

lemma add_is_bounded {T S : α →ₗ[ℝ] β} (hT : is_lin_bounded T) (hS : is_lin_bounded S) : is_lin_bounded (T + S) :=
begin
    dsimp [is_lin_bounded] at *,
    cases hT with M₁ hT,
    cases hT with h₁ hT,
    cases hS with M₂ hS,
    cases hS with h₂ hS,
    use (M₁ + M₂),
    use (add_nonneg h₁ h₂),
    dsimp [is_lin_bound] at *,
    intros x,
    have hT' := hT x,
    have hS' := hS x,
    apply le_trans (triangle_ineq (T x) (S x)),
    rw [right_distrib],
    exact add_le hT' hS',
end

instance bounded_has_add : has_add (bounded_linear_operator α β) := 
⟨λ T S, bounded_linear_operator.mk (T.T + S.T) (add_is_bounded T.has_bound S.has_bound)⟩ 

lemma zero_respects_add : ∀ (x y : α), (λ x, (0 : β)) (x + y) = (λ x, (0 : β)) x + (λ x, (0 : β)) y :=
by {intros x y, simp}

lemma zero_respects_smul : ∀ (c : ℝ), ∀ (x : α), (λ x, (0 : β)) (c • x) = c • (λ x, (0 : β)) x :=
by {intros c x, simp}

instance operators_has_zero : has_zero (α →ₗ[ℝ] β) :=
⟨linear_map.mk (λ x, 0) zero_respects_add zero_respects_smul⟩

lemma zero_has_bound : ∃ (M ≥ 0), is_lin_bound (0 : α →ₗ[ℝ] β) M :=
begin
    use 0,
    use le_refl 0,
    dsimp [is_lin_bound],
    intros x,
    simp,
end

instance bounded_has_zero : has_zero (bounded_linear_operator α β) :=
⟨bounded_linear_operator.mk (0 : α →ₗ[ℝ] β) zero_has_bound⟩

lemma neg_respects_add {T : α →ₗ[ℝ] β} : ∀ (x y : α), - T (x + y) = - T x + - T y :=
by {intros x y, simp}

lemma neg_respects_smul {T : α →ₗ[ℝ] β} : ∀ (c : ℝ), ∀ (x : α), - T (c • x) = c • (- T x) :=
by {intros c x, simp}

instance operators_has_neg : has_neg (α →ₗ[ℝ] β) :=
⟨λ T, linear_map.mk (λ x, - T x) neg_respects_add neg_respects_smul⟩

lemma neg_is_bounded {T : α →ₗ[ℝ] β} (hT : is_lin_bounded T) : is_lin_bounded (-T) :=
begin
    cases hT with M hT,
    cases hT with h hT,
    dsimp [is_lin_bounded, is_lin_bound] at *,
    use M,
    use h,
    simp only [norm_neg],
    exact hT,
end 

instance bounded_has_neg : has_neg (bounded_linear_operator α β) :=
⟨λ T, bounded_linear_operator.mk (-T.T) (neg_is_bounded T.has_bound)⟩ 

instance bounded_has_sub : has_sub (bounded_linear_operator α β) :=
⟨λ T S, T + -S⟩

@[simp] lemma operators_add_assoc : ∀ (T S R : α →ₗ[ℝ] β), (T + S) + R = T + (S + R) :=
by {intros T S R, simp}

@[simp] lemma operators_add_comm : ∀ (T S : α →ₗ[ℝ] β), T + S = S + T :=
by {intros T S, simp}

@[simp] lemma operators_zero_add : ∀ (T : α →ₗ[ℝ] β), 0 + T = T :=
by {intros T, simp}

@[simp] lemma operators_add_left_neg : ∀ (T : α →ₗ[ℝ] β), - T + T = 0 :=
by {intros T, simp}

@[simp] lemma operators_add_zero : ∀ (T : α →ₗ[ℝ] β), T + 0 = T :=
by {intros T, rw [operators_add_comm], exact operators_zero_add T}

instance operators_add_comm_group : add_comm_group (α →ₗ[ℝ] β) :=
{add := (+), add_assoc := operators_add_assoc, zero := 0,
 zero_add := operators_zero_add, add_zero := operators_add_zero,
 neg := has_neg.neg, add_left_neg := operators_add_left_neg,
 add_comm := operators_add_comm}

instance bounded_has_dist : has_dist (bounded_linear_operator α β) := ⟨λ T S, ∥T-S∥⟩

instance operators_has_decidable_eq : decidable_eq (α →ₗ[ℝ] β) := sorry

lemma zero_is_lin_bound_of_zero : 0 ∈ linear_bounds (0 : α →ₗ[ℝ] β) :=
begin
    dsimp [linear_bounds],
    split,

    exact le_refl 0,

    dsimp [is_lin_bound],
    intros x,
    simp,
end

lemma linear_bounds_is_bounded_below (T : α →ₗ[ℝ] β) : ∀ (M : ℝ), M ∈ linear_bounds T → 0 ≤ M :=
begin
    intros M h,
    dsimp [linear_bounds] at h,
    exact h.1,
end

@[simp] lemma operators_norm_zero : ∥(0 : α →ₗ[ℝ] β)∥ = 0 :=
begin
    dsimp [norm],
    have h₁ : ∃ (x : ℝ), x ∈ linear_bounds (0 : α →ₗ[ℝ] β) := begin
        use 0,
        exact zero_is_lin_bound_of_zero,
    end,
    have h₂ : ∃ (x : ℝ), ∀ (y ∈ linear_bounds (0 : α →ₗ[ℝ] β)), x ≤ y := begin
        use 0,
        exact linear_bounds_is_bounded_below (0 : α →ₗ[ℝ] β),
    end,
    have h₃ := (@le_Inf (linear_bounds (0 : α →ₗ[ℝ] β)) h₁ h₂ 0).2 (linear_bounds_is_bounded_below (0 : α →ₗ[ℝ] β)),
    have h₄ := @Inf_le (linear_bounds (0 : α →ₗ[ℝ] β)) h₂ 0 zero_is_lin_bound_of_zero,
    exact (antisymm h₃ h₄).symm,
end

lemma operators_dist_self : ∀ (T : α →ₗ[ℝ] β), dist T T = 0 :=
by {intros T, dsimp [dist], simp}

lemma operators_norm_nonneg : ∀ (T : α →ₗ[ℝ] β), ∥T∥ ≥ 0 :=
begin
    intros T,
    dsimp [norm],
    have w := lb_le_Inf (linear_bounds T),
    sorry,
end

lemma operators_zero_of_norm_zero : ∀ (T : α →ₗ[ℝ] β), ∥T∥ = 0 → T = 0 :=
begin
    intros T h,
    dsimp [norm, linear_bounds] at h,
    ext,
    have w : is_lin_bound T 0 := by sorry,
    dsimp [is_lin_bound] at *,
    have w₁ := w x,
    simp only [zero_mul] at w₁,
    sorry,
end

lemma operators_eq_of_dist_eq_zero : ∀ (T S : α →ₗ[ℝ] β), dist T S = 0 → T = S :=
begin
    intros T S h,
    dsimp [dist] at h,
    have w := congr_arg (λ R, R + S) (operators_zero_of_norm_zero _ h),
    simp at w,
    exact w,
end

lemma linear_bounds_of_neg (T : α →ₗ[ℝ] β) : linear_bounds T = linear_bounds (-T) :=
begin
    ext M,
    dsimp [linear_bounds, is_lin_bound],
    split,

    intros h,
    split,
    exact h.1,
    simp only [norm_neg],
    exact h.2,

    intros h,
    split,
    exact h.1,
    simp only [norm_neg] at h,
    exact h.2,
end

lemma operators_dist_comm : ∀ (T S : α →ₗ[ℝ] β), dist T S = dist S T :=
begin
    intros T S,
    dsimp [dist, norm],
    have h : (T + -S) = -(S + -T) := by simp,
    rw [h, linear_bounds_of_neg (S+-T)],
end

lemma operators_norm_triangle : ∀ (T S : α →ₗ[ℝ] β), ∥T+S∥ ≤ ∥T∥ + ∥S∥ :=
begin
    intros T S,
    sorry,
end

lemma operators_dist_triangle : ∀ (T S R : α →ₗ[ℝ] β), dist T R ≤ dist T S + dist S R :=
begin
    intros T S R,
    dsimp [dist],
    have h := operators_norm_triangle (T+-S) (S+-R),
    simp at h,
    exact h,
end

instance operators_metric_space : metric_space (α →ₗ[ℝ] β) :=
{dist_self := operators_dist_self, eq_of_dist_eq_zero := operators_eq_of_dist_eq_zero,
 dist_comm := operators_dist_comm, dist_triangle := operators_dist_triangle}

lemma operators_dist_eq : ∀ (T S : α →ₗ[ℝ] β), dist T S = ∥T-S∥ :=
by {intros T S, dsimp [dist], refl}

def operators_is_normed_group : normed_group (α →ₗ[ℝ] β) :=
{dist_eq := operators_dist_eq}


end operator_norm