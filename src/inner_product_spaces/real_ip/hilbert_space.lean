import inner_product_spaces.real_ip.ip_normed_space
import linear_algebra.basic
import analysis.normed_space.bounded_linear_maps

noncomputable theory

variables {α : Type*} {β : Type*}
variables [decidable_eq α] [add_comm_group α] [vector_space ℝ α] [ℝ_inner_product_space α]
variables [decidable_eq β] [add_comm_group β] [vector_space ℝ β] [ℝ_inner_product_space β]

open real

def ℝ_topological_space : topological_space ℝ := by apply_instance

def α_uniform_space : uniform_space α :=
begin
    have w := @ip_space_is_metric_space α _ _ _ _,
    exact @metric_space.to_uniform_space α w,
end

def α_topological_space : topological_space α := @uniform_space.to_topological_space α α_uniform_space

section riesz_representation

def ip_map (x : α) : linear_map ℝ α ℝ :=
begin
    constructor,
    swap 3,
    use λ y, x†y,
    repeat {simp},
end
.

@[simp] lemma ip_map_to_fun (x : α) : ⇑(ip_map x) = λ y, x † y := rfl

theorem ip_map_is_bounded_linear_map (x : α) : @is_bounded_linear_map ℝ _ α (ip_space_is_normed_space) ℝ _ (ip_map x) :=
begin
    constructor,
    constructor,
    repeat {simp},

    by_cases (x = 0),

    use 1,
    split,
    linarith,
    intros y,
    rw [h],
    simp,

    use ∥x∥,
    split,
    have w := (@norm_neq_zero_iff_neq_zero α (ip_space_is_normed_space) x).2 h,
    have α_normed_group : normed_group α := begin
        have w := @ip_space_is_normed_space α _ _ _ _,
        exact @normed_space.to_normed_group ℝ α _ w,
    end,
    have k := (@norm_pos_iff α α_normed_group x).2,
    sorry,
    intros y,
    simp,
end

lemma ip_map_is_continuous (x : α) : @continuous α _ (α_topological_space) (ℝ_topological_space) (ip_map x) :=
@is_bounded_linear_map.continuous ℝ _ α (ip_space_is_normed_space) ℝ _ _ (ip_map_is_bounded_linear_map x)

variables {f : α →ₗ[ℝ] ℝ}

lemma fun_coe (x : α) : ⇑f = f.to_fun := rfl

def is_riesz_rep (f : α →ₗ[ℝ] ℝ) (x : α) := f.to_fun = ip_map x

theorem riesz_rep_exists : @is_bounded_linear_map ℝ _ α (ip_space_is_normed_space) _ _ f → (∃ (x : α), is_riesz_rep f x) :=
begin
    intros h,
    have h' := @is_bounded_linear_map.continuous ℝ _ α (ip_space_is_normed_space) ℝ _ _ h,
    sorry,
end

theorem riesz_rep_unique {x y : α} : is_riesz_rep f x → is_riesz_rep f y → x = y :=
begin
    intros h w,
    dsimp [is_riesz_rep] at *,
    have k := @ip_all_unique α _,
    apply k,
    intros z,
    rw [h] at w,
    have k₁ := @congr_arg _ _ z z (λ z, inner_product x z) rfl,
    conv at k₁ {to_rhs, rw [w]},
    exact k₁,
end

end riesz_representation

section hilbert_space

class Hilbert_space (α : Type*) [decidable_eq α] [add_comm_group α] [vector_space ℝ α] extends ℝ_inner_product_space α :=
(complete : ∀ {f : filter α}, (@cauchy α (@α_uniform_space α _ _ _ _)) f → ∃x, f ≤ @nhds α (@α_topological_space α _ _ _ _) x)

end hilbert_space

section orthogonal_projection



end orthogonal_projection