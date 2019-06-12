import inner_product_spaces.real_ip.ip_normed_space
import linear_algebra.basic
import analysis.normed_space.bounded_linear_maps

noncomputable theory

variables {α : Type*} {β : Type*}
variables [decidable_eq α] [add_comm_group α] [vector_space ℝ α] [ℝ_inner_product_space α]
variables [decidable_eq β] [add_comm_group β] [vector_space ℝ β] [ℝ_inner_product_space β]

open real function

def ℝ_topological_space : topological_space ℝ := by apply_instance

def α_uniform_space : uniform_space α :=
begin
    have w := @ip_space_is_metric_space α _ _ _ _,
    exact @metric_space.to_uniform_space α w,
end

def α_topological_space : topological_space α := @uniform_space.to_topological_space α α_uniform_space

section ip_map

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
    exact zero_lt_one,
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
    rw [ne.def] at k,
    sorry,
    intros y,
    exact cauchy_schwarz,
end

lemma ip_map_is_continuous (x : α) : @continuous α _ (α_topological_space) (ℝ_topological_space) (ip_map x) :=
@is_bounded_linear_map.continuous ℝ _ α (ip_space_is_normed_space) ℝ _ _ (ip_map_is_bounded_linear_map x)

end ip_map

section hilbert_space

class Hilbert_space (α : Type*) [decidable_eq α] [add_comm_group α] [vector_space ℝ α] extends ℝ_inner_product_space α :=
(complete : ∀ {f : filter α}, (@cauchy α (@α_uniform_space α _ _ _ _)) f → ∃x, f ≤ @nhds α (@α_topological_space α _ _ _ _) x)

variables [Hilbert_space α] [Hilbert_space β]

structure unitary_operator (α : Type*) (β : Type*) [decidable_eq α] [add_comm_group α] [vector_space ℝ α] [ℝ_inner_product_space α] [Hilbert_space α]
[decidable_eq β] [add_comm_group β] [vector_space ℝ β] [ℝ_inner_product_space β] [Hilbert_space β] extends linear_map ℝ α β :=
(bijective : bijective to_fun)
(norm_preserving : ∀ (x : α), ∥to_fun x∥ = ∥x∥)

variables {T : unitary_operator α β}

@[simp] lemma norm_preserving (x : α) : ∥T.to_fun x∥ = ∥x∥ :=
by apply unitary_operator.norm_preserving

lemma polarisation_identity (x y : α) : x†y = 1/4*(∥x+y∥^2 - ∥x-y∥^2) :=
begin
    conv {to_lhs, rw [←one_mul (x†y), ←@inv_mul_cancel _ _ (4 : ℝ) four_ne_zero]},
    rw [←one_div_eq_inv, mul_assoc],
    apply congr_arg (λ (r : ℝ), 1/4 * r),
    dsimp [norm],
    rw [sqr_sqrt (ip_self_nonneg _), sqr_sqrt (ip_self_nonneg _)],
    dsimp [ip_self],
    repeat {rw [add_in_fst_coord]},
    repeat {rw [add_in_snd_coord]},
    rw [←neg_one_smul ℝ y],
    repeat {rw [mul_in_fst_coord]},
    repeat {rw [mul_in_snd_coord]},
    rw [conj_symm y x],
    ring,
end

@[simp] theorem ip_preserving (x y : α) : (T.to_fun x) † (T.to_fun y) = x†y :=
begin
    rw [polarisation_identity (T.to_fun x) (T.to_fun y), ←linear_map.add, 
        sub_eq_add_neg (T.to_fun x) (T.to_fun y), ←neg_one_smul ℝ (T.to_fun y),
        ←linear_map.smul, ←linear_map.add, norm_preserving, norm_preserving,
        neg_one_smul, ←sub_eq_add_neg, ←polarisation_identity],
end

end hilbert_space