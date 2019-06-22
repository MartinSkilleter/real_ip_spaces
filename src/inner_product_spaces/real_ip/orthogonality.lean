import inner_product_spaces.real_ip.hilbert_space
import linear_algebra.basis
import tactic.interactive

noncomputable theory

variables {α : Type*}

open real set module submodule linear_map set

variables [decidable_eq α] [add_comm_group α] [vector_space ℝ α] [ℝ_inner_product_space α]

section norm_known

def α_normed_space : normed_space ℝ α := ip_space_is_normed_space

local attribute [instance] α_normed_space
local attribute [instance] classical.prop_decidable

def orthog_set (L : set α) : Prop :=
∀ (a b ∈ L), a ≠ b → a ⊥ b

lemma emptyset_orthog : orthog_set (∅ : set α) :=
by {dsimp [orthog_set], simp}

lemma add_elt_to_orthog (L : set α) (x : α) (h : orthog_set L) (w : ∀ (y ∈ L), x ⊥ y) : orthog_set (L ∪ {x}) :=
begin
    dsimp [orthog_set] at *,
    intros a b k₁ k₂ k₃,
    cases k₁,
    cases k₂,

    exact h a b k₁ k₂ k₃,

    apply orthog_symm,
    rw [eq_of_mem_singleton k₂],
    exact w a k₁,

    cases k₂,

    rw [eq_of_mem_singleton k₁],
    exact w b k₂,

    have k₃ := (eq_of_mem_singleton k₂).symm,
    rw [←eq_of_mem_singleton k₁] at k₃,
    contradiction,
end

lemma orthog_subset (L S : set α) (h : orthog_set L) (w : S ⊆ L) : orthog_set S :=
by {dsimp [orthog_set] at *,
    dsimp [(⊆), set.subset] at w,
    intros a b k₁ k₂ k₃,
    exact (h a b (w k₁) (w k₂) k₃)}

def orthonormal (L : set α) : Prop :=
orthog_set L ∧ ∀ (a ∈ L), ∥a∥=1

def normalise (L : set α) := image (λ (a : α), (1/∥a∥ : ℝ) • a) L

lemma elem_of_normalised (L : set α) (x : α) (h : x ∈ normalise L) : ∃ (y ∈ L) (a : ℝ), a • y = x :=
by {dsimp [normalise, image] at h, rcases h with ⟨y, hl, hr⟩,
    use y, use hl, use (1 / ∥y∥), exact hr}

lemma elem_of_normalised' (L : set α) (x : α) (h : x ∈ L) : ((1 / ∥x∥ : ℝ) • x) ∈ normalise L :=
by {dsimp [normalise, image], use x, exact ⟨h, rfl⟩}

lemma norm_one_of_norm_inv (x : α) (h : x ≠ 0) : ∥(1/∥x∥)•x∥ = 1 :=
by {rw [one_div_eq_inv, @norm_smul ℝ α _ ip_space_is_normed_space _ x, norm_inv,
    @norm_norm α ip_space_is_normed_group, inv_mul_cancel],
    exact (@norm_neq_zero_iff_neq_zero α ip_space_is_normed_space x).2 h}

lemma norm_one_of_normalised (L : set α) (h : (0 : α) ∉ L) (a : α) (w : a ∈ normalise L) : ∥a∥=1 :=
begin
    dsimp [normalise] at w,
    simp at w,
    rcases w with ⟨b, k₁, k₂⟩,
    have k₃ : b ≠ 0, begin
        by_contradiction,
        simp only [not_not] at a_1,
        rw [a_1] at k₁,
        contradiction,
    end,
    rw [←k₂, ←one_div_eq_inv],
    exact norm_one_of_norm_inv b k₃,
end

lemma zero_not_elem_of_normalised (L : set α) (h : (0 : α) ∉ L) : (0 : α) ∉ normalise L :=
by {by_contradiction, have w := norm_one_of_normalised L h 0 a, simp at w, exact w}

lemma orthog_normalised_of_orthog (L : set α) (h : orthog_set L) : orthog_set (normalise L) :=
begin
    dsimp [orthog_set] at *,
    dsimp [normalise],
    simp,
    intros a b x k₁ k₂ y k₃ k₄ k₅,
    have k₆ : x ≠ y, begin
        by_contradiction,
        simp only [not_not] at a_1,
        rw [a_1] at k₂,
        rw [k₂] at k₄,
        contradiction,
    end,
    rw [←k₄, ←k₂],
    exact mul_orthog x y (∥x∥)⁻¹ (∥y∥)⁻¹ (h x y k₁ k₃ k₆),
end

lemma orthonormal_normalised_of_orthog_set (L : set α) (h : orthog_set L) (w : (0 : α) ∉ L) : orthonormal (normalise L) :=
by {dsimp [orthonormal], exact ⟨orthog_normalised_of_orthog L h, norm_one_of_normalised L w⟩}

lemma orthog_set_is_lin_indep (L : set α) (h : orthog_set L) (w : (0 : α) ∉ L) : linear_independent ℝ L :=
begin
    rw [linear_independent_iff],
    intros l k₁ k₂,
    -- rw [linear_combination.mem_supported] at k₁,
    sorry,
end

lemma scale_elem_in_span (L : set α) (x : α) (a : ℝ) (h : x ∈ span ℝ L) : (a • x) ∈ span ℝ L :=
by {rw [mem_span] at *, intros p k, exact smul p a (h p k)}

lemma elem_span_of_elem_normalised (L : set α) (x : α) (a : x ∈ normalise L) : x ∈ span ℝ L :=
begin
    have w₁ := elem_of_normalised L x a,
    rcases w₁ with ⟨y, w₁, a, w₂⟩,
    have w₃ := @subset_span ℝ _ _ _ _ _,
    rw [←w₂],
    exact scale_elem_in_span L y a (w₃ w₁),
end

lemma normalised_subset_span (L : set α) : normalise L ⊆ ↑(span ℝ L) := elem_span_of_elem_normalised L

lemma in_submodule_of_normalised_in_submodule (L : set α) (p : submodule ℝ α) (k : normalise L ⊆ ↑p) : L ⊆ ↑p :=
begin
    have w : ∀ (x : α), x ∈ L → x ∈ ↑p := begin
        intros x l,
        by_cases (x = 0),

        rw [mem_coe p, h],
        exact zero_mem p,

        have w₁ := elem_of_normalised' L x l,
        have w₂ := k w₁,
        rw [mem_coe] at w₂,
        have w₃ := smul p (∥x∥) w₂,
        rw [smul_smul, one_div_eq_inv, mul_inv_cancel, one_smul] at w₃,
        rw [mem_coe],
        exact w₃,
        rw [←ne.def] at h,
        exact (norm_neq_zero_iff_neq_zero x).2 h,
    end,
    exact w,
end

lemma span_of_normalised_is_span (L : set α) : span ℝ (normalise L) = span ℝ L :=
begin
    ext,
    rw [mem_span],
    constructor,

    intros h,
    exact (h (span ℝ L)) (normalised_subset_span L),

    intros h p w,
    have h' := mem_span.1 h,
    have h₁ := h' p,
    exact h₁ (in_submodule_of_normalised_in_submodule L p w),
end

def orthonormal_basis (L : set α) := orthonormal L ∧ is_basis ℝ L

theorem normalised_basis_is_orthonormal_basis (L : set α) (h : is_basis ℝ L) (k : orthog_set L) : orthonormal_basis (normalise L) :=
begin
    dsimp [orthonormal_basis, is_basis] at *,
    cases h,
    have w := zero_not_mem_of_linear_independent (@zero_ne_one ℝ _) h_left,
    exact ⟨by {dsimp [orthonormal],
    exact ⟨orthog_normalised_of_orthog L k, norm_one_of_normalised L w⟩},
    by {exact ⟨orthog_set_is_lin_indep _ (orthog_normalised_of_orthog L k) (zero_not_elem_of_normalised L w), 
    by {simpa [span_of_normalised_is_span]}⟩}⟩,
end

-- The Gram-Schimdt Procedure. Never finished defining it because I ended up
-- doing most of my work without fixing a basis.

-- def gram_partial (s : ℕ → α) : ℕ → set α
-- | 0 := {∥s 0∥⁻¹ • s 0}
-- | n := sorry

-- def gram_schmidt (s : ℕ → α) : ℕ → α :=
-- ⋃₀ {L | ∃ (n : ℕ), L = gram_partial s n}

end norm_known

section perp_space

def perp (L : set α) : set α := {x | ∀ (y ∈ L), x ⊥ y}

lemma perp_perp (L : set α) : L ⊆ perp (perp L) :=
begin
    have w : ∀ (x : α), x ∈ L → x ∈ perp (perp L) := begin
        intros x h,
        dsimp [perp],
        intros y k,
        have k₁ := orthog_symm (k x h),
        exact k₁,
    end,
    exact w,
end

lemma perp_antitone (S : set α) (L : set α) (h : S ⊆ L) : perp L ⊆ perp S :=
begin
    have w : ∀ (x : α), x ∈ perp L → x ∈ perp S := begin
        intros x w,
        dsimp [perp] at *,
        intros y k,
        exact w y (h k),
    end,
    exact w,
end

variables {S : set α}

lemma perp_add_closed (x y : α) (hx : x ∈ perp S) (hy : y ∈ perp S) : x + y ∈ perp S :=
begin
    dsimp [perp] at *,
    intros z hz,
    exact add_orthog (hx z hz) (hy z hz),
end

lemma perp_smul_closed (c : ℝ) (x : α) (hx : x ∈ perp S) : c•x ∈ perp S :=
begin
    dsimp [perp] at *,
    intros z hz,
    rw [←one_smul ℝ z],
    exact @mul_orthog α _ _ _ _ x z c 1 (hx z hz),
end

lemma zero_in_perp : (0 : α) ∈ perp S :=
begin
    dsimp [perp],
    intros y h,
    exact right_orthog_to_zero y,
end

def perp_subspace : subspace ℝ α :=
{carrier := perp S,
 zero := zero_in_perp,
 add := perp_add_closed,
 smul := perp_smul_closed}

lemma sub_simp {α : Type*} [add_comm_group α] [vector_space ℝ α] {S : subspace ℝ α} {y : α} : y ∈ S ↔ y ∈ S.carrier :=
by {rw [←submodule.mem_coe], unfold_coes}

lemma perp_singleton_ker (x : α) : perp {x} = (linear_map.ker (ip_map x)).carrier :=
begin
    ext y,
    rw [←sub_simp, mem_ker, ip_map_to_fun],
    dsimp [perp],
    split,

    intros h,
    have h₁ := h x (mem_singleton x),
    dsimp [orthog] at h₁,
    rw [conj_symm] at h₁,
    exact h₁,

    intros h z w,
    have k := eq_of_mem_singleton w,
    dsimp [orthog],
    rw [conj_symm, k],
    exact h,
end

lemma functional_ker_is_preimage_zero {f : α →ₗ[ℝ] ℝ} : (linear_map.ker f).carrier = f⁻¹' {0} :=
by {ext, rw [←sub_simp], simp}

lemma bounded_functional_ker_closed {f : α →ₗ[ℝ] ℝ} {w : @is_bounded_linear_map ℝ _ α ip_space_is_normed_space _ _ f} : @is_closed α α_topological_space (linear_map.ker f).carrier :=
by {rw [@functional_ker_is_preimage_zero α _ _ _ _],
    apply ((@continuous_iff_is_closed α ℝ α_topological_space ℝ_topological_space f).1 (@is_bounded_linear_map.continuous ℝ _ α ip_space_is_normed_space ℝ _ _ w) {0}),
    exact is_closed_singleton}

lemma ip_map_ker_is_preimage_zero (x : α) : (linear_map.ker (ip_map x)).carrier = (ip_map x)⁻¹' {0} :=
functional_ker_is_preimage_zero

lemma ip_map_ker_is_closed (x : α) : @is_closed α α_topological_space (linear_map.ker (ip_map x)).carrier :=
@bounded_functional_ker_closed α _ _ _ _ _ (ip_map_is_bounded_linear_map x)

lemma perp_singleton_closed (x : α) : @is_closed α α_topological_space (perp {x}) :=
by {rw [perp_singleton_ker], exact ip_map_ker_is_closed x}

lemma perp_int_singleton (S : set α) : perp S = ⋂₀ {L | ∃ (a ∈ S), L = perp ({a})} :=
begin
    ext x,
    rw [mem_sInter],
    split,

    intros h t w,
    simp at w,
    cases w with a w,
    cases w,
    dsimp [perp] at *,
    rw [w_right],
    simp,
    exact h a w_left,

    intros h y w,
    simp at h,
    have h₁ := h (perp {y}) y w rfl,
    dsimp [perp] at h₁,
    exact h₁ y (mem_singleton y),
end

lemma perp_int_trivial {l : (0 : α) ∈ S}: S ∩ perp S = {0} :=
begin
    ext,
    split,

    simp,
    intros h w,
    dsimp [perp] at w,
    have k := w x h,
    have k₁ := zero_of_norm_sq_zero x,
    dsimp [norm_sq] at k₁,
    dsimp [orthog] at k,
    exact k₁ k,

    intros h,
    have k := eq_of_mem_singleton h,
    rw [k],
    simp,
    split,
    exact l,
    exact zero_in_perp,
end


lemma perp_singleton_expr (S : set α) {t : set α} (h :t ∈ {L : set α | ∃ (a : α) (H : a ∈ S), L = perp {a}}) : ∃ (a ∈ S), t = perp {a} :=
by {rw [mem_set_of_eq] at h, exact h}

theorem perp_space_closed (S : set α) : @is_closed α α_topological_space (perp S) :=
begin
    rw [perp_int_singleton],
    apply @is_closed_sInter α α_topological_space _,
    intros t h,
    have k := perp_singleton_expr S h,
    rcases k with ⟨a, k₁, k₂⟩,
    rw [k₂],
    exact perp_singleton_closed a,
end

end perp_space

section orthogonal_projection

local attribute [instance] α_normed_space

variables [Hilbert_space α]
variables (S : submodule ℝ α)
variables (h : @is_closed α α_topological_space S.carrier)

include h

theorem proj_exists_unique (x : α) : ∃! (y : α), y ∈ S ∧ (∥x-y∥ = Inf {r | ∃ (z ∈ S), r = ∥x-z∥}) :=
begin
    sorry,
end

def orthog_proj (x : α) := classical.some (exists_of_exists_unique (proj_exists_unique S h x))

lemma orthog_classical (x : α) : orthog_proj S h x = classical.some (exists_of_exists_unique (proj_exists_unique S h x)) := rfl

lemma orthog_proj_mem (x : α) : orthog_proj S h x ∈ S :=
begin
    have w := classical.some_spec (exists_of_exists_unique (proj_exists_unique S h x)),
    rw [←orthog_classical] at w,
    cases w,
    exact w_left,
end

lemma orthog_proj_dist (x : α) : ∥x -  orthog_proj S h x∥ = Inf {r | ∃ (z ∈ S), r = ∥x-z∥} :=
begin
    have w := classical.some_spec (exists_of_exists_unique (proj_exists_unique S h x)),
    rw [←orthog_classical] at w,
    cases w,
    exact w_right,
end

lemma orthog_unique (x y z : α) (w : (y ∈ S ∧ (∥x-y∥ = Inf {r | ∃ (j ∈ S), r = ∥x-j∥})) ∧ (z ∈ S ∧ (∥x-z∥ = Inf {r | ∃ (j ∈ S), r = ∥x-j∥}))) : y = z :=
by {cases w, exact unique_of_exists_unique (proj_exists_unique S h x) w_left w_right}

lemma orthog_proj_suff (x y : α) (w : y ∈ S ∧ (∥x-y∥ = Inf {r | ∃ (z ∈ S), r = ∥x-z∥})) : y = orthog_proj S h x :=
by {apply orthog_unique S h, exact ⟨w, ⟨orthog_proj_mem S h x, orthog_proj_dist S h x⟩⟩}

lemma orthog_proj_suff' (x y : α) (w : y ∈ S ∧ (∥x-y∥ = Inf {r | ∃ (z ∈ S), r = ∥x-z∥})) : orthog_proj S h x = y :=
by {apply symm, exact orthog_proj_suff S h x y w}

lemma dist_bounded_below (x : α): ∃ (l : ℝ), ∀ (y : ℝ), y ∈ {r : ℝ | ∃ (z ∈ S), r = ∥x - z∥} → l ≤ y :=
begin
    use 0,
    intros y,
    simp,
    intros z w₁ w₂,
    rw [w₂],
    exact norm_nonneg _,
end

lemma dist_nonempty (x : α) : (∃ (r : ℝ), r ∈ {r : ℝ | ∃ (z : α) (H : z ∈ S), r = ∥x - z∥}) :=
begin
    use ∥x∥,
    simp,
    use 0,
    exact ⟨zero_mem S, by {simp}⟩,
end

lemma orthog_proj_id_on_S (x : α) (k : x ∈ S) : orthog_proj S h x = x :=
begin
    apply symm,
    apply orthog_proj_suff,
    split,

    exact k,
    simp,
    have w₁ : (0 : ℝ) ∈ {r : ℝ | ∃ (z : α) (H : z ∈ S), r = ∥x - z∥} := begin
        simp,
        use x,
        split,

        exact k,

        simp,
    end,
    have w₂ := @Inf_le {r | ∃ (z ∈ S), r = ∥x-z∥} (dist_bounded_below S h x) 0 w₁,
    have w₃ : (∀ (z : ℝ), z ∈ {r : ℝ | ∃ (z : α) (H : z ∈ S), r = ∥x - z∥} → 0 ≤ z) := begin
        intros z k₁,
        simp at k₁,
        cases k₁,
        cases k₁_h,
        rw [k₁_h_right],
        exact norm_nonneg _,
    end,
    have w₄ := (le_Inf {r | ∃ (z ∈ S), r = ∥x-z∥} (dist_nonempty S h _) (dist_bounded_below S h x)).2 w₃,
    have w₅ := (antisymm w₂ w₄).symm,
    simp at w₅,
    exact w₅,
end

lemma orthog_proj_zero_on_perp_S (x : α) (k : x ∈ perp S.carrier) : orthog_proj S h x = 0 :=
begin
    apply orthog_proj_suff',
    split,

    exact zero_mem S,
    rw [sub_zero],
    have w₁ : ∥x∥ ∈ {r : ℝ | ∃ (z : α) (H : z ∈ S), r = ∥x - z∥} := begin
        simp,
        use 0,
        split,

        exact zero_mem S,

        simp,
    end,
    have w₂ := Inf_le {r | ∃ (z ∈ S), r = ∥x-z∥} (dist_bounded_below S h x) w₁,
    have w₃ : (∃ (r : ℝ), r ∈ {r : ℝ | ∃ (z : α) (H : z ∈ S), r = ∥x - z∥}) := begin
        use ∥x∥,
        exact w₁,
    end,
    have w₄ : (∀ (z : ℝ), z ∈ {r : ℝ | ∃ (z : α) (H : z ∈ S), r = ∥x - z∥} → ∥x∥ ≤ z) := begin
        intros r l,
        simp at l,
        cases l with z l,
        cases l,
        rw ←norm_sqr_leq_iff_norm_leq,

        rw [l_right, pythagoras],
        simp,
        exact (norm_sq_nonneg z),

        dsimp [perp] at k,
        have k₁ := @mul_orthog α _ _ _ _ x z 1 (-1) (k z l_left),
        rw [one_smul, neg_one_smul] at k₁,
        exact k₁,
        rw [l_right],
        exact norm_nonneg _,
    end,
    have w₅ := (le_Inf {r | ∃ (z ∈ S), r = ∥x-z∥} w₃ (dist_bounded_below S h x)).2 w₄,
    exact (antisymm w₂ w₅).symm,
end

lemma orthog_proj_idempotent (x : α) : orthog_proj S h (orthog_proj S h x) = orthog_proj S h x :=
by {apply orthog_proj_id_on_S, exact orthog_proj_mem S h x}

lemma perp_mem_of_orthog_to_units (x : α) (k : ∀ (y ∈ S), ∥y∥=1 → x ⊥ y) : x ∈ perp S.carrier :=
begin
    dsimp [perp, orthog] at *,
    intros y k₁,
    by_cases (y=0),

    rw [h],
    exact left_orthog_to_zero x,

    revert h,
    intros k₂,
    rw [←ne.def] at k₂,
    have w₁ := k ((1/∥y∥) • y) (smul_mem S (1/∥y∥) k₁) (norm_one_of_norm_inv y k₂),
    have w₂ := mul_orthog x _ 1 (∥y∥) w₁,
    rw [one_smul, one_div_eq_inv, ←mul_smul, mul_inv_cancel ((norm_neq_zero_iff_neq_zero y).2 k₂), one_smul] at w₂,
    exact w₂,
end

lemma orthog_of_orthog_proj_sub (x : α) : (x - orthog_proj S h x) ∈ perp S.carrier:=
begin
    apply perp_mem_of_orthog_to_units S h,
    intros y k₁ k₂,
    dsimp [orthog],
    have w₁ : ∥x-orthog_proj S h x∥ ≤ ∥x - (orthog_proj S h x + ⟪y ∥ x - orthog_proj S h x⟫ • y)∥ := begin
        have w₁ := orthog_proj_dist S h x,
        rw [w₁],
        have w₂ : ∥x - (orthog_proj S h x + ⟪y ∥ x - orthog_proj S h x⟫ • y)∥ ∈ {r : ℝ | ∃ (z : α) (H : z ∈ S), r = ∥x - z∥} := begin
            simp,
            existsi orthog_proj S h x + ⟪y ∥ x - orthog_proj S h x⟫ • y,
            split,
            exact add_mem S (orthog_proj_mem S h x) (smul_mem S _ k₁),
            simp,
        end,
        have w₃ := Inf_le {r : ℝ | ∃ (z : α) (H : z ∈ S), r = ∥x - z∥} (dist_bounded_below S h x) w₂,
        exact w₃,
    end,
    have w₂ : ∥x-(orthog_proj S h x + ⟪y ∥ x - orthog_proj S h x⟫•y)∥^2 = ∥x - orthog_proj S h x∥^2 - ⟪y ∥ x - orthog_proj S h x⟫^2 := begin
        sorry,
    end,
    by_contradiction,
    rw [conj_symm, ←ne.def, ←sqr_pos_iff_neq_zero] at a,
    have w₃ : ∥x - orthog_proj S h x∥ ^ 2 - ⟪y ∥ x - orthog_proj S h x⟫ ^ 2 < ∥x-orthog_proj S h x∥^2 := begin
        rw [sub_eq_add_neg],
        conv {to_rhs, rw [←add_zero (∥x - orthog_proj S h x∥ ^ 2)]},
        apply (real.add_lt_add_iff_left (∥x - orthog_proj S h x∥ ^ 2)).2,
        exact neg_lt_zero.2 a,
    end,
    rw [←w₂] at w₃,
    rw [←norm_sqr_leq_iff_norm_leq] at w₁,
    rw [lt_iff_not_ge] at w₃,
    exact absurd w₁ w₃,
    exact norm_nonneg _,
end

lemma orthog_proj_norm_leq (x : α) : ∥orthog_proj S h x∥ ≤ ∥x∥ :=
begin
    have k₁ := orthog_of_orthog_proj_sub S h x,
    dsimp [perp] at k₁,
    have w := pythagoras (k₁ (orthog_proj S h x) (orthog_proj_mem S h x)),
    rw [add_assoc, add_left_neg, add_zero, add_comm] at w,
    rw [←@norm_sqr_leq_iff_norm_leq _ _ _ _ (norm_nonneg _)],
    exact @leq_of_add_nonneg _ _ _ (sqr_nonneg _) (sqr_nonneg _) (sqr_nonneg _) w,
end

lemma orthog_proj_has_bound : ∃ M > 0, ∀ x : α, ∥orthog_proj S h x ∥ ≤ M * ∥ x ∥ :=
begin
    use 1,
    use zero_lt_one,
    intros x,
    rw [one_mul],
    exact orthog_proj_norm_leq S h x,
end

theorem orthog_direct_sum_exists (x : α) : ∃ (u ∈ S), ∃ (v ∈ perp S.carrier), x = u + v :=
begin
    use orthog_proj S h x,
    use orthog_proj_mem S h x,
    use (x-orthog_proj S h x),
    use orthog_of_orthog_proj_sub S h x,
    simp,
end

theorem orthog_direct_sum_unique (x u₁ u₂ v₁ v₂ : α) (U₁ : u₁ ∈ S) (U₂ : u₂ ∈ S) (V₁ : v₁ ∈ perp S.carrier) (V₂ : v₂ ∈ perp S.carrier)
(k₁ : x = u₁ + v₁) (k₂ : x = u₂ + v₂) : (u₁ = u₂ ∧ v₁ = v₂) :=
begin
    rw [k₁] at k₂,
    have k₃ : u₁ - u₂ = v₂ - v₁ := begin
        have l₁ := congr_arg (λ (z : α), z - u₂ - v₁) k₂,
        simp at l₁,
        rw [sub_eq_add_neg],
        exact l₁,
    end,
    have w₁ := sub_mem S U₁ U₂,
    have w₂ := @sub_mem ℝ α _ _ _ (@perp_subspace α _ _ _ _ S.carrier) v₂ v₁ V₂ V₁,
    have w₃ : u₁ - u₂ ∈ S.carrier ∩ perp S.carrier := begin
        split,
        exact w₁,
        rw [k₃],
        exact w₂,
    end,
    rw [@perp_int_trivial α _ _ _ _ S.carrier (zero_mem S)] at w₃,
    have w₄ := sub_eq_zero.1 (eq_of_mem_singleton w₃),
    rw [k₃] at w₃,
    exact ⟨w₄, (sub_eq_zero.1 (eq_of_mem_singleton w₃)).symm⟩,
end

theorem orthog_proj_of_orthog_direct_sum (x u v : α) (U : u ∈ S) (V : v ∈ perp S.carrier) (k : x = u + v) : orthog_proj S h x = u :=
begin
    have w₁ := orthog_direct_sum_unique S h x u (orthog_proj S h x) v (x - orthog_proj S h x) U (orthog_proj_mem S h x) V (orthog_of_orthog_proj_sub S h x) k (by simp),
    cases w₁,
    exact (w₁_left).symm,
end

lemma orthog_proj_add (x y : α) : orthog_proj S h (x+y) = orthog_proj S h x + orthog_proj S h y :=
begin
    have w₁ := orthog_direct_sum_exists S h x,
    rcases w₁ with ⟨ux, Ux, vx, Vx, w₁⟩,
    have w₂ := orthog_direct_sum_exists S h y,
    rcases w₂ with ⟨uy, Uy, vy, Vy, w₂⟩,
    have w₃ := orthog_proj_of_orthog_direct_sum S h x ux vx Ux Vx w₁,
    have w₄ := orthog_proj_of_orthog_direct_sum S h y uy vy Uy Vy w₂,
    rw [w₃, w₄],
    have w₅ : x + y = (ux + uy) + (vx + vy) := begin
        rw [w₁, w₂],
        simp,
    end,
    exact (orthog_proj_of_orthog_direct_sum S h (x+y) (ux+uy) (vx+vy) (add_mem S Ux Uy) (add_mem (perp_subspace) Vx Vy) w₅),
end

lemma orthog_proj_smul (c : ℝ) (x : α) : orthog_proj S h (c • x) = c • (orthog_proj S h x) :=
begin
    have w₁ := orthog_direct_sum_exists S h x,
    rcases w₁ with ⟨u, U, v, V, w₁⟩,
    have w₂ := orthog_proj_of_orthog_direct_sum S h x u v U V w₁,
    rw [w₂],
    have w₃ : c•x = c•u + c•v := begin
        rw [←smul_add, w₁],
    end,
    have w₅ := orthog_proj_of_orthog_direct_sum S h (c•x) (c•u) (c•v) (smul_mem S c U) (smul_mem (@perp_subspace α _ _ _ _ S.carrier) c V) w₃,
    rw [w₅],
end

def orthog_proj_linear : is_linear_map ℝ (orthog_proj S h) :=
{add := orthog_proj_add S h, smul := orthog_proj_smul S h}

lemma perp_of_orthog_proj_zero (x : α) (w : orthog_proj S h x = 0) : x ∈ perp S.carrier :=
begin
    have w₁ := orthog_direct_sum_exists S h x,
    rcases w₁ with ⟨u, U, v, V, w₁⟩,
    dsimp [perp, orthog] at *,
    intros y k,
    rw [w₁, add_left],
    have w₂ := orthog_proj_of_orthog_direct_sum S h x u v U V w₁,
    rw [w] at w₂,
    rw [←w₂, right_orthog_to_zero, zero_add],
    exact V y k,
end

theorem ker_orthog_img : (linear_map.ker (is_linear_map.mk' (orthog_proj S h) (orthog_proj_linear S h))).carrier = @perp α _ _ _ _ (linear_map.range ((is_linear_map.mk' (orthog_proj S h) (orthog_proj_linear S h)))).carrier :=
begin
    ext,
    rw [←sub_simp, mem_ker],
    split,

    intros k,
    dsimp [perp],
    intros y w,
    rw [←sub_simp] at w,
    simp at w,
    cases w with z w,
    simp at k,
    have w₁ := perp_of_orthog_proj_zero S h x k,
    have w₂ := orthog_proj_mem S h z,
    rw [w] at w₂,
    dsimp [perp] at w₁,
    exact w₁ y w₂,

    dsimp [perp],
    intros w,
    apply orthog_proj_zero_on_perp_S,
    dsimp [perp],
    intros y k,
    have w₁ := orthog_proj_id_on_S S h y k,
    have w₂ := w y,
    rw [←sub_simp] at w₂,
    simp at w₂,
    exact w₂ y w₁,
end

lemma orthog_proj_is_symmetric (x y : α) : ⟪orthog_proj S h x ∥ y⟫ = ⟪x ∥ orthog_proj S h y⟫ :=
begin
    have w₁ := orthog_direct_sum_exists S h x,
    rcases w₁ with ⟨u₁, U₁, v₁, V₁, w₁⟩,
    have w₂ := orthog_direct_sum_exists S h y,
    rcases w₂ with ⟨u₂, U₂, v₂, V₂, w₂⟩,
    rw [w₁, w₂],
    simp [orthog_proj_add],
    dsimp [perp] at *,
    have k₁ := V₂ (orthog_proj S h u₁) (orthog_proj_mem S h u₁),
    have k₂ := orthog_proj_zero_on_perp_S S h v₁ V₁,
    have k₃ := orthog_proj_zero_on_perp_S S h v₂ V₂,
    have k₄ := V₁ (orthog_proj S h u₂) (orthog_proj_mem S h u₂),
    dsimp [orthog] at *,
    rw [conj_symm] at k₁,
    rw [k₁, zero_add, k₂, right_orthog_to_zero, right_orthog_to_zero, add_zero, add_zero,
        k₃, left_orthog_to_zero, left_orthog_to_zero, add_zero, zero_add, k₄, add_zero,
        orthog_proj_id_on_S S h u₁ U₁, orthog_proj_id_on_S S h u₂ U₂],
end

lemma orthog_proj_is_bounded_linear_map : is_bounded_linear_map ℝ (orthog_proj S h) :=
begin
    constructor,

    constructor,
    exact orthog_proj_add S h,
    exact orthog_proj_smul S h,

    exact orthog_proj_has_bound S h,
end

end orthogonal_projection

section riesz_representation

local attribute [instance] classical.prop_decidable

variables (f : α →ₗ[ℝ] ℝ)

lemma fun_coe : ⇑f = f.to_fun := rfl

variables [Hilbert_space α]
variables (S : @submodule ℝ α _ _ _)

lemma perp_trivial_of_subspace_all (h : @is_closed α α_topological_space S.carrier) (k₁ : ∀ (x : α), x ∈ S) (y : α) (k₂ : y ∈ perp S.carrier) : y = 0 :=
by {dsimp [perp] at k₂, exact zero_of_orthog_self (k₂ y (k₁ y))}

lemma perp_nonempty_of_subspace_not_all (h : @is_closed α α_topological_space S.carrier) : (∃ (x : α), x ∉ S) → (∃ (y : α), y ≠ 0 ∧ y ∈ perp S.carrier) :=
begin
    rw [awesome_mt],
    simp,
    intros k,
    intros x,
    have k₁ := orthog_direct_sum_exists S h x,
    rcases k₁ with ⟨u, ⟨U, ⟨v, ⟨V, k₁⟩⟩⟩⟩,
    rw [k₁],
    have k₂ := k v,
    rw [awesome_mt] at k₂,
    simp at k₂,
    have k₃ := k₂ V,
    rw [k₃, add_zero],
    exact U,
end

lemma perp_nonempty_of_subspace_not_all' (h : @is_closed α α_topological_space S.carrier) (k : ∃ (x : α), x ∉ S) : ∃ (y : α), ∥y∥=1 ∧ y ∈ perp S.carrier :=
begin
    have k₁ := perp_nonempty_of_subspace_not_all S h k,
    rcases k₁ with ⟨z, k₁, k₂⟩,
    use ((1/∥z∥)•z),
    exact ⟨norm_one_of_norm_inv z k₁, smul_mem perp_subspace (1/∥z∥) k₂⟩,
end

theorem riesz_rep_exists (w : @is_bounded_linear_map ℝ _ α ip_space_is_normed_space _ _ f) : ∃ (x : α), f.to_fun = ip_map x :=
begin
    have w₁ := @bounded_functional_ker_closed α _ _ _ _ f w,
    have w₂ := orthog_direct_sum_exists (linear_map.ker f) w₁,
    by_cases k : (∀ (x : α), x ∈ linear_map.ker f),

    use 0,
    ext,
    simp,
    have w₃ := w₂ x,
    cases w₃ with u w₃,
    cases w₃ with w₃ w₄,
    cases w₄ with v w₄,
    cases w₄ with w₄ w₅,
    rw [w₅, linear_map.add],
    simp at w₃,
    rw [fun_coe] at w₃,
    simp [w₃],
    have w₆ := perp_trivial_of_subspace_all (linear_map.ker f) w₁ k v w₄,
    rw [w₆],
    exact linear_map.map_zero f,

    rw [not_forall] at k,
    have k₁ := perp_nonempty_of_subspace_not_all' (linear_map.ker f) w₁ k,
    rcases k₁ with ⟨z, ⟨k₁, k₂⟩⟩,
    use ((f z) • z),
    ext,
    have k₃ : (f x) • z - (f z) • x ∈ linear_map.ker f := begin
        simp,
        ring,
    end,
    dsimp [perp] at k₂,
    rw [←mul_one (f.to_fun x), ←mul_one ((f.to_fun x)*1), mul_assoc, ←pow_two, ←k₁, sqr_norm],
    dsimp [norm_sq],
    rw [←mul_left, ←add_zero (f.to_fun x • z), ←add_left_neg (f.to_fun z • x), ←add_assoc,
    add_left],
    have k₄ := k₂ _ k₃,
    dsimp [orthog] at k₄,
    rw [conj_symm, fun_coe] at k₄,
    rw [k₄, zero_add, fun_coe, mul_left, conj_symm, ←mul_left],
end

theorem riesz_rep_unique {x y : α} (h : f.to_fun = ip_map x) (w : f.to_fun = ip_map y) : x = y :=
begin
    apply left_ext x y,
    intros z,
    rw [h, fun_coe, fun_coe] at w,
    dsimp [ip_map] at w,
    have k₁ := @congr_arg _ _ z z (λ z, inner_product x z) rfl,
    conv at k₁ {to_rhs, rw [w]},
    exact k₁,
end

end riesz_representation

section adjoint

variables (f : α →ₗ[ℝ] α)
variables (h : @is_bounded_linear_map ℝ _ α ip_space_is_normed_space α ip_space_is_normed_space f)
variables [Hilbert_space α]

include f h

def adjoint_map (y : α): α →ₗ[ℝ] ℝ :=
begin
    refine_struct {..},
    use (λ x, ⟪f x ∥ y⟫),
    repeat {simp},
end

lemma adjoint_map_fun (y : α) : (adjoint_map f h y).to_fun = λ x, ⟪f.to_fun x ∥ y⟫ := rfl

lemma adjoint_map_bounded (y : α) : @is_bounded_linear_map ℝ _ α ip_space_is_normed_space _ _ (adjoint_map f h y) :=
begin
    constructor,

    constructor,
    repeat {simp},

    have h₁ := @is_bounded_linear_map.bound ℝ _ α ip_space_is_normed_space α ip_space_is_normed_space f h,
    by_cases (y=0),

    use 1,
    use zero_lt_one,
    intros x,
    have w₁ : (λ (x : α), ⟪f.to_fun x ∥ 0⟫) x = ⟪f.to_fun x ∥ 0⟫ := rfl,
    rw [fun_coe, adjoint_map_fun, h, w₁, left_orthog_to_zero, norm_zero, one_mul],
    apply norm_nonneg _,

    rcases h₁ with ⟨M, H, h₁⟩,
    use M*∥y∥,
    have w₁ : ∥y∥>0 := sorry,
    use mul_pos H w₁,
    intros x,
    apply le_trans (cauchy_schwarz (f x) y),
    rw [mul_assoc, mul_comm ∥y∥, ←mul_assoc],
    apply (mul_le_mul_right w₁).2,
    exact h₁ x,
end

def adjoint_to_fun : α → α :=
λ y, classical.some (riesz_rep_exists (adjoint_map f h y) (adjoint_map_bounded f h y))

lemma adjoint_ip_switch (x y : α) : ⟪f x ∥ y⟫ = ⟪x ∥ adjoint_to_fun f h y⟫ :=
begin
    have w := classical.some_spec (riesz_rep_exists (adjoint_map f h y) (adjoint_map_bounded f h y)),
    have k := adjoint_map_fun f h y,
    rw [w] at k,
    simp at k,
    dsimp [adjoint_to_fun],
    have k' := @congr_arg _ _ x x (λ (x : α), ⟪f.to_fun x ∥ y⟫) rfl,
    conv at k' {to_rhs, rw [←k, conj_symm]},
    exact k',
end

lemma adjoint_ip_switch' (x y : α) : ⟪adjoint_to_fun f h x ∥ y⟫ = ⟪x ∥ f y⟫ :=
by {rw [conj_symm, ←adjoint_ip_switch, conj_symm]}

lemma adjoint_to_fun_unique (S : α → α) (w : ∀ (x y : α), ⟪f x ∥ y⟫ = ⟪x ∥ S y⟫) : S = adjoint_to_fun f h :=
begin
    ext,
    apply @left_ext α _ _ _ _ _ _,
    intros z,
    have w' := w z x,
    have k := (adjoint_ip_switch f h) z x,
    rw [w', conj_symm, conj_symm z] at k,
    exact k,
end

lemma adjoint_to_fun_add (x y : α) : adjoint_to_fun f h (x+y) = adjoint_to_fun f h x + adjoint_to_fun f h y :=
begin
    apply @left_ext α _ _ _ _ _ _,
    intros z,
    rw [add_left, adjoint_ip_switch', adjoint_ip_switch', adjoint_ip_switch', add_left],
end

lemma adjoint_to_fun_smul (c : ℝ) (x : α) : adjoint_to_fun f h (c • x) = c • adjoint_to_fun f h x :=
begin
    apply @left_ext α _ _ _ _ _ _,
    intros z,
    rw [adjoint_ip_switch', mul_left, mul_left, adjoint_ip_switch'],
end

def adjoint : α →ₗ[ℝ] α :=
{to_fun := adjoint_to_fun f h, add := adjoint_to_fun_add f h, smul := adjoint_to_fun_smul f h}

local attribute [instance] α_normed_space

lemma adjoint_fun : (adjoint f h).to_fun = adjoint_to_fun f h := rfl

lemma adjoint_bounded : @is_bounded_linear_map ℝ _ α ip_space_is_normed_space α ip_space_is_normed_space (adjoint f h):=
begin
    constructor,
    constructor,
    exact adjoint_to_fun_add f h,
    exact adjoint_to_fun_smul f h,

    have w := h.bound,
    rcases w with ⟨M, H, w⟩,
    use M,
    use H,

    have k : ∀ (x y : α), ∥⟪adjoint_to_fun f h x ∥ y⟫∥≤M*∥x∥*∥y∥ := begin
        intros x y,
        rw [adjoint_ip_switch'],
        apply le_trans (cauchy_schwarz x _),
        have k := w y,
        by_cases (x=0),

        revert h,
        intros l,
        rw [l, norm_zero, zero_mul, mul_zero, zero_mul],

        revert h,
        intros l,
        rw [←ne.def] at l,
        rw [mul_comm, mul_assoc, mul_comm ∥x∥, ←mul_assoc],
        apply (mul_le_mul_right ((norm_pos_iff x).2 l)).2,
        exact k,
    end,
    intros x,
    by_cases (∥(adjoint f h).to_fun x∥ = 0),
    have k₁ : 0 ≤ M * ∥x∥ := mul_nonneg (le_of_lt H) (norm_nonneg x),
    rw [←h] at k₁,
    exact k₁,

    revert h,
    intros l,
    rw [←ne.def] at l,
    have k₁ := k x (adjoint_to_fun f h x),
    have k₂ := @sqr_norm α _ _ _ _ (adjoint_to_fun f h x),
    dsimp [norm_sq] at k₂,
    rw [←k₂, norm_sqr_eq_sqr, pow_two] at k₁,
    have k₄ := mul_le_mul_of_nonneg_right k₁ ((inv_nonneg.mpr (norm_nonneg (adjoint_to_fun f h x)))),
    rw [mul_assoc, mul_inv_cancel, mul_one, mul_assoc, mul_inv_cancel, mul_one] at k₄,
    exact k₄,
    rw [adjoint_fun] at l,
    repeat {exact l},
end

lemma adjoint_unique (S : α →ₗ[ℝ] α) (k : ∀ (x y : α), ⟪f x ∥ y⟫ = ⟪x ∥ S y⟫) : S = adjoint f h :=
begin
    ext,
    have k₁ := adjoint_to_fun_unique f h _ k,
    simp only [] at k₁,
    rw [k₁, ←adjoint_fun],
    refl,
end

lemma adjoint_is_involution : adjoint (adjoint f h) (adjoint_bounded f h) = f :=
begin
    apply eq.symm,
    apply adjoint_unique _ _,
    intros x y,
    exact adjoint_ip_switch' f h x y,
end

end adjoint


