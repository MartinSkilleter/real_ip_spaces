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
begin
    dsimp [orthog_set],
    simp,
end

lemma add_elt_to_orthog (L : set α) (x : α) (h : orthog_set L) (w : ∀ (y ∈ L), x ⊥ y) : orthog_set (L ∪ {x}) :=
begin
    dsimp [orthog_set] at *,
    intros a b k₁ k₂ k₃,
    cases k₁,
    cases k₂,

    exact h a b k₁ k₂ k₃,

    have k₄ := w a k₁,
    apply orthog_symm,
    have k₅ := eq_of_mem_singleton k₂,
    rw [k₅],
    exact k₄,

    cases k₂,

    have k₄ := eq_of_mem_singleton k₁,
    have k₅ := w b k₂,
    rw [←k₄] at k₅,
    exact k₅,

    have k₄ := eq_of_mem_singleton k₁,
    have k₅ := (eq_of_mem_singleton k₂).symm,
    rw [←k₄] at k₅,
    contradiction,
end

lemma orthog_subset (L S : set α) (h : orthog_set L) (w : S ⊆ L) : orthog_set S :=
begin
    dsimp [orthog_set] at *,
    dsimp [(⊆), set.subset] at w,
    intros a b k₁ k₂ k₃,
    exact (h a b (w k₁) (w k₂) k₃),
end

def orthonormal (L : set α) : Prop :=
orthog_set L ∧ ∀ (a ∈ L), ∥a∥=1

def normalise (L : set α) := image (λ (a : α), (1/∥a∥ : ℝ) • a) L

lemma elem_of_normalised (L : set α) (x : α) : x ∈ normalise L → ∃ (y ∈ L) (a : ℝ), a • y = x :=
begin
    intros h,
    dsimp [normalise, image] at h,
    cases h with y h,
    cases h,
    use y,
    use h_left,
    use (1 / ∥y∥),
    exact h_right,
end

lemma elem_of_normalised' (L : set α) (x : α) : (x ∈ L) → (((1 / ∥x∥ : ℝ) • x) ∈ normalise L) :=
begin
    intros h,
    dsimp [normalise, image],
    use x,
    split,

    exact h,
    refl,
end

lemma norm_one_of_norm_inv (x : α) : x ≠ 0 → ∥(1/∥x∥)•x∥ = 1 :=
begin
    intros h,
    rw [one_div_eq_inv, @norm_smul ℝ α _ (ip_space_is_normed_space) _ x, norm_inv,
    @norm_norm α (ip_space_is_normed_group), inv_mul_cancel],
    exact (@norm_neq_zero_iff_neq_zero α (ip_space_is_normed_space) x).2 h,
end

lemma norm_one_of_normalised (L : set α) (h : (0 : α) ∉ L) : ∀ (a ∈ (normalise L)), ∥a∥=1 :=
begin
    intros a w,
    dsimp [normalise] at w,
    simp at w,
    cases w with b k₁,
    cases k₁ with k₁ k₂,
    have k₃ : b ≠ 0, begin
        by_contradiction,
        simp only [not_not] at a_1,
        rw [a_1] at k₁,
        contradiction,
    end,
    rw [←k₂, ←one_div_eq_inv],
    exact norm_one_of_norm_inv b k₃,
end

lemma zero_not_elem_of_normalised (L : set α) : (0 : α) ∉ L → (0 : α) ∉ normalise L :=
begin
    intros h,
    by_contradiction,

    have w := norm_one_of_normalised L h 0 a,
    simp at w,
    exact w,
end

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
    have k₇ := h x y k₁ k₃ k₆,
    have k₈ := @mul_orthog _ _ _ _ _ x y (∥x∥)⁻¹ (∥y∥)⁻¹ k₇,
    rw [k₂, k₄] at k₈,
    exact k₈,
end

lemma orthonormal_normalised_of_orthog_set (L : set α) (h : orthog_set L) (w : (0 : α) ∉ L) : orthonormal (normalise L) :=
begin
    dsimp [orthonormal],
    split,
    exact (orthog_normalised_of_orthog L h),
    exact (norm_one_of_normalised L w),
end

lemma orthog_set_is_lin_indep (L : set α) (h : orthog_set L) (w : (0 : α) ∉ L) : linear_independent ℝ L :=
begin
    rw [linear_independent_iff],
    intros l k₁ k₂,
    -- rw [linear_combination.mem_supported] at k₁,
    sorry,
end

lemma scale_elem_in_span (L : set α) (x : α) (a : ℝ) : x ∈ span ℝ L → (a • x) ∈ span ℝ L :=
begin
    intros h,
    rw [mem_span] at *,
    intros p k,
    have w := h p k,
    have l := smul p a w,
    exact l,
end

lemma normalised_subset_span (L : set α) : normalise L ⊆ ↑(span ℝ L) :=
begin
    have w : ∀ (x : α), (x ∈ normalise L) → x ∈ ↑(span ℝ L) := begin
        intros x a,
        have w₁ := elem_of_normalised L x a,
        cases w₁ with y w₁,
        cases w₁ with w₁ w₂,
        cases w₂ with a w₂,
        have w₃ := @subset_span ℝ _ _ _ _ _,
        have w₄ := w₃ w₁,
        have w₅ := scale_elem_in_span L y a w₄,
        rw [w₂] at w₅,
        exact w₅,
    end,
    exact w,
end

lemma in_submodule_of_normalised_in_submodule (L : set α) (p : submodule ℝ α) : (normalise L ⊆ ↑p) → L ⊆ ↑p :=
begin
    intros k,
    have w : ∀ (x : α), x ∈ L → x ∈ ↑p := begin
        intros x l,
        by_cases (x = 0),

        rw [mem_coe p, h],
        exact zero_mem p,

        have w₁ := elem_of_normalised' L x l,
        have w₂ := k w₁,
        rw [mem_coe] at w₂,
        have w₃ := smul p (∥x∥) w₂,
        simp [smul_smul] at w₃,
        have w₄ := ((norm_neq_zero_iff_neq_zero x).2 h),
        have w₅ := div_self w₄,
        have w₆ : ∥x∥/∥x∥ = ∥x∥*(∥x∥)⁻¹ := begin
            rw [←mul_one ∥x∥, mul_div_assoc ∥x∥ (1 : ℝ), one_div_eq_inv],
            simp,
            recover,
            repeat {apply_instance},
        end,
        rw [←w₆, w₅, one_smul] at w₃,
        rw [mem_coe],
        exact w₃,
    end,
    exact w,
end

lemma span_of_normalised_is_span (L : set α) : span ℝ (normalise L) = span ℝ L :=
begin
    ext,
    rw [mem_span],
    split,

    intros h,
    exact (h (span ℝ L)) (normalised_subset_span L),
    
    intros h p w,
    have h' := mem_span.1 h,
    have h₁ := h' p,
    clear h',
    exact h₁ (in_submodule_of_normalised_in_submodule L p w),
end

def orthonormal_basis (L : set α) := orthonormal L ∧ is_basis ℝ L

theorem normalised_basis_is_orthonormal_basis (L : set α) : is_basis ℝ L → orthog_set L → orthonormal_basis (normalise L) :=
begin
    intros h k,
    dsimp [orthonormal_basis, is_basis] at *,
    cases h,
    have w := zero_not_mem_of_linear_independent (@zero_ne_one ℝ _) h_left,
    split,
    
    dsimp [orthonormal],
    split,
    exact orthog_normalised_of_orthog L k,
    
    exact norm_one_of_normalised L w,

    split,

    have h₁ := orthog_normalised_of_orthog L k,
    have h₂ := zero_not_elem_of_normalised L w,
    exact orthog_set_is_lin_indep _ h₁ h₂,

    rw [←span_of_normalised_is_span L] at h_right,
    exact h_right,
end

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

lemma perp_antitone (S : set α) (L : set α) : S ⊆ L → perp L ⊆ perp S :=
begin
    intros h,
    have w : ∀ (x : α), x ∈ perp L → x ∈ perp S := begin
        intros x w,
        dsimp [perp] at *,
        intros y k,
        exact w y (h k),
    end,
    exact w,
end

variables {S : set α}

lemma perp_add_closed (x y : α) : x ∈ perp S → y ∈ perp S → x + y ∈ perp S :=
begin
    intros hx hy,
    dsimp [perp] at *,
    intros z hz,
    have hz₁ := hx z hz,
    have hz₂ := hy z hz,
    exact add_orthog hz₁ hz₂,
end

lemma perp_smul_closed (c : ℝ) (x : α) : x ∈ perp S → c•x ∈ perp S :=
begin
    intros hx,
    dsimp [perp] at *,
    intros z hz,
    have hz₁ := hx z hz,
    have k := @mul_orthog α _ _ _ _ x z c 1 hz₁,
    rw [one_smul] at k,
    exact k,
end

lemma zero_in_perp : (0 : α) ∈ perp S :=
begin
    dsimp [perp],
    intros y h,
    exact right_orthog_to_zero y,
end

def perp_subspace : subspace ℝ α :=
{carrier := perp S, zero := zero_in_perp, add := perp_add_closed, smul := perp_smul_closed}

lemma sub_simp {α : Type*} [add_comm_group α] [vector_space ℝ α] {S : subspace ℝ α} {y : α} : y ∈ S ↔ y ∈ S.carrier :=
begin
    rw [←submodule.mem_coe],
    unfold_coes,
end

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
begin
    ext,
    rw [←sub_simp],
    simp,
end

lemma bounded_functional_ker_closed {f : α →ₗ[ℝ] ℝ} {w : @is_bounded_linear_map ℝ _ α (ip_space_is_normed_space) _ _ f} : @is_closed α (α_topological_space) (linear_map.ker f).carrier :=
begin
    rw [@functional_ker_is_preimage_zero α _ _ _ _],
    have w₁ := @is_bounded_linear_map.continuous ℝ _ α (ip_space_is_normed_space) ℝ _ _ w,
    apply ((@continuous_iff_is_closed α ℝ (α_topological_space) (ℝ_topological_space) f).1 w₁ {0}),
    exact is_closed_singleton,
end

lemma ip_map_ker_is_preimage_zero (x : α) : (linear_map.ker (ip_map x)).carrier = (ip_map x)⁻¹' {0} :=
functional_ker_is_preimage_zero

lemma ip_map_ker_is_closed (x : α) : @is_closed α (α_topological_space) (linear_map.ker (ip_map x)).carrier :=
@bounded_functional_ker_closed α _ _ _ _ _ (ip_map_is_bounded_linear_map x)

lemma perp_singleton_closed (x : α) : @is_closed α (α_topological_space) (perp {x}) :=
begin
    rw [perp_singleton_ker],
    exact ip_map_ker_is_closed x,
end

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
    have k₁ := zero_of_ip_self_zero x,
    dsimp [ip_self] at k₁,
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


lemma perp_singleton_expr (S : set α) {t : set α}: t ∈ {L : set α | ∃ (a : α) (H : a ∈ S), L = perp {a}} → ∃ (a ∈ S), t = perp {a} :=
begin
    intros h,
    simp at h,
    cases h with a h,
    cases h,
    use a,
    use h_left,
    exact h_right,
end

theorem perp_space_closed (S : set α) : @is_closed α (α_topological_space) (perp S) :=
begin
    rw [perp_int_singleton],
    apply @is_closed_sInter α (α_topological_space) _,
    intros t h,
    have k := perp_singleton_expr S h,
    cases k with a k,
    cases k with k₁ k₂,
    rw [k₂],
    exact perp_singleton_closed a,
end

end perp_space

section orthogonal_projection

local attribute [instance] α_normed_space

variables [Hilbert_space α]
variables {S : @submodule ℝ α _ _ _}
variables {h : @is_closed α (α_topological_space) S.carrier}

include h

theorem proj_exists_unique (x : α) : ∃! (y : α), y ∈ S ∧ (∥x-y∥ = Inf {r | ∃ (z ∈ S), r = ∥x-z∥}) :=
begin
    sorry,
end

def orthog_proj (x : α) := classical.some (exists_of_exists_unique (@proj_exists_unique α _ _ _ _ _ S h x))

lemma orthog_classical (x : α) : @orthog_proj α _ _ _ _ _ S h x = classical.some (exists_of_exists_unique (@proj_exists_unique α _ _ _ _ _ S h x)) := rfl

lemma orthog_proj_mem (x : α) : @orthog_proj α _ _ _ _ _ S h x ∈ S :=
begin
    have w := classical.some_spec (exists_of_exists_unique (@proj_exists_unique α _ _ _ _ _ S h x)),
    rw [←orthog_classical] at w,
    cases w,
    exact w_left,
end

lemma orthog_proj_dist (x : α) : ∥x -  @orthog_proj α _ _ _ _ _ S h x∥ = Inf {r | ∃ (z ∈ S), r = ∥x-z∥} :=
begin
    have w := classical.some_spec (exists_of_exists_unique (@proj_exists_unique α _ _ _ _ _ S h x)),
    rw [←orthog_classical] at w,
    cases w,
    exact w_right,
end

lemma orthog_unique (x : α) : ∀ (y z : α), (y ∈ S ∧ (∥x-y∥ = Inf {r | ∃ (j ∈ S), r = ∥x-j∥})) ∧ (z ∈ S ∧ (∥x-z∥ = Inf {r | ∃ (j ∈ S), r = ∥x-j∥})) → y = z :=
begin
    intros y z w,
    cases w,
    have k := unique_of_exists_unique (proj_exists_unique x) w_left w_right,
    exact k,
    exact h,
end

lemma orthog_proj_suff (x y : α) : y ∈ S ∧ (∥x-y∥ = Inf {r | ∃ (z ∈ S), r = ∥x-z∥}) → y = @orthog_proj α _ _ _ _ _ S h x :=
begin
    intros w,
    apply @orthog_unique α _ _ _ _ _ S h,
    split,
    exact w,
    exact ⟨orthog_proj_mem x, orthog_proj_dist x⟩,
end

lemma orthog_proj_suff' (x y : α) : y ∈ S ∧ (∥x-y∥ = Inf {r | ∃ (z ∈ S), r = ∥x-z∥}) → @orthog_proj α _ _ _ _ _ S h x = y :=
by {intros h, apply symm, exact orthog_proj_suff x y h}

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
    split,

    exact zero_mem S,

    simp,
end

lemma orthog_proj_id_on_S : ∀ (x ∈ S), @orthog_proj α _ _ _ _ _ S h x = x :=
begin
    intros x k,
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
    have w₂ := @Inf_le {r | ∃ (z ∈ S), r = ∥x-z∥} (dist_bounded_below x) 0 w₁,
    have w₃ : (∀ (z : ℝ), z ∈ {r : ℝ | ∃ (z : α) (H : z ∈ S), r = ∥x - z∥} → 0 ≤ z) := begin
        intros z k₁,
        simp at k₁,
        cases k₁,
        cases k₁_h,
        rw [k₁_h_right],
        exact norm_nonneg _,
    end,
    have w₄ := (le_Inf {r | ∃ (z ∈ S), r = ∥x-z∥} (dist_nonempty _) (dist_bounded_below x)).2 w₃,
    have w₅ := (antisymm w₂ w₄).symm,
    simp at w₅,
    exact w₅,

    recover,
    repeat {exact h},
end

lemma orthog_proj_zero_on_perp_S : ∀ (x ∈ perp S.carrier), @orthog_proj α _ _ _ _ _ S h x = 0 :=
begin
    intros x k,
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
    have w₂ := Inf_le {r | ∃ (z ∈ S), r = ∥x-z∥} (dist_bounded_below x) w₁,
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
        exact (ip_self_nonneg z),

        dsimp [perp] at k,
        have k₁ := @mul_orthog α _ _ _ _ x z 1 (-1) (k z l_left),
        rw [one_smul, neg_one_smul] at k₁,
        exact k₁,
        rw [l_right],
        exact norm_nonneg _,
    end,
    have w₅ := (le_Inf {r | ∃ (z ∈ S), r = ∥x-z∥} w₃ (dist_bounded_below x)).2 w₄,
    exact (antisymm w₂ w₅).symm,
    repeat {exact h},
end

lemma orthog_proj_add (x y : α) : @orthog_proj α _ _ _ _ _ S h (x+y) = @orthog_proj α _ _ _ _ _ S h x + @orthog_proj α _ _ _ _ _ S h y :=
begin
    apply orthog_proj_suff',
    have w := add_mem S (orthog_proj_mem x) (orthog_proj_mem y),
    split,

    exact w,

    have w₁ : ∥x + y - (orthog_proj x + orthog_proj y)∥ ∈ {r : ℝ | ∃ (z : α) (H : z ∈ S), r = ∥x + y - z∥} := begin
        simp,
        existsi (orthog_proj x + orthog_proj y),
        split,

        exact w,

        simp,
    end,
    have w₂ := Inf_le {r | ∃ (z ∈ S), r = ∥x+y-z∥} (dist_bounded_below _) w₁,
    have w₃ : ∀ (z : ℝ), z ∈ {r : ℝ | ∃ (z : α) (H : z ∈ S), r = ∥x + y - z∥} → ∥x + y - (orthog_proj x + orthog_proj y)∥ ≤ z := begin
        intros r k,
        simp at k,
        cases k with z k,
        cases k,
        rw [k_right],
        sorry,
        recover,
        repeat {exact h},
    end,
    have w₄ := (@le_Inf {r | ∃ (z ∈ S), r = ∥x+y-z∥} (dist_nonempty _) (dist_bounded_below _) ∥x+y-(orthog_proj x + orthog_proj y)∥).2,
    sorry,
    use S,
    exact h,
    use S,
    repeat {exact h},
end
.

lemma orthog_proj_smul (c : ℝ) (x : α) : @orthog_proj α _ _ _ _ _ S h (c • x) = c • (@orthog_proj α _ _ _ _ _ S h x) :=
begin
    apply orthog_proj_suff',
    have w := smul_mem S c (orthog_proj_mem x),
    split,
    
    exact w,
    have w₁ : ∥c • x - c • orthog_proj x∥ ∈ {r : ℝ | ∃ (z ∈ S), r = ∥c • x - z∥} := begin
        simp,
        existsi (c•(orthog_proj x)),
        split,

        exact w,
        rw [add_comm],
    end,
    have w₂ := Inf_le {r | ∃ (z ∈ S), r = ∥c•x-z∥} (@dist_bounded_below α _ _ _ _ _ S h (c•x)) w₁,
    have w₃ : ∀ (z : ℝ), z ∈ {r : ℝ | ∃ (z : α) (H : z ∈ S), r = ∥c • x - z∥} → ∥c•x - c•orthog_proj x∥ ≤ z := sorry,
    have w₄ := (le_Inf {r | ∃ (z ∈ S), r = ∥c•x-z∥} (dist_nonempty (c•x)) (dist_bounded_below _)).2,
    sorry,
    use c,
    exact h,
    exact h,
    use S,
    exact h,
end
.

def orthog_proj_linear : is_linear_map ℝ (@orthog_proj α _ _ _ _ _ S h) :=
{add := orthog_proj_add, smul := orthog_proj_smul}

lemma perp_of_orthog_proj_zero (x : α) : @orthog_proj α _ _ _ _ _ S h x = 0 → x ∈ perp S.carrier :=
begin
    intros w,
    dsimp [perp, orthog],
    intros y k,
    have w₁ := orthog_proj_dist x,
    rw [w] at w₁,
    simp at w₁,
    have w₂ : ∥x∥ ≤ ∥x-y∥ := begin
        have w₂ : ∥x-y∥ ∈ {r : ℝ | ∃ (z : α) (H : z ∈ S), r = ∥x - z∥} := begin
            simp,
            use y,
            exact ⟨k, rfl⟩,
        end,
        have w₃ := Inf_le {r | ∃ (z ∈ S), r = ∥x-z∥} (@dist_bounded_below α _ _ _ _ _ S h x) w₂,
        simp at *,
        rw [←w₁] at w₃,
        exact w₃,
    end,
    rw [←norm_sqr_leq_iff_norm_leq] at w₂,
    simp at w₂,
    rw [←neg_one_smul ℝ, mul_in_snd_coord] at w₂,
    simp at w₂,
    sorry,
    exact norm_nonneg _,
end

theorem ker_orthog_img : (linear_map.ker (is_linear_map.mk' orthog_proj (@orthog_proj_linear α _ _ _ _ _ S h))).carrier = @perp α _ _ _ _ (linear_map.range ((is_linear_map.mk' orthog_proj (@orthog_proj_linear α _ _ _ _ _ S h)))).carrier :=
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
    have w₁ := perp_of_orthog_proj_zero x k,
    have w₂ := orthog_proj_mem z,
    rw [w] at w₂,
    dsimp [perp] at w₁,
    exact w₁ y w₂,

    dsimp [perp],
    intros w,
    apply orthog_proj_zero_on_perp_S,
    dsimp [perp],
    intros y k,
    have w₁ := @orthog_proj_id_on_S α _ _ _ _ _ S h y k,
    have w₂ := w y,
    clear w,
    rw [←sub_simp] at w₂,
    simp at w₂,
    exact w₂ y w₁,
end

lemma orthog_proj_idempotent (x : α) : @orthog_proj α _ _ _ _ _ S h (@orthog_proj α _ _ _ _ _ S h x) = @orthog_proj α _ _ _ _ _ S h x :=
begin
    have w := @orthog_proj_mem α _ _ _ _ _ S h x,
    exact orthog_proj_id_on_S (orthog_proj x) w,
end

lemma orthog_of_orthog_proj_sub (x : α) : (x - @orthog_proj α _ _ _ _ _ S h x) ∈ perp S.carrier:=
begin
    dsimp [perp],
    intros y w,
    -- have w₁ : ∥x-@orthog_proj α _ _  _ _ _ S h x∥ ≤ ∥x - (@orthog_proj α _ _ _ _ _ S h x + y)∥ := begin
    --     have w₁ := @orthog_proj_dist α _ _ _ _ _ S h x,
    --     rw [w₁],
    --     have w₂ : ∥x - (@orthog_proj α _ _ _ _ _ S h x + y)∥ ∈ {r : ℝ | ∃ (z : α) (H : z ∈ S), r = ∥x - z∥} := begin
    --         simp,
    --         use @orthog_proj α _ _ _ _ _ S h x + y,
    --         split,
    --         exact add_mem S (@orthog_proj_mem α _ _ _ _ _ S h x) w,
    --         simp,
    --     end,
    --     have w₃ := Inf_le {r : ℝ | ∃ (z : α) (H : z ∈ S), r = ∥x - z∥} (@dist_bounded_below α _ _ _ _ _ S h x) w₂,
    --     exact w₃,
    -- end,
    -- w₁ : ∥x - orthog_proj x∥ ≤ ∥x - (orthog_proj x + y)∥
    dsimp [orthog],
    by_cases (y=0),

    revert h,
    intros k,
    rw [k],
    exact left_orthog_to_zero _,

    revert h,
    intros k,
    rw [←ne.def, ←norm_neq_zero_iff_neq_zero] at k,
    have k₁ : ∥x-(@orthog_proj α _ _ _ _ _ S h x + ((y † (x - @orthog_proj α _ _ _ _ _ S h x))/∥y∥^2) • y)∥^2 = ∥x-@orthog_proj α _ _ _ _ _ S h x∥^2 - (((x - @orthog_proj α _ _ _ _ _ S h x) † y)/∥y∥^2)^2 := begin
        simp,
        sorry,
    end,
    sorry,
end

lemma orthog_proj_is_symmetric (x y : α) : (@orthog_proj α _ _ _ _ _ S h x) † y = x † (@orthog_proj α _ _ _ _ _ S h y) :=
begin
    sorry,
end

-- lemma orthog_proj_norm_leq (x : α) : ∥@orthog_proj α _ _ _ _ _ S h x∥ ≤ ∥x∥ :=
-- begin
--     have w := pythagoras (@orthog_of_orthog_proj_sub α _ _ _ _ _ S h x),
--     have w₁ : x - orthog_proj x = x + -orthog_proj x := rfl,
--     rw [w₁, ←add_assoc, add_comm _ x, add_assoc, add_right_neg, add_zero] at w,
--     have w₂ := @leq_of_add_nonneg _ _ _ (sqr_nonneg _) (sqr_nonneg _) (sqr_nonneg _) w,
--     rw [←@norm_sqr_leq_iff_norm_leq _ _ _ _ (norm_nonneg _)],
--     exact w₂,
-- end

-- lemma orthog_proj_has_bound : ∃ M > 0, ∀ x : α, ∥@orthog_proj α _ _ _ _ _ S h x ∥ ≤ M * ∥ x ∥ :=
-- begin
--     use 1,
--     use zero_lt_one,
--     intros x,
--     rw [one_mul, ←norm_leq_of_norm_sq_leq, sqr_norm, sqr_norm],
--     dsimp [ip_self],
--     rw [orthog_proj_is_symmetric, orthog_proj_idempotent],
-- end

theorem orthog_direct_sum_exists (x : α) : ∃ (u ∈ S), ∃ (v ∈ perp S.carrier), x = u + v :=
begin
    use @orthog_proj α _ _ _ _ _ S h x,
    use @orthog_proj_mem α _ _ _ _ _ S h x,
    use (x-@orthog_proj α _ _ _ _ _ S h x),
    use @orthog_of_orthog_proj_sub α _ _ _ _ _ S h x,
    simp,
end

theorem orthog_direct_sum_unique (x u₁ u₂ v₁ v₂ : α) (U₁ : u₁ ∈ S) (U₂ : u₂ ∈ S) (V₁ : v₁ ∈ perp S.carrier) (V₂ : v₂ ∈ perp S.carrier) : 
x = u₁ + v₁ → x = u₂ + v₂ → (u₁ = u₂ ∧ v₁ = v₂) :=
begin
    intros k₁ k₂,
    rw [k₁] at k₂,
    have k₃ : u₁ - u₂ = v₂ - v₁ := begin
        sorry,
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
    have w₅ := sub_eq_zero.1 (eq_of_mem_singleton w₃),
    exact ⟨w₄, w₅.symm⟩,
end

end orthogonal_projection

section riesz_representation

local attribute [instance] classical.prop_decidable

def is_riesz_rep (f : α →ₗ[ℝ] ℝ) (x : α) := f.to_fun = ip_map x

variables {f : α →ₗ[ℝ] ℝ}

lemma fun_coe : ⇑f = f.to_fun := rfl

variables [Hilbert_space α]
variables {S : @submodule ℝ α _ _ _}

lemma perp_trivial_of_subspace_all {h : @is_closed α (α_topological_space) S.carrier} : (∀ (x : α), x ∈ S) → (∀ (y : α), y ∈ perp S.carrier → y = 0) :=
begin
    intros k₁ y k₂,
    dsimp [perp] at k₂,
    have k₃ := k₂ y (k₁ y),
    exact zero_of_orthog_self k₃,
end

lemma perp_nonempty_of_subspace_not_all {h : @is_closed α (α_topological_space) S.carrier} : (∃ (x : α), x ∉ S) → (∃ (y : α), y ≠ 0 ∧ y ∈ perp S.carrier) :=
begin
    rw [awesome_mt],
    simp,
    intros k,
    intros x,
    have k₁ := @orthog_direct_sum_exists α _ _ _ _ _ S h x,
    rcases k₁ with ⟨u, ⟨U, ⟨v, ⟨V, k₁⟩⟩⟩⟩,
    rw [k₁],
    have k₂ := k v,
    rw [awesome_mt] at k₂,
    simp at k₂,
    have k₃ := k₂ V,
    rw [k₃, add_zero],
    exact U,
end

lemma perp_nonempty_of_subspace_not_all' {h : @is_closed α (α_topological_space) S.carrier} : (∃ (x : α), x ∉ S) → (∃ (y : α), ∥y∥=1 ∧ y ∈ perp S.carrier) :=
begin
    intros k,
    have k₁ := @perp_nonempty_of_subspace_not_all α _ _ _ _ _ S h k,
    rcases k₁ with ⟨z, ⟨k₁, k₂⟩⟩,
    use ((1/∥z∥)•z),
    split,

    exact norm_one_of_norm_inv z k₁,

    exact smul_mem (perp_subspace) (1/∥z∥) k₂,
end

theorem riesz_rep_exists : @is_bounded_linear_map ℝ _ α (ip_space_is_normed_space) _ _ f → (∃ (x : α), is_riesz_rep f x) :=
begin
    intros w,
    have w₁ := @bounded_functional_ker_closed α _ _ _ _ f w,
    have w₂ := @orthog_direct_sum_exists α _ _ _ _ _ (linear_map.ker f) w₁,
    by_cases (∀ (x : α), x ∈ linear_map.ker f),

    use 0,
    dsimp [is_riesz_rep],
    ext,
    simp,
    have w₃ := w₂ x,
    clear w₂,
    cases w₃ with u w₃,
    cases w₃ with w₃ w₄,
    cases w₄ with v w₄,
    cases w₄ with w₄ w₅,
    rw [w₅, linear_map.add],
    simp at w₃,
    rw [fun_coe] at w₃,
    simp [w₃],
    have w₆ := @perp_trivial_of_subspace_all α _ _ _ _ _ _ w₁ h v w₄,
    rw [w₆],
    exact linear_map.map_zero f,

    revert h,
    intros k,
    rw [not_forall] at k,
    have k₁ := @perp_nonempty_of_subspace_not_all' α _ _ _ _ _ _ w₁ k,
    rcases k₁ with ⟨z, ⟨k₁, k₂⟩⟩,
    use ((f z) • z),
    dsimp [is_riesz_rep],
    ext,
    have k₃ : (f x) • z - (f z) • x ∈ linear_map.ker f := begin
        simp,
        ring,
    end,
    dsimp [perp] at k₂,
    rw [←mul_one (f.to_fun x), ←mul_one ((f.to_fun x)*1), mul_assoc, ←pow_two, ←k₁, sqr_norm],
    dsimp [ip_self],
    rw [←mul_in_fst_coord, ←add_zero (f.to_fun x • z), ←add_left_neg (f.to_fun z • x), ←add_assoc,
    add_in_fst_coord],
    have k₄ := k₂ _ k₃,
    dsimp [orthog] at k₄,
    rw [conj_symm, fun_coe] at k₄,
    rw [k₄, zero_add, fun_coe, mul_in_fst_coord, conj_symm, ←mul_in_fst_coord],
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
