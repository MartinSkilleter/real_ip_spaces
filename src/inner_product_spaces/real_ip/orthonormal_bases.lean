import inner_product_spaces.real_ip.hilbert_space
import linear_algebra.basis

noncomputable theory

variables {α : Type*}

open real set module submodule

variables [decidable_eq α] [add_comm_group α] [vector_space ℝ α] [ℝ_inner_product_space α]

section norm_known

instance normed_space_ℝ_α : normed_space ℝ α := ip_space_is_normed_space

instance α_topological_space : topological_space α := by apply_instance

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
    rw [←k₂, ip_norm_smul],
    simp,
    exact (inv_mul_cancel ((norm_neq_zero_iff_neq_zero b).2 k₃)),
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
    dsimp [linear_independent, lc.total, lc.lsum, lc, lc.supported, disjoint],
    
    -- dsimp [lc],
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

set_option trace.eqn_compiler.elim_match true
def gram_schmidt : set α → set α
| false := false -- The emptyset
 
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

def ip_map (x : α) := λ y, x † y

lemma perp_singleton_closed (x : α) : @is_closed α _ (perp {x}) :=
begin
    rw [is_closed_iff_nhds],
    intros a h,
    simp at h,
    dsimp [nhds, (⊥)] at h,
    sorry,
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

    intros h,
    dsimp [perp] at *,
    intros y w,
    have k := h {y},
    simp at k,
    sorry,
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

theorem perp_space_closed (S : set α) : @is_closed α _ (perp S) :=
begin
    rw [perp_int_singleton],
    apply @is_closed_sInter α _ _,
    intros t h,
    have k := perp_singleton_expr S h,
    cases k with a k,
    cases k with k₁ k₂,
    rw [k₂],
    exact perp_singleton_closed a,
end

variables {S : set α}

lemma perp_add_closed {x y : α} {hx : x ∈ perp S} {hy : y ∈ perp S} : x + y ∈ perp S :=
begin
    dsimp [perp] at *,
    intros z hz,
    have hz₁ := hx z hz,
    have hz₂ := hy z hz,
    exact add_orthog hz₁ hz₂,
end

lemma perp_mul_closed {x : α} {hx : x ∈ perp S} {c : ℝ} : c•x ∈ perp S :=
begin
    dsimp [perp] at *,
    intros z hz,
    have hz₁ := hx z hz,
    have k := @mul_orthog α _ _ _ _ x z c 1 hz₁,
    rw [one_smul] at k,
    exact k,
end

instance perp_has_add : has_add (perp S) := 
⟨λ x y, ⟨x.val + y.val, @perp_add_closed _ _ _ _ _ S _ _ x.property y.property⟩⟩

lemma perp_add_assoc (x y z : perp S) : (x + y) + z = x + (y + z) :=
begin
    dsimp [(+)],
    simp only [subtype.mk_eq_mk],
    exact (add_assoc _ _ _),
end

lemma zero_in_perp : (0 : α) ∈ perp S :=
begin
    dsimp [perp],
    intros y h,
    exact right_orthog_to_zero y,
end

instance perp_has_zero : has_zero (perp S) :=
begin
    constructor,
    use (0 : α),
    exact zero_in_perp,
end

lemma perp_zero_add (x : perp S) : 0 + x = x :=
begin
    dsimp [(+)],
    have h : add_semigroup.add ((0 : perp S).val) (x.val) = x.val := by exact zero_add x.val,
    simp [h],
end

lemma perp_add_comm (x y : perp S) : x + y = y + x :=
begin
    dsimp [(+)],
    have h : add_semigroup.add x.val y.val = add_semigroup.add y.val x.val := by exact add_comm x.val y.val,
    simp [h],
end

lemma perp_add_zero (x : perp S) : x + 0 = x:=
by {rw [perp_add_comm], exact perp_zero_add x}

lemma neg_in_perp (x : α) : x ∈ perp S → -x ∈ perp S :=
begin
    intros h,
    dsimp [perp] at *,
    intros y w,
    rw [←@neg_one_smul ℝ α _, ←one_smul ℝ y],
    exact mul_orthog (h y w),
end

instance perp_has_neg : has_neg (perp S) :=
begin
    constructor,
    intros x,
    use (-(x : α)),
    have h : (x : α) ∈ perp S := by simp,
    exact neg_in_perp (x : α) h,
end

lemma perp_add_left_neg (x : perp S) : -x + x = 0 :=
begin
    dsimp [(+), has_neg.neg],
    have h : add_semigroup.add (add_group.neg ↑x) (x.val) = 0 := by exact add_left_neg _,
    simp [h],
    refl,
end

instance perp_add_comm_group : add_comm_group (perp S) :=
{add := (+), add_assoc := perp_add_assoc, zero := 0, zero_add := perp_zero_add,
 add_zero := perp_add_zero, neg := has_neg.neg, add_left_neg := perp_add_left_neg,
 add_comm := perp_add_comm}

instance perp_vector_space : vector_space ℝ (perp S) :=
sorry



end perp_space
