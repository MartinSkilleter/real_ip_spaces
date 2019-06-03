import inner_product_spaces.complex_ip.ip_normed_space
import linear_algebra.basis

noncomputable theory

variables {α : Type*}

open complex set module submodule

variables [decidable_eq α] [add_comm_group α] [vector_space ℂ α] [ℂ_inner_product_space α]

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

def normalise (L : set α) := image (λ (a : α), (1/∥a∥ : ℂ) • a) L

lemma elem_of_normalised (L : set α) (x : α) : x ∈ normalise L → ∃ (y ∈ L) (a : ℂ), a • y = x :=
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

lemma elem_of_normalised' (L : set α) (x : α) : (x ∈ L) → (((1 / ∥x∥ : ℂ) • x) ∈ normalise L) :=
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
    have k₈ := mul_orthog x y (↑∥x∥)⁻¹ (↑∥y∥)⁻¹ k₇,
    rw [k₂, k₄] at k₈,
    exact k₈,
end

lemma orthonormal_normalised_of_orthog_set (L : set α) (h : orthog_set L) (w : (0 : α) ∉ L) : orthonormal (normalise L) :=
⟨orthog_normalised_of_orthog L h, norm_one_of_normalised L w⟩

lemma orthog_set_is_lin_indep (L : set α) (h : orthog_set L) (w : (0 : α) ∉ L) : linear_independent ℂ L :=
begin
    rw [linear_independent_iff],
    intros l k₁ k₂,
    dsimp [lc.total, finsupp.sum] at k₂,
    sorry,
end

lemma scale_elem_in_span (L : set α) (x : α) (a : ℂ) : x ∈ span ℂ L → (a • x) ∈ span ℂ L :=
begin
    intros h,
    rw [mem_span] at *,
    intros p k,
    have w := h p k,
    have l := smul p a w,
    exact l,
end

lemma normalised_subset_span (L : set α) : normalise L ⊆ ↑(span ℂ L) :=
begin
    have w : ∀ (x : α), (x ∈ normalise L) → x ∈ ↑(span ℂ L) := begin
        intros x a,
        have w₁ := elem_of_normalised L x a,
        cases w₁ with y w₁,
        cases w₁ with w₁ w₂,
        cases w₂ with a w₂,
        have w₃ := @subset_span ℂ _ _ _ _ _,
        have w₄ := w₃ w₁,
        have w₅ := scale_elem_in_span L y a w₄,
        rw [w₂] at w₅,
        exact w₅,
    end,
    exact w,
end

lemma in_submodule_of_normalised_in_submodule (L : set α) (p : submodule ℂ α) : (normalise L ⊆ ↑p) → L ⊆ ↑p :=
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
        have w₃ := smul p ↑∥x∥ w₂,
        simp [smul_smul] at w₃,
        have w₄ := of_real_ne_zero.2 ((norm_neq_zero_iff_neq_zero x).2 h),
        have w₅ := div_self w₄,
        have w₆ : ↑∥x∥/↑∥x∥ = ↑∥x∥*(↑∥x∥)⁻¹ := begin
            rw [←mul_one ↑∥x∥, mul_div_assoc ↑∥x∥ (1 : ℂ), one_div_eq_inv],
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

lemma span_of_normalised_is_span (L : set α) : span ℂ (normalise L) = span ℂ L :=
begin
    ext,
    rw [mem_span],
    split,

    intros h,
    exact (h (span ℂ L)) (normalised_subset_span L),
    
    intros h p w,
    have h' := mem_span.1 h,
    have h₁ := h' p,
    clear h',
    exact h₁ (in_submodule_of_normalised_in_submodule L p w),
end

def orthonormal_basis (L : set α) := orthonormal L ∧ is_basis ℂ L

theorem normalised_basis_is_orthonormal_basis (L : set α) : is_basis ℂ L → orthog_set L → orthonormal_basis (normalise L) :=
begin
    intros h k,
    dsimp [orthonormal_basis, is_basis] at *,
    cases h,
    have w := zero_not_mem_of_linear_independent (@zero_ne_one ℂ _) h_left,
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

section perp_space

def perp (L : set α) : set α := {x | ∀ (y ∈ L), x ⊥ y}

lemma perp_perp (L : set α) : L ⊆ perp (perp L) :=
begin
    have w : ∀ (x : α), x ∈ L → x ∈ perp (perp L) := begin
        intros x h,
        dsimp [perp],
        intros y k,
        have k₁ := orthog_symm y x (k x h),
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
variables [add_comm_group S] [vector_space ℂ S] [subspace ℂ S]

set_option trace.class_instances true
lemma perp_closed : ∀ (x y : α), (x ∈ perp S) → (y ∈ perp S) → ((x+y) ∈ perp S) :=
begin
    -- intros x y h₁ h₂,
    -- dsimp [perp] at *,
    -- intros z k,
    -- have w₁ := h₁ z k,
    -- have w₂ := h₂ z k,
    -- dsimp [orthog] at *,
    -- rw [add_in_fst_coord, h₁, h₂],
    sorry,
end

instance perp_has_add : has_add (perp S) := ⟨λ x y : α, @has_add.add α sorry x y⟩



lemma perp_add_assoc (x y z : perp S) : (x + y) + z = x + (y + z) :=
begin
    sorry,
end

instance perp_space_is_add_comm_group : add_comm_group (perp S) :=
begin
    refine {add := sorry, add_assoc := perp_add_assoc, zero := (0 : α)}
end

instance perp_space_is_vector_space : vector_space ℂ (perp S) :=
begin
    sorry,
end

end perp_space
