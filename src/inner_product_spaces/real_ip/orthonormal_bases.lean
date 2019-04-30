import inner_product_spaces.real_ip.ip_normed_space
import linear_algebra.basis

noncomputable theory

variables {α : Type*}

open real set module submodule

variables [decidable_eq α] [add_comm_group α] [vector_space ℝ α] [ℝ_inner_product_space α]

lemma real_zero (r : ℝ) : r = -r ↔ r = 0 :=
begin
    split,

    intros h,
    have w := congr_arg (λ (s : ℝ), s + r) h,
    simp at w,
    have k : r + r = 2*r := begin
        have k₁ : (1 : ℝ) + 1 = 2 := by refl,
        rw [←k₁, right_distrib, one_mul],
    end,
    rw [k] at w,
    have w₁ := eq_zero_or_eq_zero_of_mul_eq_zero w,
    cases w₁,
    have w₂ : 2 ≠ 0 := by exact dec_trivial,
     

    intros h,
    rw [h, neg_zero],
end

-- lemma orthog_equiv {x y : α} (h₁ : x ≠ 0) (h₂ : y ≠ 0) : x ⊥ y ↔ ∀ (r : ℝ), ∥x+r•y∥=∥x-r•y∥ :=
-- begin
--     split,

--     intros h r,
--     rw [norm_eq_iff_norm_sq_eq, sqr_norm, sqr_norm],
--     dsimp [ip_self],
--     rw [←neg_one_smul ℝ],
--     simp,
--     repeat {rw [mul_in_fst_coord]},
--     repeat {rw [mul_in_snd_coord]},
--     simp,
--     dsimp [orthog] at h,
--     rw [conj_symm, h],
--     simp,
    
--     intros h,
--     have w := h 1,
--     rw [norm_eq_iff_norm_sq_eq] at w,
--     simp at w,
--     rw [←neg_one_smul ℝ, mul_in_snd_coord] at w,
--     simp at w,
    
    
-- end

-- def orthog_set (L : set α) : Prop :=
-- ∀ (a b ∈ L), a ≠ b → a ⊥ b

-- lemma emptyset_orthog : orthog_set (∅ : set α) :=
-- begin
--     dsimp [orthog_set],
--     simp,
-- end

-- lemma add_elt_to_orthog (L : set α) (x : α) (h : orthog_set L) (w : ∀ (y ∈ L), x ⊥ y) : orthog_set (L ∪ {x}) :=
-- begin
--     dsimp [orthog_set] at *,
--     intros a b k₁ k₂ k₃,
--     cases k₁,
--     cases k₂,

--     exact h a b k₁ k₂ k₃,

--     have k₄ := w a k₁,
--     apply orthog_symm,
--     have k₅ := eq_of_mem_singleton k₂,
--     rw [k₅],
--     exact k₄,

--     cases k₂,

--     have k₄ := eq_of_mem_singleton k₁,
--     have k₅ := w b k₂,
--     rw [←k₄] at k₅,
--     exact k₅,

--     have k₄ := eq_of_mem_singleton k₁,
--     have k₅ := (eq_of_mem_singleton k₂).symm,
--     rw [←k₄] at k₅,
--     contradiction,
-- end

-- lemma orthog_subset (L S : set α) (h : orthog_set L) (w : S ⊆ L) : orthog_set S :=
-- begin
--     dsimp [orthog_set] at *,
--     dsimp [(⊆), set.subset] at w,
--     intros a b k₁ k₂ k₃,
--     exact (h a b (w k₁) (w k₂) k₃),
-- end

-- def orthonormal (L : set α) : Prop :=
-- orthog_set L ∧ ∀ (a ∈ L), ∥a∥=1

-- def normalise (L : set α) := image (λ (a : α), (1/∥a∥ : ℝ) • a) L

-- lemma norm_one_of_normalised (L : set α) (h : (0 : α) ∉ L) : ∀ (a ∈ (normalise L)), ∥a∥=1 :=
-- begin
--     intros a w,
--     dsimp [normalise] at w,
--     simp at w,
--     cases w with b k₁,
--     cases k₁ with k₁ k₂,
--     have k₃ : b ≠ 0, begin
--         by_contradiction,
--         simp only [not_not] at a_1,
--         rw [a_1] at k₁,
--         contradiction,
--     end,
--     rw [←k₂, ip_norm_smul],
--     simp,
--     exact (inv_mul_cancel ((norm_neq_zero_iff_neq_zero b).2 k₃)),
-- end

-- lemma orthog_normalised_of_orthog (L : set α) (h : orthog_set L) : orthog_set (normalise L) :=
-- begin
--     dsimp [orthog_set] at *,
--     dsimp [normalise],
--     simp,
--     intros a b x k₁ k₂ y k₃ k₄ k₅,
--     have k₆ : x ≠ y, begin
--         by_contradiction,
--         simp only [not_not] at a_1,
--         rw [a_1] at k₂,
--         rw [k₂] at k₄,
--         contradiction,
--     end,
--     have k₇ := h x y k₁ k₃ k₆,
--     have k₈ := @mul_orthog _ _ _ _ _ x y (∥x∥)⁻¹ (∥y∥)⁻¹ k₇,
--     rw [k₂, k₄] at k₈,
--     exact k₈,
-- end

-- lemma orthonormal_normalised_of_orthog_set (L : set α) (h : orthog_set L) (w : (0 : α) ∉ L) : orthonormal (normalise L) :=
-- begin
--     dsimp [orthonormal],
--     split,
--     exact (orthog_normalised_of_orthog L h),
--     exact (norm_one_of_normalised L w),
-- end

-- lemma orthog_set_is_lin_indep (L : set α) (h : orthog_set L) (w : (0 : α) ∉ L) : linear_independent ℝ L :=
-- begin
--     dsimp [linear_independent, lc.total, lc.lsum, lc, lc.supported, disjoint],
--     -- rw [linear_independent_iff],
--     -- dsimp [lc],
--     sorry,
-- end

-- lemma span_of_normalised_is_span (L : set α) : span ℝ (normalise L) = span ℝ L :=
-- begin
--     dsimp [span],
--     sorry,
-- end
