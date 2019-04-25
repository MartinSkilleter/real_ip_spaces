import inner_product_spaces.complex_ip.ip_normed_space

noncomputable theory

variables {α : Type*}
variables [decidable_eq α] [add_comm_group α] [vector_space ℂ α] [ℂ_inner_product_space α]

open complex

section complex_ip

theorem ip_parallelogram_law (x y : α) : ∥x+y∥^2+∥x-y∥^2=2*∥x∥^2+2*∥y∥^2 :=
begin
    simp,
    dsimp [ip_self],
    have w : (x†-y).re = -(x†y).re, begin
        rw [←neg_one_smul ℂ y],
        have k : ((-1 : ℝ) : ℂ) = (-1 : ℂ), begin
            rw [ext_iff],
            split,

            refl,

            dsimp [(-1 : ℂ)],
            simp only [neg_zero],
        end,
        rw [←k, mul_re_in_snd],
        ring,
    end,
    rw [w],
    simp,
    ring,
end

class parallelopotamus (β : Type*) [add_comm_group β] [vector_space ℂ β] extends normed_space ℂ β :=
(parallelogram_law : ∀ (x y : β), ∥x+y∥^2+∥x-y∥^2=2*∥x∥^2+2*∥y∥^2)

variables {β : Type*}
variables [decidable_eq β] [add_comm_group β] [vector_space ℂ β] [normed_space ℂ β]
variables [parallelopotamus β] [has_norm β]

def par_inner_product (x y : β) : ℂ := 1/4*(∥x+y∥^2 + ∥x-y∥^2 + I*∥x+I•y∥^2 + -I*∥x-I•y∥^2)

instance par_has_inner_product : has_ℂ_inner_product β := ⟨par_inner_product⟩

lemma ip_self_eq_norm_sq (x : β) : (x†x).re = ∥x∥^2 :=
begin
    have w : x†x = (∥x∥^2 : ℂ) → (x†x).re = ∥x∥^2, begin
        intros h,
        have w₁ := (ext_iff.1 h).left,
        have w₂ : (∥x∥^2 : ℂ).re = ∥x∥^2, by sorry,
        rw [w₂] at w₁,
        exact w₁,
    end,
    apply w,
    dsimp [(†), par_inner_product],
    sorry,
end

end complex_ip
