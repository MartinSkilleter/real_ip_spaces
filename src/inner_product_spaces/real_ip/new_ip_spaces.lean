import inner_product_spaces.real_ip.ip_normed_space

set_option class.instance_max_depth 100

noncomputable theory

open real linear_map

section cartesian_prod

variables {α : Type*} {β : Type*}
variables [decidable_eq α] [add_comm_group α] [vector_space ℝ α] [ℝ_inner_product_space α]
variables [decidable_eq β] [add_comm_group β] [vector_space ℝ β] [ℝ_inner_product_space β]

@[reducible] def prod_inner_product (x y : α×β) : ℝ := ⟪x.1 ∥ y.1⟫ + ⟪x.2 ∥ y.2⟫

@[reducible] instance prod_has_inner_product : has_ℝ_inner_product (α×β) := ⟨prod_inner_product⟩

lemma prod_conj_symm (x y : α × β) : ⟪x ∥ y⟫ = ⟪y ∥ x⟫ :=
by {dsimp [inner_product, prod_inner_product],
    rw [conj_symm x.fst, conj_symm x.snd]}

lemma prod_linearity (x y z : α × β) (a : ℝ) : ⟪a • x + y ∥ z⟫ = a * ⟪x ∥ z⟫ + ⟪y ∥ z⟫ :=
begin
    dsimp [inner_product, prod_inner_product],
    simp [-add_comm, add_comm],
    simp,
    rw [left_distrib],
end

lemma comp_neq_zero_of_neq_zero (x : α × β) : x ≠ 0 → x.1 ≠ 0 ∨ x.2 ≠ 0 :=
begin
    rw [awesome_mt], 
    simp [not_or_distrib],
    intros a b,
    rw [←@prod.mk.eta _ _ x, a, b],
    refl,
end

lemma prod_pos_def (x : α × β) (h : x ≠ 0) : ⟪x ∥ x⟫ > 0 :=
begin
    dsimp [inner_product, prod_inner_product],
    have w := comp_neq_zero_of_neq_zero _ h,
    cases w,
    
    exact lt_add_of_pos_of_le (pos_def _ w) (norm_sq_nonneg x.2),

    exact lt_add_of_le_of_pos (norm_sq_nonneg x.1) (pos_def _ w),
end

instance prod_inner_product_space : ℝ_inner_product_space (α×β) :=
{conj_symm := prod_conj_symm, linearity := prod_linearity, pos_def := prod_pos_def}

end cartesian_prod

section real_ip

@[reducible] instance ℝ_has_ℝ_inner_product : has_ℝ_inner_product ℝ := ⟨λ a b, a*b⟩

lemma ℝ_conj_symm (x y : ℝ) : ⟪x ∥ y⟫ = ⟪y ∥ x⟫ := mul_comm x y

lemma ℝ_linearity (x y z : ℝ) (a : ℝ) : ⟪a•x+y ∥ z⟫ = a*⟪x ∥ z⟫ + ⟪y ∥ z⟫ :=
by {dsimp [inner_product], rw [right_distrib, mul_assoc]}

lemma ℝ_pos_def (x : ℝ) : x ≠ 0 → ⟪x ∥ x⟫ > 0 := mul_self_pos

instance ℝ_is_ℝ_inner_product_space : ℝ_inner_product_space ℝ :=
{conj_symm := ℝ_conj_symm, linearity := ℝ_linearity, pos_def := ℝ_pos_def}

end real_ip

open function

section inj_linear_map

variables {γ : Type*} [decidable_eq γ] [add_comm_group γ] [vector_space ℝ γ] [ℝ_inner_product_space γ]
variables {η : Type*} [decidable_eq η] [add_comm_group η] [vector_space ℝ η]
variables (f : linear_map ℝ η γ) (h : injective f.to_fun)

lemma fun_coe (f : linear_map ℝ η γ) : ⇑f = f.to_fun := rfl

include f h

@[reducible] instance inj_has_inner_product : has_ℝ_inner_product η := ⟨λ x y, ⟪f.to_fun x ∥ f.to_fun y⟫⟩

lemma inj_conj_symm (x y : η) : ⟪f.to_fun x ∥ f.to_fun y⟫ = ⟪f.to_fun y ∥ f.to_fun x⟫ := conj_symm (f.to_fun x) (f.to_fun y)

lemma inj_linearity (x y z : η) (a : ℝ) : ⟪f.to_fun (a • x + y) ∥ f.to_fun z⟫ = a * ⟪f.to_fun x ∥ f.to_fun z⟫ + ⟪f.to_fun y ∥ f.to_fun z⟫ :=
by {rw [add, smul],
    exact linearity (f.to_fun x) (f.to_fun y) (f.to_fun z) a}

lemma trivial_ker_of_injective (x : η) (k : f.to_fun x = 0) : x = 0 :=
begin
    have w := map_zero f,
    dsimp [injective] at h,
    rw [←w, fun_coe f] at k,
    exact (h k),
end

lemma inj_pos_def (x : η) : x ≠ 0 → ⟪f.to_fun x ∥ f.to_fun x⟫ > 0 :=
begin
    rw [awesome_mt],
    simp,
    have w := norm_sq_nonneg (f.to_fun x),
    have k₁ := zero_iff_norm_sq_zero (f.to_fun x),
    dsimp [norm_sq] at *,
    intros k,
    have w₁ := antisymm w k,
    have w₂ := k₁.1 w₁,
    exact (trivial_ker_of_injective f h x w₂),
end

instance inj_inner_product_space (f : linear_map ℝ η γ) (h : injective f.to_fun) : ℝ_inner_product_space η :=
begin
    refine_struct {..},

    use λ x y, ⟪f.to_fun x ∥ f.to_fun y⟫,

    exact inj_conj_symm f h,

    exact inj_linearity f h,

    exact inj_pos_def f h,
end

end inj_linear_map

section subspace

variables {γ : Type*} [decidable_eq γ] [add_comm_group γ] [vector_space ℝ γ] [ℝ_inner_product_space γ]
variables {η : subspace ℝ γ}

def realise : linear_map ℝ η γ :=
begin
    refine_struct {..},
    use λ x, x,
    repeat {simp},
end

lemma realise_injective : @injective ↥η γ (realise.to_fun) :=
begin
    dsimp [injective, realise],
    intros x₁ x₂ k,
    exact set_coe.ext k,
end

instance sub_inner_product_space : ℝ_inner_product_space η :=
inj_inner_product_space realise realise_injective

end subspace



