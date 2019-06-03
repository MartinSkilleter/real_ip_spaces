import inner_product_spaces.real_ip.ip_normed_space
import tactic.interactive
import tactic.basic

-- Ask Scott how to fix this
set_option class.instance_max_depth 100

noncomputable theory

open complex linear_map

section cartesian_prod

variables {α : Type*} {β : Type*}
variables [decidable_eq α] [add_comm_group α] [vector_space ℝ α] [ℝ_inner_product_space α]
variables [decidable_eq β] [add_comm_group β] [vector_space ℝ β] [ℝ_inner_product_space β]

instance prod_vector_space : vector_space ℝ (α×β) := by apply_instance

def prod_inner_product (x y : α×β) : ℝ := x.1†y.1 + x.2†y.2

instance prod_has_inner_product : has_ℝ_inner_product (α×β) := ⟨prod_inner_product⟩

lemma prod_conj_symm : ∀ (x y : α × β), x†y = y†x :=
begin
    intros x y,
    dsimp [(†), prod_inner_product],
    rw [conj_symm x.fst, conj_symm x.snd],
end

lemma prod_linearity (x y z : α × β) (a : ℝ) : (a • x + y) † z = a * (x † z) + y † z :=
begin
    dsimp [(†), prod_inner_product],
    simp [-add_comm],
    simp,
    rw [left_distrib],
end

lemma comp_neq_zero_of_neq_zero (x : α × β) : x ≠ 0 → x.1 ≠ 0 ∨ x.2 ≠ 0 :=
begin
    intros h,
    by_contradiction,
    rw [not_or_distrib] at a,
    simp only [not_not] at a,
    cases a,
    have w : x = (x.1, x.2) := by simp only [prod.mk.eta, eq_self_iff_true],
    rw [a_left, a_right] at w,
    have k : (0, 0) = (0 : α × β) := by refl,
    rw [←w] at k,
    contradiction,
end

lemma prod_pos_def : ∀ (x : α × β), x ≠ 0 → x†x > 0 :=
begin
    intros x h,
    dsimp [(†), prod_inner_product],
    have w := comp_neq_zero_of_neq_zero _ h,
    cases w,
    
    have k := pos_def _ w,
    have k' := ip_self_nonneg x.2,
    dsimp [ip_self] at k',
    exact lt_add_of_pos_of_le k k',

    have k := pos_def _ w,
    have k' := ip_self_nonneg x.1,
    dsimp [ip_self] at k',
    exact lt_add_of_le_of_pos k' k,
end

instance prod_inner_product_space : ℝ_inner_product_space (α×β) :=
{conj_symm := prod_conj_symm, linearity := prod_linearity, pos_def := prod_pos_def}

end cartesian_prod

section real_ip

instance ℝ_has_ℝ_inner_product : has_ℝ_inner_product ℝ := ⟨λ a b, a*b⟩

lemma ℝ_conj_symm (x y : ℝ) : x†y=y†x :=
by {dsimp [(†)], exact mul_comm x y}

lemma ℝ_linearity (x y z : ℝ) (a : ℝ) : (a•x+y)†z = a*(x†z) + y†z :=
by {dsimp [(†)], rw [right_distrib, mul_assoc]}

lemma ℝ_pos_def (x : ℝ) : x ≠ 0 → x†x > 0 :=
by {exact mul_self_pos}

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

instance inj_has_inner_product : has_ℝ_inner_product η := ⟨λ x y, f.to_fun x † f.to_fun y⟩

lemma inj_conj_symm : ∀ (x y : η), (f.to_fun x) † (f.to_fun y) = (f.to_fun y) † (f.to_fun x) :=
by {intros x y, exact conj_symm (f.to_fun x) (f.to_fun y)}

lemma inj_linearity : ∀ (x y z : η) (a : ℝ), (f.to_fun (a • x + y))†(f.to_fun z) = a * ((f.to_fun x)†(f.to_fun z)) + (f.to_fun y)†(f.to_fun z) :=
begin
    intros x y z a,
    rw [add, smul],
    exact linearity (f.to_fun x) (f.to_fun y) (f.to_fun z) a,
end

lemma trivial_ker_of_injective : ∀ (x : η), f.to_fun x = 0 → x = 0 :=
begin
    intros x k,
    have w := map_zero f,
    dsimp [injective] at h,
    rw [←w, fun_coe f] at k,
    exact (h k),
end

lemma inj_pos_def : ∀ (x : η), x ≠ 0 → (f.to_fun x)†(f.to_fun x) > 0 :=
begin
    intros x,
    rw [awesome_mt],
    simp,
    have w := ip_self_nonneg (f.to_fun x),
    have k₁ := zero_iff_ip_self_zero (f.to_fun x),
    dsimp [ip_self] at *,
    intros k,
    have w₁ := antisymm w k,
    have w₂ := k₁.1 w₁,
    exact (trivial_ker_of_injective f h x w₂),
end

instance inj_inner_product_space (f : linear_map ℝ η γ) (h : injective f.to_fun) : ℝ_inner_product_space η :=
begin
    refine_struct {..},

    use λ x y, f.to_fun x † f.to_fun y,

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
@inj_inner_product_space γ _ _ _ _ η _ _ _ realise realise_injective

end subspace



