import inner_product_spaces.complex_ip.basic

-- Ask Scott how to fix this
set_option class.instance_max_depth 100

noncomputable theory

open complex

variables {α : Type*} {β : Type*}
variables [decidable_eq α] [add_comm_group α] [vector_space ℂ α] [ℂ_inner_product_space α]
variables [decidable_eq β] [add_comm_group β] [vector_space ℂ β] [ℂ_inner_product_space β]

instance prod_vector_space : vector_space ℂ (α×β) := by apply_instance

section cartesian_prod

def prod_inner_product (x y : α×β) : ℂ := x.1†y.1 + x.2†y.2

instance prod_has_inner_product : has_ℂ_inner_product (α×β) := ⟨prod_inner_product⟩

lemma prod_conj_symm : ∀ (x y : α × β), x†y = conj (y†x) :=
begin
    intros x y,
    dsimp [(†), prod_inner_product],
    rw [conj_add, ←conj_symm x.fst y.fst, ←conj_symm x.snd y.snd],
end

lemma prod_linearity (x y z : α × β) (a : ℂ) : (a • x + y) † z = a * (x † z) + y † z :=
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

lemma prod_pos_def : ∀ (x : α × β), x ≠ 0 → (x†x).re > 0 :=
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

instance prod_inner_product_space : ℂ_inner_product_space (α×β) :=
{conj_symm := prod_conj_symm, linearity := prod_linearity, pos_def := prod_pos_def}

end cartesian_prod
