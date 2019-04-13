import analysis.normed_space.basic
import data.complex.basic

noncomputable theory

variables {α : Type*} {β : Type*}

open complex

class has_inner_product (α : Type*) := (inner_product : α → α → ℂ)

export has_inner_product (inner_product)

class inner_product_space (α : Type*) [add_comm_group α] [vector_space ℂ α] extends has_inner_product α :=
(conj_symm : ∀ (x y : α), inner_product x y = conj (inner_product y x))
(linearity : ∀ (x y z : α), ∀ (a : ℂ), inner_product (a • x + y) z = a * inner_product x z + inner_product y z)
(pos_def : ∀ (x : α), ∃ (r : ℝ), (r : ℂ) = inner_product x x ∧ (x ≠ 0 → r > 0))

section inner_product_space
variables [decidable_eq α] [add_comm_group α] [vector_space ℂ α] [inner_product_space α]

precedence `†` : 70
infix `†` := inner_product

lemma conj_symm (x y : α) : x † y = conj (y † x) :=
by apply inner_product_space.conj_symm

lemma linearity (x y z : α) (a : ℂ) : (a • x + y) † z = a * (x † z) + y † z :=
by apply inner_product_space.linearity

lemma pos_def (x : α) : ∃ (r : ℝ), (r : ℂ) = x † x ∧ (x ≠ 0 → r > 0) :=
by apply inner_product_space.pos_def

lemma right_orthog_to_zero (x : α) : 0 † x = 0 :=
begin
    have h := linearity 0 0 x 1,
    simp only [add_zero, one_mul, smul_zero] at h,
    have w := @add_left_cancel ℂ _ (0†x) 0 (0†x),
    simp only [add_zero] at w,
    exact (w h).symm,
end

lemma left_orthog_to_zero (x : α) : x † 0 = 0 :=
begin
    have h := right_orthog_to_zero x,
    rw conj_symm at h,
    simp only [complex.conj_eq_zero] at h,
    exact h,
end

lemma zero_of_self_ip_zero (x : α) : x † x = 0 → x = 0 :=
begin
    intros h,
    by_contradiction,
    have w := pos_def x,
    cases w with r w,
    cases w,
    rw [h] at w_left,
    simp only [of_real_eq_zero] at w_left,
    have k := le_of_eq w_left,
    have k' := w_right a,
    dsimp [(>)] at k',
    rw [lt_iff_not_ge 0 r] at k',
    have j := and.intro k k',
    rw [and_not_self] at j,
    exact j,
end

lemma zero_iff_self_ip_zero (x : α) : x†x=0 ↔ x=0 :=
begin
    split,
    exact zero_of_self_ip_zero x,
    have h := left_orthog_to_zero x,
    intros w,
    rw [←w] at h,
    exact h, 
end

lemma mul_in_snd_coord (x y : α) (a : ℂ) : x † (a • y) = (conj a) * (x†y) :=
begin
    rw [conj_symm],
    apply conj_inj.1,
    conv {to_rhs, rw [conj_symm, ←conj_mul]},
    simp only [conj_conj],
    have h := linearity y 0 x a,
    simp only [right_orthog_to_zero, add_zero] at h,
    exact h,
end

lemma add_in_snd_coord (x y z : α) : x†(y+z) = (x†y)+(x†z) :=
begin
    have h := linearity y z x 1,
    simp only [one_smul, one_mul] at h,
    rw [←conj_inj, conj_add, ←conj_symm, ←conj_symm x y, ←conj_symm] at h,
    exact h,
end

def norm_sq' (x y : α) : ℝ :=
begin
    have h := pos_def (x-y),
    induction h,
    sorry,
end

instance ip_space_has_norm : has_norm α := sorry

variables [decidable_eq β] [add_comm_group β] [vector_space ℂ β] [inner_product_space β]

instance prod_vector_space : vector_space ℂ (α×β) := by apply_instance

def prod_inner_product (x y : α×β) : ℂ := x.1†y.1 + x.2†y.2

instance prod_has_inner_product : has_inner_product (α×β) := ⟨prod_inner_product⟩

lemma prod_conj_symm : ∀ (x y : α×β), x†y = conj (y†x) :=
begin
    intros x y,
    dsimp [(†), prod_inner_product],
    rw [conj_add],
end

instance prod_inner_product_space : inner_product_space (α×β) :=
begin
    refine {conj_symm := sorry, linearity := sorry, pos_def := sorry}
end

end inner_product_space
