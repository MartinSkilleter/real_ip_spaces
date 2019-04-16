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
(pos_def : ∀ (x : α), x ≠ 0 → (inner_product x x).re > 0)

section inner_product_space
variables [decidable_eq α] [add_comm_group α] [vector_space ℂ α] [inner_product_space α]

precedence `†` : 70
infix `†` := inner_product

lemma conj_symm (x y : α) : x † y = conj (y † x) :=
by apply inner_product_space.conj_symm

lemma linearity (x y z : α) (a : ℂ) : (a • x + y) † z = a * (x † z) + y † z :=
by apply inner_product_space.linearity

@[simp] lemma add_in_fst_coord (x y z : α) : (x + y) † z = x † z + y † z :=
begin
    have h := linearity x y z 1,
    simp only [one_mul, one_smul] at h,
    exact h,
end

lemma pos_def (x : α) : x ≠ 0 → (inner_product x x).re > 0 :=
by apply inner_product_space.pos_def

@[simp] lemma right_orthog_to_zero (x : α) : 0 † x = 0 :=
begin
    have h := linearity 0 0 x 1,
    simp only [add_zero, one_mul, smul_zero] at h,
    have w := @add_left_cancel ℂ _ (0†x) 0 (0†x),
    simp only [add_zero] at w,
    exact (w h).symm,
end

@[simp] lemma left_orthog_to_zero (x : α) : x † 0 = 0 :=
begin
    have h := right_orthog_to_zero x,
    rw conj_symm at h,
    simp only [complex.conj_eq_zero] at h,
    exact h,
end

@[simp] lemma mul_in_fst_coord (x z : α) (a : ℂ) : (a•x)†z = a*(x†z) :=
begin
    have h := linearity x 0 z a,
    simp only [right_orthog_to_zero, add_zero] at h,
    exact h,
end

def ip_self : α → ℂ := λ x, x†x

@[simp] lemma ip_self_zero : ip_self (0 : α) = 0 :=
begin
    dsimp [ip_self],
    exact (right_orthog_to_zero 0),
end

lemma zero_of_self_ip_zero (x : α) : ip_self x = 0 → x = 0 :=
begin
    intros h,
    by_contradiction,
    have w := pos_def x a,
    dsimp [ip_self] at h,
    have k : (x†x).re = 0, by {rw [h], refl},
    have k₁ : (x†x).re ≤ 0, by rw [←k],
    have k₂ := not_lt_of_le k₁,
    contradiction,
end

lemma zero_iff_ip_self_zero (x : α) : ip_self x=0 ↔ x=0 :=
begin
    split,

    exact zero_of_self_ip_zero x,

    intros h,
    rw [h],
    exact ip_self_zero,
end

@[simp] lemma ip_self_im_zero (x : α) : (ip_self x).im = 0 :=
begin
    have h := conj_symm x x,
    dsimp [ip_self],
    have h' := h.symm,
    rw [eq_conj_iff_real (x†x)] at h',
    cases h' with r h',
    rw [ext_iff] at h',
    cases h',
    simp only [of_real_im] at h'_right,
    exact h'_right,
end

@[simp] lemma ip_self_eq_conj (x : α) : conj (x†x) = x†x :=
begin
    simp [ext_iff],
    have w := ip_self_im_zero x,
    dsimp [ip_self] at w,
    rw [w, neg_zero],
end

@[simp] lemma ip_self_comm_eq (x : α) : (((ip_self x).re) : ℂ) = ip_self x :=
by simp [ext_iff]

@[simp] lemma ip_self_nonneg (x : α) : (ip_self x).re ≥ 0 :=
begin
    dsimp [ip_self, (≥)],
    apply le_iff_eq_or_lt.2,
    by_cases (x = 0),

    left,
    rw [h],
    simp,

    right,
    have w := pos_def x h,
    exact w,
end

@[simp] lemma swap_re (x y : α) : (x†y).re = (y†x).re :=
begin
    rw [conj_symm y x],
    simp only [conj_re],
end

@[simp] lemma add_swap (x y : α) : x†y + y†x = 2*(x†y).re :=
begin
    rw [conj_symm y x],
    simp [ext_iff],
    ring,
end

@[simp] lemma add_in_snd_coord (x y z : α) : x†(y+z) = (x†y)+(x†z) :=
begin
    have h := linearity y z x 1,
    simp only [one_smul, one_mul] at h,
    rw [←conj_inj, conj_add, ←conj_symm, ←conj_symm x y, ←conj_symm] at h,
    exact h,
end

@[simp] lemma mul_in_snd_coord (x y : α) (a : ℂ) : x † (a • y) = (conj a) * (x†y) :=
begin
    rw [conj_symm],
    apply conj_inj.1,
    conv {to_rhs, rw [conj_symm, ←conj_mul]},
    simp only [conj_conj],
    have h := linearity y 0 x a,
    simp only [right_orthog_to_zero, add_zero] at h,
    exact h,
end

@[simp] lemma ip_self_add (x y : α) : (ip_self (x+y)).re = (ip_self x).re + 2*(x†y).re + (ip_self y).re :=
begin
    dsimp [ip_self],
    simp,
    ring,
end

end inner_product_space
