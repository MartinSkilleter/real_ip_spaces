import analysis.normed_space.basic
import tactic.basic

noncomputable theory

open real

variables {α : Type*} {β : Type*}

lemma awesome_mt {p q : Prop} [decidable p] [decidable q] : p → q ↔ (¬q → ¬p) :=
begin
    split,

    exact mt,

    have w := @mt ¬q ¬p,
    rw [not_not, not_not] at w,
    exact w,
end

class has_ℝ_inner_product (α : Type*) := (inner_product : α → α → ℝ)

export has_ℝ_inner_product (inner_product)

class ℝ_inner_product_space (α : Type*) [add_comm_group α] [vector_space ℝ α] extends has_ℝ_inner_product α :=
(conj_symm : ∀ (x y : α), inner_product x y = inner_product y x)
(linearity : ∀ (x y z : α), ∀ (a : ℝ), inner_product (a • x + y) z = a * inner_product x z + inner_product y z)
(pos_def : ∀ (x : α), x ≠ 0 → inner_product x x > 0)

variables [decidable_eq α] [add_comm_group α] [vector_space ℝ α] [ℝ_inner_product_space α]

precedence `†` : 70
infix `†` := inner_product

lemma conj_symm (x y : α) : x † y = y † x :=
by apply ℝ_inner_product_space.conj_symm

lemma linearity (x y z : α) (a : ℝ) : (a • x + y) † z = a * (x † z) + y † z :=
by apply ℝ_inner_product_space.linearity

@[simp] lemma add_in_fst_coord (x y z : α) : (x + y) † z = x † z + y † z :=
by {have h := linearity x y z 1,
    simp only [one_mul, one_smul] at h,
    exact h}

lemma pos_def (x : α) : x ≠ 0 → inner_product x x > 0 :=
by apply ℝ_inner_product_space.pos_def

@[simp] lemma right_orthog_to_zero (x : α) : 0 † x = 0 :=
begin
    have h := linearity 0 0 x 1,
    simp only [add_zero, one_mul, smul_zero] at h,
    have w := @add_left_cancel ℝ _ (0†x) 0 (0†x),
    simp only [add_zero] at w,
    exact (w h).symm,
end

@[simp] lemma left_orthog_to_zero (x : α) : x † 0 = 0 :=
begin
    have h := right_orthog_to_zero x,
    rw conj_symm at h,
    exact h,
end

lemma zero_of_orthog_to_all {y : α} : (∀ (x : α), x † y = 0) → y = 0 :=
begin
    intros h,
    have w := mt (pos_def y),
    simp [le_iff_lt_or_eq] at w,
    exact (w (or.inr (h y))),
end

@[simp] lemma mul_in_fst_coord (x z : α) (a : ℝ) : (a•x)†z = a*(x†z) :=
begin
    have h := linearity x 0 z a,
    simp only [right_orthog_to_zero, add_zero] at h,
    exact h,
end

def ip_self : α → ℝ := λ x, x†x

@[simp] lemma ip_self_zero : ip_self (0 : α) = 0 :=
begin
    dsimp [ip_self],
    exact (right_orthog_to_zero 0),
end

lemma zero_of_self_ip_zero (x : α) : ip_self x = 0 → x = 0 :=
begin
    rw awesome_mt,
    intros h,
    exact (ne_of_gt (pos_def x h)),
end

lemma zero_iff_ip_self_zero (x : α) : ip_self x=0 ↔ x=0 :=
begin
    split,

    exact zero_of_self_ip_zero x,

    intros h,
    rw [h],
    exact ip_self_zero,
end

lemma neq_zero_iff_ip_self_neq_zero (x : α) : ip_self x ≠ 0 ↔ x ≠ 0 :=
begin
    split,

    apply mt,
    exact (zero_iff_ip_self_zero x).2,

    apply mt,
    exact (zero_iff_ip_self_zero x).1,
end

@[simp] lemma ip_self_nonneg (x : α) : ip_self x ≥ 0 :=
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

@[simp] lemma add_in_snd_coord (x y z : α) : x†(y+z) = (x†y)+(x†z) :=
by {rw [conj_symm, add_in_fst_coord, conj_symm, conj_symm z]}

@[simp] lemma mul_in_snd_coord (x y : α) (a : ℝ) : x † (a • y) = a * (x†y) :=
by {rw [conj_symm, mul_in_fst_coord, conj_symm]}

@[simp] lemma ip_self_add (x y : α) : ip_self (x+y) = ip_self x + 2*(x†y) + ip_self y :=
begin
    dsimp [ip_self],
    simp,
    rw [conj_symm y x],
    ring,
end

@[simp] lemma ip_self_neg_eq (x : α) : ip_self (-x) = ip_self x :=
begin
    dsimp [ip_self],
    rw [←@neg_one_smul ℝ α _ _ _ x],
    simp only [mul_in_fst_coord, mul_in_snd_coord],
    simp,
end

