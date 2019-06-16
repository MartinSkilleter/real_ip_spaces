import analysis.normed_space.basic
import tactic.basic

noncomputable theory

open real

variables {α : Type*} {β : Type*}

lemma awesome_mt {p q : Prop} [decidable p] [decidable q] : p → q ↔ (¬q → ¬p) :=
by {constructor, exact mt, have w := @mt ¬q ¬p, rw [not_not, not_not] at w, exact w}

class has_ℝ_inner_product (α : Type*) := (inner_product : α → α → ℝ)

export has_ℝ_inner_product (inner_product)

class ℝ_inner_product_space (α : Type*) [add_comm_group α] [vector_space ℝ α] extends has_ℝ_inner_product α :=
(conj_symm : ∀ (x y : α), inner_product x y = inner_product y x)
(linearity : ∀ (x y z : α), ∀ (a : ℝ), inner_product (a • x + y) z = a * inner_product x z + inner_product y z)
(pos_def : ∀ (x : α), x ≠ 0 → inner_product x x > 0)

variables [decidable_eq α] [add_comm_group α] [vector_space ℝ α] [ℝ_inner_product_space α]

-- Scott:
-- This is very unusual notation, and wouldn't survive a PR.
-- Dagger is widely used just for adjoints, so x † y looks too much like
-- "the adjoint of x, times y"

-- I tried the physicists' notation, `⟨x|y⟩`, but it breaks using anonymous constructors.
-- notation `⟨` x `|` y `⟩` := inner_product x y

-- Maybe?
-- notation `⟪` x `∥` y `⟫` := inner_product x y

precedence `†` : 70
infix `†` := inner_product

-- Scott:
-- All these lemmas need to be inside a namespace, e.g. inner_product_space

lemma conj_symm (x y : α) : x † y = y † x :=
by apply ℝ_inner_product_space.conj_symm

lemma linearity (x y z : α) (a : ℝ) : (a • x + y) † z = a * (x † z) + y † z :=
by apply ℝ_inner_product_space.linearity

-- Scott:
-- Should just be called `add_left`. Where's `add_right`?
@[simp] lemma add_in_fst_coord (x y z : α) : (x + y) † z = x † z + y † z :=
by {have h := linearity x y z 1,
    simp only [one_mul, one_smul] at h,
    exact h}

-- Scott:
-- Why do you have this? It's just a copy of ℝ_inner_product_space.pos_def?
lemma pos_def (x : α) : x ≠ 0 → inner_product x x > 0 :=
by apply ℝ_inner_product_space.pos_def

@[simp] lemma right_orthog_to_zero (x : α) : 0 † x = 0 :=
by {have h := linearity 0 0 x 1,
    rw [add_zero, one_mul, smul_zero] at h,
    conv at h {to_lhs, rw [←add_zero (0†x)]},
    exact (add_left_cancel h).symm}

@[simp] lemma left_orthog_to_zero (x : α) : x † 0 = 0 :=
by {rw [conj_symm],
    exact right_orthog_to_zero x}

-- Scott:
-- If your tactic block begins with `intros`, just move the argument before the
-- colon and name it.
lemma zero_of_orthog_to_all {y : α} : (∀ (x : α), x † y = 0) → y = 0 :=
by {intros h,
    have w := mt (pos_def y),
    simp [le_iff_lt_or_eq] at w,
    exact (w (or.inr (h y)))}

-- Scott:
-- Use _left and _right naming schemes, the prime is no good.
lemma zero_of_orthog_to_all' {y : α} : (∀ (x : α), y † x = 0) → y = 0 :=
begin
    intros h,
    apply @zero_of_orthog_to_all α _ _ _,
    intros x,
    rw [conj_symm],
    exact h x,
end

-- Scott:
-- rename to mul_left?
@[simp] lemma mul_in_fst_coord (x z : α) (a : ℝ) : (a•x)†z = a*(x†z) :=
by {rw [←add_zero (a•x), ←add_zero (a*(x†z)), ←right_orthog_to_zero z],
    exact linearity x 0 z a}

-- Scott:
-- rename to left_ext? (remember this is going to be inside an `inner_product` namespace)
-- add right_ext?
lemma ip_all_unique (x y : α) : (∀ (z : α), x†z = y†z) → x = y :=
begin
    intros h,
    have k : ∀ (z : α), (x-y)†z = 0 := begin
        intros z,
        simp,
        rw [←add_right_neg (y†z), ←neg_one_mul, ←mul_in_fst_coord, neg_one_smul],
        apply (congr_arg (λ g, g + (-y)†z)),
        exact h z,
    end,
    have k' := zero_of_orthog_to_all' k,
    exact sub_eq_zero.1 k',
end

-- Scott:
-- I'm not sure this is worth having.
-- Perhaps rename it as `norm_sq`? I definitely don't like the name at the moment.
@[reducible] def ip_self : α → ℝ := λ x, x†x

@[simp] lemma ip_self_zero : ip_self (0 : α) = 0 := right_orthog_to_zero 0

-- Scott:
-- I golfed this one: check the diff.
lemma zero_of_ip_self_zero (x : α) (h : ip_self x = 0) : x = 0 :=
begin
  by_contradiction,
  exact ne_of_gt (pos_def x a) h,
end

-- Scott:
-- Similarly:
lemma zero_iff_ip_self_zero (x : α) : ip_self x = 0 ↔ x = 0 :=
⟨zero_of_ip_self_zero x, by { rintro rfl, simp }⟩

-- Scott:
-- If we want to PR lots of these will need to be golfed in similar ways.
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
    apply le_iff_eq_or_lt.2,
    by_cases (x = 0),

    left,
    rw [h],
    simp,

    right,
    exact pos_def x h,
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
by {dsimp [ip_self],
    rw [←@neg_one_smul ℝ α _ _ _ x, mul_in_fst_coord, mul_in_snd_coord,
        ←mul_assoc, ←neg_eq_neg_one_mul, neg_neg, one_mul]}

