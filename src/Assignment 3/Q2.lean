import algebra.group
import data.finset

variables {α : Type} {G : comm_semigroup α} 

@[derive decidable_eq]
inductive semigroup_expr (n : ℕ)
| const : fin n → semigroup_expr
| mul : semigroup_expr → semigroup_expr → semigroup_expr

notation `SE` := semigroup_expr

open semigroup_expr

def to_list {n : ℕ}: SE n → list (fin n)
| (const a) := [a]
| (mul a b) := (to_list a) ++ (to_list b)

def to_multiset {n : ℕ}: SE n → multiset (fin n)
| (const a) := {a}
| (mul a b) := (to_multiset a) + (to_multiset b)

def eval [semigroup α] {n : ℕ} : SE n → (fin n → α) → α
| (const a) f := f a
| (mul a b) f := (eval a f) * (eval b f)

lemma sing_not_append {a : α} {b c : list α} : [a] = b ++ c → (b = [a] ∧ c = []) ∨ (b = [] ∧ c = [a]) :=
begin
    intros h,
    cases b,
    right,
    split,
    trivial,
    simp at h,
    exact h.symm,

    cases c,
    left,
    split,
    simp at h,
    cases h,
    simp [h_right],
    exact h_left.symm,
    trivial,

    simp at h,
    contradiction,
end

theorem main_theorem_1 [semigroup α] {n : ℕ} (e₁ e₂ : SE n) (f : fin n → α) (x₁ x₂ : α) 
(h : to_list e₁ = to_list e₂) (v₁ : eval e₁ f = x₁) (v₂ : eval e₂ f = x₂) : x₁ = x₂ :=
begin
    cases e₁ with e₁ e₁ e₁',
    cases e₂ with e₂ e₂ e₂',
    dsimp [eval] at v₁,
    dsimp [to_list] at h,
    dsimp [eval] at v₂,
    have h₁ := list.head_eq_of_cons_eq h,
    have h₂ := congr_arg f h₁,
    rw [v₁, v₂] at h₂,
    exact h₂,

    dsimp [eval] at v₁,
    dsimp [to_list] at h,
    dsimp [eval] at v₂,
    have h₁ := sing_not_append h,
    cases h₁,
    cases h₁,
    cases e₂,
    dsimp [to_list] at h₁_left,
    have h₂ := list.head_eq_of_cons_eq h₁_left,
    have h₃ := congr_arg f h₂,
    dsimp [eval] at v₂,
    sorry,

    cases h₁,
    

end