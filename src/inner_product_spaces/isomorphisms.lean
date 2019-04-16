import inner_product_spaces.basic
import init.algebra.functions

noncomputable theory

open function complex

universes u v

variables {α : Type u} {β : Type v}
variables [decidable_eq α] [add_comm_group α] [vector_space ℂ α]
variables [decidable_eq β] [add_comm_group β] [vector_space ℂ β]  [inner_product_space β]
variables {f : linear_map ℂ α β}

def hom_inner_product (x y : α) := (f x)†(f y)

instance hom_has_inner_product : has_inner_product α := ⟨hom_inner_product⟩

lemma hom_conj_symm : ∀ (x y : α), x†y = conj (y†x) := sorry

lemma hom_linearity : ∀ (x y z : α) (a : ℂ), (a•x+y)†z = a*(x†z) + y†z := sorry

lemma hom_pos_def : ∀ (x : α), x ≠ 0 → (x†x).re > 0 := sorry

instance hom_inner_product_space : inner_product_space α :=
begin
    refine {conj_symm := hom_conj_symm, linearity := hom_linearity, pos_def := hom_pos_def},
end




