import tactic.interactive

/-
It's time to learn about universes!

This assignment is hopefully fairly quick, but will walk you through the
universe polymorphism issues involved in defining categories in Lean.
-/

-- Here's a simple attempt at defining a category.
-- The parameter `C` describes the objects of the category.
class category (C : Type) :=
(hom : C → C → Type)
(id : Π X : C, hom X X)
(comp : Π {X Y Z : C}, hom X Y → hom Y Z → hom X Z)
(comp_id : Π {X Y : C} (f : hom X Y), comp f (id Y) = f)
(id_comp : Π {X Y : C} (f : hom X Y), comp (id X) f = f)
(assoc : Π {W X Y Z : C} (f : hom W X) (g : hom X Y) (h : hom Y Z), comp (comp f g) h = comp f (comp g h))

-- However, this definition is no good: we can't define the category of types:
instance category_of_types_broken : category Type :=
{ hom := λ X Y, X → Y }

-- To fix this, you're going to need to modify the definition above,
-- to fix the universe levels.

-- Question 0: Explain why the definition above wasn't useful, perhaps
-- mentioning Russell's paradox.

-- Here's one attempt:

class category_1 (C : Type 1) :=
(hom : C → C → Type)
(id : Π X : C, hom X X)
(comp : Π {X Y Z : C}, hom X Y → hom Y Z → hom X Z)
(comp_id : Π {X Y : C} (f : hom X Y), comp f (id Y) = f)
(id_comp : Π {X Y : C} (f : hom X Y), comp (id X) f = f)
(assoc : Π {W X Y Z : C} (f : hom W X) (g : hom X Y) (h : hom Y Z), comp (comp f g) h = comp f (comp g h))

-- Question 1: fill in the remaining fields of this definition.
instance category_of_types : category_1 Type :=
{ hom := λ X Y, X → Y,
  id := λ X, λ x, x,
  comp := λ X Y Z, λ f g, λ x, g (f x),
  comp_id := by {intros X Y f, simp},
  id_comp := by {intros X Y f, simp},
  assoc := by {intros W X Y Z f g h, simp}
}

-- However, this variant has its own problems. A standard solution to Russell's
-- paradox about "the set of all sets" (resolved in Lean's dependent type theory
-- by the typing judgement `Type : Type 1`) is to consider all subsets of some
-- fixed 'big' set, rather than "all sets".

-- Question 2: Decide whether `C` below should be `category` or `category_1`,
-- and fill in the remaining fields.
instance category_of_subsets (X : Type) : category (set X) :=
{ hom := λ P Q, { x // P x } → { x // Q x },
  id := λ P, λ x, x,
  comp := λ P Q R, λ p q, λ x, q (p x),
  comp_id := by {intros P Q f, simp},
  id_comp := by {intros P Q f, simp},
  assoc := by {intros P Q R f g h, simp}
}

-- We've now got a conundrum: for some reasonable examples, we want the
-- objects and morphisms to live in the same universe, while for other
-- examples we want the objects to live one universe level higher than
-- the morphisms.

-- In ZFC based category theory, these two variants of the notion of a category
-- are called "small categories" and "large categories".

-- Rather than duplicate everything we want to prove about categories
-- (or worse: we'll need to worry about four different sorts of functors,
-- as the source and target categories could individually be small or large!)
-- in the mathlib category theory library we've made a "universe polymorphic"
-- definition, which is essentially this one:

universes v u

class pcategory (C : Type u) :=
(hom : C → C → Type v)
(id : Π X : C, hom X X)
(comp : Π {X Y Z : C}, hom X Y → hom Y Z → hom X Z)
(comp_id : Π {X Y : C} (f : hom X Y), comp f (id Y) = f)
(id_comp : Π {X Y : C} (f : hom X Y), comp (id X) f = f)
(assoc : Π {W X Y Z : C} (f : hom W X) (g : hom X Y) (h : hom Y Z), comp (comp f g) h = comp f (comp g h))

-- Question 3:
-- Work out the appropriate values of the universe parameters `p`, `q`, `r`, `s`
-- below, and then verify that the same fields you used above can be used to
-- complete the following two definitions:
-- (Hint: substitute fixed large values, like p=5, q=10, and read the error messages...)
instance category_of_types' : pcategory.{0 1} Type :=
{ hom := λ X Y, X → Y,
  id := λ X, λ x, x,
  comp := λ X Y Z, λ f g, λ x, g (f x),
  comp_id := by {intros X Y f, simp},
  id_comp := by {intros X Y f, simp},
  assoc := by {intros W X Y Z f g h, simp}
}

instance category_of_subsets' (X : Type) : pcategory.{0 0} (set X) :=
{ hom := λ P Q, { x // P x } → { x // Q x },
  id := λ P, λ x, x,
  comp := λ P Q R, λ p q, λ x, q (p x),
  comp_id := by {intros P Q f, simp},
  id_comp := by {intros P Q f, simp},
  assoc := by {intros P Q R f g h, simp}
}

-- Question 4:
-- Complete the following definitions:
universes v₁ u₁ v₂ u₂

structure Functor (C : Type u₁) [pcategory.{v₁ u₁} C] (D : Type u₂) [pcategory.{v₂ u₂} D] :=
(obj : C → D)
(map : Π {X Y : C}, pcategory.hom X Y → pcategory.hom (obj X) (obj Y))
(id_map : Π X : C, map (pcategory.id X) = pcategory.id (obj X))
(map_comp : Π X Y Z : C, Π f : pcategory.hom X Y, Π g : pcategory.hom Y Z, map (pcategory.comp f g) = pcategory.comp (map f) (map g))
-- Hint: there are two missing fields here, giving the axioms for functors.

def List : Functor Type Type :=
{ obj := λ α, list α,
  map := λ α β : Type, λ f : pcategory.hom α β, λ L, list.map f L,
  id_map := by {intros X, dsimp [pcategory.id], ext, induction x, simp, dsimp [list.map], rw [x_ih]},
  map_comp := by {intros X Y Z f g, simp, ext, dsimp [pcategory.comp], induction x,
                  simp, dsimp [list.map], rw [x_ih],}}

-- Question 5:
-- Complete the following definitions:

structure NaturalTransformation
  {C : Type u₁} [pcategory.{v₁ u₁} C] {D : Type u₂} [pcategory.{v₂ u₂} D]
  (F G : Functor C D) :=
(app : Π X : C, pcategory.hom (F.obj X) (G.obj X))
(naturality : Π X Y : C, Π f : pcategory.hom X Y, pcategory.comp (F.map f) (app Y) = pcategory.comp (app X) (G.map f))

namespace NaturalTransformation
def id
  {C : Type u₁} [pcategory.{v₁ u₁} C] {D : Type u₂} [pcategory.{v₂ u₂} D]
  (F : Functor C D) : NaturalTransformation F F :=
{app := λ X : C, pcategory.id (F.obj X), 
 naturality := by {intros X Y f, rw [pcategory.comp_id, pcategory.id_comp]}}

def comp
  {C : Type u₁} [pcategory.{v₁ u₁} C] {D : Type u₂} [pcategory.{v₂ u₂} D]
  {F G H : Functor C D}
  (α : NaturalTransformation F G) (β : NaturalTransformation G H) : NaturalTransformation F H :=
{app := λ X : C, pcategory.comp (α.app X) (β.app X), 
 naturality := by {intros X Y f, rw [←pcategory.assoc, α.naturality, pcategory.assoc, pcategory.assoc],
 apply congr_arg, rw [β.naturality]}}
 
-- Hint: you may find `conv` helpful.
end NaturalTransformation

-- Here's the crux of the whole assignment: understand what the correct values
-- of `p` and `q` are in this definition, then complete the definition.
-- Hint: you may like to prove an extensionality lemma for natural transformations,
-- and appropriate simp lemmas.
instance {C : Type u₁} [pcategory.{v₁ u₁} C] {D : Type u₂} [pcategory.{v₂ u₂} D] :
  pcategory.{p q} (Functor C D) :=
{ hom := λ F G, NaturalTransformation F G }

-- Question 6:
-- What universe does `NaturalTransformation F G` live in? Why?
-- Hint: a really good answer will use the word 'impredicativity' somewhere
-- along the way.
