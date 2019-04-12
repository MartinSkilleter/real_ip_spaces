import tactic.interactive

def X := [1,2,3]
def g (n : ℕ) := [n, 7*n]

def Z : list ℕ :=
do x ← X,
   y ← g x,
   return y

#eval Z
-- set_option pp.notation false
#print Z
-- https://github.com/leanprover-community/mathlib/blob/master/docs/extras/tactic_writing.md

def h (n : ℕ) := if 2 ∣ n then some (n/2) else none

def Y (n : ℕ) :=
do n ← h n,
   n ← h n,
   n ← h n,
   return n

#eval Y 24
#eval Y 12

def monad_list : monad list := by apply_instance
#print monad_list
#print list.monad

def option_monad : monad option :=
{ pure := @option.some, bind := λ α β o f, match o with | none := none | some a := f a end, map := λ α β f o, match o with | none := none | some a := some (f a) end}

example : is_lawful_monad option :=
{pure_bind := begin intros, refl, end,
 bind_assoc := begin intros, cases x,
 refl,
 refl, end}

def Z' : list ℕ :=
do x ← X,
   y ← g x,
   guard (3 ∣ y),
   return y

#eval Z'

/-
A monad is just a monoid object in the monoidal category
of natural endomorphisms of a functor.

To a computer scientist, all functors are functors from Type to Type.
α → list α is a functor. So is option
-/

/-
A functor from C to D, takes objects of C to objects of D,
and arrows in C to arrows in D, respecting all the structure 
(sources, targets, identities, compositions).

A natural transformation from a function `F : C ⥤ D` to another `G : C ⥤ D`,
compares the values of `F` and `G`. That is, for each object `X : C`,
it gives an arrow (in `D`) from `F.obj X` to `G.obj X`.

It satisfies a compatibility condition: for every arrow in `C`, `f : X ⟶ Y`.
Then the two arrows F X  → F Y → G Y and F X → G X → G Y are equal:

* GL_n is a functor from rings to groups under matrix multiplication. det is a
natural transformation from GL_n to GL_1, as factors Ring ⥤ Grp.

A monad is a functor `T` from Type to Type, along with natural transformations
`η : 1 ⟶ T` and `μ : TT ⟶ T`.
i.e. for each Type α, the component of η at α is a function from α → T α (`pure`).
i.e. for each Type α, the component of μ at α is a function from T T α → T α.
-/

def state_ (σ : Type) (α : Type) := σ → σ × α

instance (σ : Type) : monad (state_ σ) :=
{pure := λ α a s, (s, a),
 bind := λ α β f k s, 
 begin have p := f s, clear s f, have q := k p.2, clear k, exact q p.1, end}

#print tactic
meta def tactic_monad : monad tactic := by apply_instance
#print tactic_monad

#print interaction_monad.monad

open tactic
meta def swap' : tactic unit :=
do gs ← get_goals,
   match gs with
    | (a :: b :: rem) := set_goals (b :: a :: rem)
    | _ := skip
   end

meta def swap'' : tactic unit :=
do a :: b :: t ← get_goals | fail "There must be at least two goals!",
   set_goals (b :: a :: t)

example : true :=
begin
    success_if_fail {swap''},
    trivial,
end

example : true ∧ 1=1 :=
begin
    split,
    swap'',
    refl,
    trivial,
end

meta def swap''' : tactic unit :=
do a :: b :: t ← get_goals | fail "There must be at least two goals!",
   set_goals [b,a]

example : true ∧ true ∧ 1 = 2 :=
begin
    (do result >>= trace),
    split; [skip, split],
    (do result >>= trace),
    swap''',
    (do result >>= trace),
    trivial,
    (do result >>= trace),
    trivial,
    (do result >>= trace),
    -- :-) .... :-(
    recover,
    sorry,
end

meta def show_locals : tactic unit :=
do ctx ← local_context,
   trace ctx,
   ctx.mmap infer_type >>= trace,
   skip

meta def target' : tactic expr :=
do gs ← get_goals,
   match gs with
    | [] := fail "No tactics left!"
    | (h :: rem) := infer_type h
end

meta def try_0_on_all_goals : tactic unit :=
`[all_goals {try {exact 0}}]

#check unify
meta def try_0_on_all_goals' : tactic unit :=
do gs ← get_goals,
   z ← to_expr ``(0 : ℕ),
   trace gs,
   gs.mmap' (λ g, try_core $ unify g z),
   trace gs,
   skip

set_option pp.instantiate_mvars false
def bar : ℕ × ℕ × list ℤ :=
begin
    split; [skip, split],
    try_0_on_all_goals',
    (do result >>= trace),
end
