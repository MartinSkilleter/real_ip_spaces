import data.list

namespace hidden

variable {α : Type}

def len {α : Type} : list α → ℕ
 | [] := 0
 | (hd :: tl) := 1 + len tl

def concat {α : Type} : list (list α) → list α
 | [] := []
 | (hd :: tl) := hd ++ (concat tl)

def nonempty {α : Type} : list α → Prop
 | [] := false
 | (_ :: _) := true

-- If the 2nd of two lists being concatenated is non-empty then their concatenation is non-empty
lemma nonempty_tail (L M : list α) (h : nonempty M) : nonempty (L ++ M) := 
begin
    cases L,
    {simp,
    exact h},
    {simp}
end

-- If the 1st of two lists being concatenated is non-empty then their concatenation is non-empty
-- This is the lemma that is actually used in the proof of our theorem, but the other lemma
-- is needed for this proof
lemma nonempty_head (L M : list α) (h : nonempty L) : nonempty (L ++ M) := 
begin
    cases M,
    {simp,
    exact h},
    {have h₂ : nonempty (M_hd :: M_tl), begin
        dsimp [nonempty],
        trivial,
    end,
    apply nonempty_tail,
    exact h₂,
    }
end

-- Given a non-empty list of lists, all of the elements of which are also non-empty, we show that the full concatenation is non-empty
theorem nonempty_concat_of_nonempty_is_nonempty 
(L : list (list α)) (h : nonempty L) (w : ∀ (m ∈ L), nonempty m) : nonempty (concat L) :=
begin
  cases L,
  {cases h},
  {dsimp [concat],
   apply nonempty_head,
   apply w,
   simp,
  }
end

end hidden