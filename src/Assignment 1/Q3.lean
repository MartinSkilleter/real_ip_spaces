import data.list

namespace hidden

def len {α : Type} : list α -> ℕ
 | [] := 0
 | (x :: L) := 1 + len L

def concat {α : Type} : list (list α) -> list α
 | [] := []
 | ([] :: L) := concat L
 | ((a :: l) :: L) := a :: (concat (l :: L))

def nonempty {α : Type}: list α -> bool
 | [] := false
 | L := true

theorem nonempty_concatenation {α : Type} (L : list (list α)) : 
nonempty L ∧ ∀ (l ∈ L), nonempty l → nonempty (concat L) :=
sorry

 end hidden