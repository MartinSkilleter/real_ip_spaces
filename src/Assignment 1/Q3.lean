import data.list

def len {α : Type} : list α -> ℕ
 | [] := 0
 | (x :: L) := 1 + len L

def concat {α : Type} : list (list α) -> list α
 | [] := []
 | ([] :: L) := concat L
 | ((a :: l) :: L) := a :: (concat (l :: L))

#reduce (len [1, 2, 3])