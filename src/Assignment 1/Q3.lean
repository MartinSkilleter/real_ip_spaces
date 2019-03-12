import data.list

namespace hidden

def len {α : Type} : list α -> ℕ
 | [] := 0
 | (hd :: tl) := 1 + len tl

def concat {α : Type} : list (list α) -> list α
 | [] := []
 | ([] :: L) := concat L
 | ((a :: l) :: L) := a :: (concat (l :: L))

def nonempty {α : Type} : list α -> bool
 | [] := false
 | (_ :: _) := true

lemma nonempty_has_head {α : Type} (L : list α) : nonempty L → ∃ (hd : α), ∃ (tl : list α), hd :: tl = L :=
begin
    intros h,
    have nonempty_def : ∃ (hd : α), ∃ (tl : list α), hd :: tl = L, begin
        cases L,
        { have h₂ : nonempty [] = false, by rw nonempty,
          simp [absurd],
          have h : false, begin
            trivial,
          end,
        use h,
        },
        { use L_hd,
          use L_tl,
        },
    end,
    apply nonempty_def,
end

theorem nonempty_concatenation {α : Type} (L : list (list α)) : 
(nonempty L ∧ ∀ (l ∈ L), nonempty l) → nonempty (concat L) :=
begin
    intros h,
    cases h with h_l h_r,
    {have h₁ : ∃ (a : list α), ∃ (l : list (list α)), a :: l = L, by apply nonempty_has_head L h_l,
     cases h₁ with hd h₂,
     cases h₂ with tl eq,
     have h₃ : hd ∈ L, sorry,
     have h₄ : ↥(nonempty hd), by apply h_r hd h₃,
     have h₅ : ∃ (a : α), ∃ (b : list α), a :: b = hd, by apply nonempty_has_head hd h₄,
     cases h₅ with a b,
     cases b with b eq,

     

     sorry
     
    
    
    },

end

end hidden