import tactic.interactive tactic.basic

open tactic

meta def run_each (c : tactic ℕ) (best : ℕ) (t : tactic unit) : tactic ℕ
| s := match t s with
    | result.success _ s₁ := do match c s₁ with | result.success c₁ s₂ :=
                                                   if (c₁ < best) then result.success c₁ s₂ 
                                                                  else result.success best s
                                                | _ := result.success best s
                                end
    | result.exception _ _ _ := result.success best s

#print lock_tactic_state
