import tactic.interactive
import init.meta.interaction_monad

open tactic

variable {α : Type}

def find_max : list ℕ → ℕ → ℕ
| [] so_far := so_far
| (h :: tl) so_far := if h > so_far then find_max tl h else find_max tl so_far

meta def find_wanted_goals : list ℕ → ℕ → ℕ → list expr → tactic (list expr)
| tgts crnt max gls := if crnt > max then return [] 
                                     else match gls with
                                     | [] := fail "Not enough goals!"
                                     | (g::gs) := if crnt ∈ tgts then 
                                                  do out ← find_wanted_goals tgts (crnt+1) max gs,
                                                     return ([g]++out)
                                                     else do out ← find_wanted_goals tgts (crnt+1) max gs,
                                                             return out
                                     end

meta def find_goals : list ℕ → tactic unit                                                 
| tgts := do let max := find_max tgts 0,
             gls ← get_goals,
             found_goals ← find_wanted_goals tgts 1 max gls,
             set_goals (found_goals)

meta def set_tactic_state (new_state : tactic_state) : tactic unit := λ s, (do skip new_state)

meta def get_tactic_state : tactic tactic_state := λ s, interaction_monad.result.success s s

meta def tactic.interactive.focus_goals (pe : interactive.parse lean.parser.pexpr) (t : tactic.interactive.itactic) : tactic unit :=
do s ← get_goals,
   e ← to_expr pe,
   tgts ← eval_expr (list ℕ) e,
   find_goals tgts,
   t,
   gls ← get_goals,
   if gls ≠ [] then do set_goals s, fail "Failed to discharge the goals!" else
   interactive.recover

-- meta def tactic.interactive.focus_goals (pe : interactive.parse lean.parser.pexpr) (t : tactic.interactive.itactic) : tactic unit :=
-- do s ← get_goals,
--    e ← to_expr pe,
--    tgts ← eval_expr (list ℕ) e,
--    find_goals tgts,
--    t,
--    gls ← get_goals,
--    if gls ≠ [] then do set_goals s, fail "Failed to discharge the goals!" else
--    interactive.recover

def find_N : ℕ → list ℕ
| 0 := []
| (N+1) := (find_N N) ++ [N+1]

-- meta def recover_goals : list ℕ → list expr → tactic (list expr)
-- | tgts gls := do let max := find_max tgts 0,
--                  let 
                 


   


