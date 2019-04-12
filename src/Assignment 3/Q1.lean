import tactic.interactive

open tactic

meta def get_goals_at_indices: list ℕ → list expr → tactic unit
| [] gs := set_goals []
| _ [] := fail "Insufficient goals"
| is gs := sorry 

open nat
meta def focus_goals [indices : list ℕ] {ts : list (tactic unit)}: tactic unit :=
do gs ← get_goals_at_indices indices get_goals,
   






#print focus


