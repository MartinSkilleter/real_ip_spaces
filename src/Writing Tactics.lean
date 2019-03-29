import tactic.basic
import tactic.ext
import data.set.basic

meta def my_tactic : tactic unit := `[exact 7, refl]
example : ∃ (n : ℕ), n = 7 :=
begin
    split,
    swap,
    my_tactic,
end

meta def my_tactic_5 : tactic unit :=
do `[induction a],
    tactic.reflexivity,
    `[simpa]