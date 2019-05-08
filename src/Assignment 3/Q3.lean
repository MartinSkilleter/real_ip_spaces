import tactic.interactive tactic.basic
import tactic.basic
import tactic.ring
import data.real.basic

open tactic real

meta def get_tactic_state : tactic tactic_state := λ s, interaction_monad.result.success s s

-- Takes a single tactic and the complexity function and checks if it is "less complex" than the previous best
meta def run_each (c : tactic ℕ) (best : ℕ) (s₀ : tactic_state) (t : tactic unit) : tactic ℕ
| s := match t s₀ with -- Get the current tactic state and try running the tactic on the original tactic state
    | result.success _ s₁ := do match c s₁ with | result.success c₁ _ := -- If it succeeds, try running our complexity function
                                                   if (c₁ < best) then result.success c₁ s₁ -- If the result is less complex, store the new complexity
                                                                                            -- and the new tactic state (before the complexity function was run)
                                                                  else result.success best s -- If it is more complex, change nothing
                                                | _ := result.success best s -- If it fails, change nothing
                                end
    | _ := result.success best s -- If it fails, change nothing
    end

-- Recursor function to deal with a list of tactics. Terminates if the list is done.
-- Otherwise, use run_each to check if the head of the list is the best and then repeat.
meta def run_list (c : tactic nat) (s₀ : tactic_state): ℕ → list (tactic unit) → tactic unit
| _ [] := do skip -- We have no more tactics left to try
| best (t :: ts) := do best' ← run_each c best s₀ t, -- Run the first tactic and store its complexity
                        out ← run_list best' ts, -- Repeat on tail of list
                        return out

-- Note that the best tactic state is carried along by being set as current tactic state
-- Can be invoked using the syntax "run_best c [`[simp], `[refl], `[trivial, dsimp]]"
-- Tried to remove the backtick syntax and use an interactive block, but Keeley
-- explained that these are not foundational in Lean and are instead "tacked on",
-- so a new parser would have had to be written. This would have been difficult,
-- hard to maintain and likely quite inefficient.
meta def run_best (c : tactic nat) (L : list (tactic unit)) : tactic unit :=
do s₀ ← get_tactic_state,
   run_list c s₀ 1000000000 L -- A large starting best value is used, because the natural numbers have no upper bound
   -- and it needs to be larger than the output of the complexity function after the first iteration

example : true ∨ (false ∧ true) :=
begin
    run_best (num_goals) [`[trivial, refl], `[constructor], `[ring]], -- Constructor is only tactic that makes progress, so constructor runs
    run_best (num_goals) [`[intros], `[trivial]], -- Trivial finishes the proof
end


