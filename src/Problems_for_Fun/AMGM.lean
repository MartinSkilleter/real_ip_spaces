import data.real.basic

noncomputable theory

open real finset

def arithmetic_mean (S : list ℝ) : ℝ :=
(list.sum S) / (list.length S)

-- No instance for has_pow ℝ ℝ
-- def geometric_mean (S : finset ℝ) {h : ∀ (s : ℝ), s ∈ S → s > 0} : ℝ :=
-- (finset.prod S id) ^ (1 / (finset.card S : ℝ))

theorem AM_geq_GM (S : list ℝ) (h : ∀ (s : ℝ), s ∈ S → s > 0) :
(arithmetic_mean S)^(list.length S) ≥ list.prod S :=
begin
    dsimp [arithmetic_mean],
    induction (S),
    
    {simp,
     exact le_refl 1,
    },

    {simp,
     rw [add_comm 1, pow_succ],
     sorry,
    }


end