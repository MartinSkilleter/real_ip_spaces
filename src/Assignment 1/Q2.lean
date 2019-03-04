import data.finset
import data.nat.prime
import data.real.basic

open nat
open finset
open int

-- n is the length of the arithmetic sequence we want, a is the starting number
-- and k is the common difference
theorem green_tao : Prop :=
∀ (n : ℕ), ∃ (a k : ℕ), ∀ (i < n), prime (a + i * k)

-- The nth partial sum of a series Σf
def P_n (f : ℝ → ℝ) (n : ℕ) : ℝ :=
sum (multiset {x : ℝ | ∃(m : ℕ), x = f m})

theorem apery's_conjecture : Prop :=
∃ (L : ℝ), (∀ (ε > 0), ∃ (N : ℕ), ∀ (n : ℕ), n >= N → sorry ∧ ∀ (p q : ℤ), p/q ≠ L) 


/- We cite the paper An Elementary Problem Equivalent to the Riemann Hypothesis by Jeffrey C. Lagarias
   available at https://arxiv.org/pdf/math/0008177.pdf which states that the following is
   equivalent to the Riemann Hypothesis -/

def H_n (n : ℕ) : ℝ :=
sum (multiset {r : ℝ | ∃ (m : ℕ), m ≤ n ∧ r=1/n})

theorem riemann_hypothesis : Prop := 
∀ (n : ℕ), (n ≥ 1 → sum (multiset {m : ℕ | ∃ (p : ℕ), n = m*p}) ≤ (H_n n) + exp(H_n n)*log(H_n n)) ∧ 
        (sum (multiset {m : ℕ | ∃ (p : ℕ), n = m*p}) = (H_n n) + exp(H_n n)*log(H_n n) ↔ n = 1)