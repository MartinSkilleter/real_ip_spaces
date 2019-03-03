import data.finset
import data.nat.prime

open nat
open finset

-- n is the length of the arithmetic sequence we want, a is the starting number
-- and k is the common difference
theorem green_tao : Prop :=
∀ (n : ℕ), ∃ (a k : ℕ), ∀ (i < n), prime (a + i * k)

-- The nth partial sum of a series Σf
def P_n (f : ℝ → ℝ) (n : ℕ) : ℕ :=
sum (multiset {1/(m : ℕ)^3 | m <= n})

theorem apery's_conjecture : Prop :=
∀ (p q : ℤ), p/q ≠ sorry



/- We cite the paper An Elementary Problem Equivalent to the Riemann Hypothesis by Jeffrey C. Lagarias
   available at https://arxiv.org/pdf/math/0008177.pdf which states that the following is
   equivalent to the Riemann Hypothesis -/
