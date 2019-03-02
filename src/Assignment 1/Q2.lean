import data.finset
import data.nat.prime

-- n is the length of the arithmetic sequence we want, a is the starting number
-- and k is the common difference
theorem green_tao : Prop :=
∀ (n : ℕ), ∃ (a k : ℕ), ∀ (i < n) prime (a + i * k)

/- We cite the paper An Elementary Problem Equivalent to the Riemann Hypothesis by Jeffrey C. Lagarias
   available at https://arxiv.org/pdf/math/0008177.pdf which states that the following is
   equivalent to the Riemann Hypothesis -/

-- We begin by defining the n^th harmonic number H_n
