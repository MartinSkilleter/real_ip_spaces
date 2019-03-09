import data.finset
import data.real.basic
import data.nat.gcd
import tactic.linarith

open nat
open finset
open int

-- n is the length of the arithmetic sequence we want, a is the starting number
-- and k is the common difference
theorem green_tao : Prop :=
∀ (n : ℕ), ∃ (a k : ℕ), ∀ (i < n), prime (a + i * k)

-- The nth partial sum of a series Σf
def P_n (f : ℕ → ℝ) (n : ℕ) : ℝ :=
finset.sum (finset.Ico 1 (n+1)) f

-- The series with f inside the sum
def converges (f : ℕ → ℝ) (L : ℝ) : Prop :=
∀ (ε > 0), ∃ (N : ℕ), ∀ (n : ℕ), n ≥ N → (P_n f n - L) < ε ∧ (L - P_n f n) < ε

theorem apery's_theorem : Prop :=
∃ (L : ℝ), converges (λ n, 1/(n^3)) L ∧ ∀ (p q : ℤ), (p/q : ℝ) ≠ L 

def find_prime_factors (n: ℕ) : list ℕ :=
((list.range (n+1)).filter prime).filter (∣ n)

def rad (n : ℕ) : ℕ := 
(find_prime_factors n).prod

-- We use formulation 2 of the abc conjecture from https://en.wikipedia.org/wiki/Abc_conjecture
def abc_conjecture : Prop :=
∀ (n : ℕ), ∃ (K : ℝ), ∀ (a b c : ℕ), 
n > 0 ∧ nat.gcd a b = 1 ∧ nat.gcd a c = 1 ∧ nat.gcd b c = 1 ∧ a + b = c → (c : ℝ) < K*(rad a*b*c)^(1+1/n)

/- We cite the paper An Elementary Problem Equivalent to the Riemann Hypothesis by Jeffrey C. Lagarias
   available at https://arxiv.org/pdf/math/0008177.pdf which states that the following is
   equivalent to the Riemann Hypothesis -/

def H_n (n : ℕ) : ℝ :=
P_n (λ n, 1/n : ℕ → ℝ) n

theorem riemann_hypothesis : Prop := 
∀ (n : ℕ), (n ≥ 1 → sum (multiset {m : ℕ | ∃ (p : ℕ), n = m*p}) ≤ (H_n n) + exp(H_n n)*log(H_n n)) ∧ 
        (sum (multiset {m : ℕ | ∃ (p : ℕ), n = m*p}) = (H_n n) + exp(H_n n)*log(H_n n) ↔ n = 1)