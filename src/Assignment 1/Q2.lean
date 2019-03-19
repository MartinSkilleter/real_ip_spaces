import data.finset
import data.real.basic
import data.real.cau_seq_completion
import data.nat.gcd
import analysis.exponential

noncomputable theory

open nat
open finset
open int
open real
open complex

example : decidable_linear_ordered_comm_group ℝ := by apply_instance

-- n is the length of the arithmetic sequence we want, a is the starting number
-- and k is the common difference (k ≠ 0 or else we can choose a to be prime and we are done)
theorem green_tao : Prop :=
∀ (n : ℕ), ∃ (a k : ℕ), ∀ (i < n), k ≠ 0 ∧ prime (a + i * k)

-- The nth partial sum of a series Σf
def P_n (f : ℕ → ℝ) (n : ℕ) : ℝ :=
finset.sum (finset.Ico 1 (n+1)) f

-- The series with f inside the sum
def converges (f : ℕ → ℝ) (L : ℝ) : Prop :=
∀ (ε > 0), ∃ (N : ℕ), ∀ (n : ℕ), n ≥ N → complex.abs (P_n f n - L) < ε

-- Apery's Theorem says that the sum from n=1 to ∞ of 1/n^3 has a limit and that the limit is irrational
theorem apery's_theorem : Prop :=
∃ (L : ℝ), converges (λ n, 1/(n^3)) L ∧ ∀ (p q : ℤ), (p/q : ℝ) ≠ L 

def find_prime_factors (n: ℕ) : list ℕ :=
((list.range (n+1)).filter prime).filter (∣ n)

def rad (n : ℕ) : ℕ := 
(find_prime_factors n).prod

-- We use formulation 2 of the abc conjecture from https://en.wikipedia.org/wiki/Abc_conjecture
-- Note that because 1/n → 0 as n → ∞, this is equivalent to the ε formulation
def abc_conjecture : Prop :=
∀ (n : ℕ), ∃ (K : ℝ), ∀ (a b c : ℕ), 
n > 0 ∧ ∀ (z : ℕ), (z ∣ a ∧ z ∣ b ∧ z ∣ c → z = 1) ∧ a + b = c → (c : ℝ) < K*(rad a*b*c : ℝ)^(1+1/n)

section
local attribute [instance] classical.prop_decidable

theorem oops : ¬ abc_conjecture :=
begin
  dsimp [abc_conjecture],
  simp only [not_forall],
  use 0,
  rintro ⟨K, p⟩,
  replace p := p 0 0 0,
  cases p,
  cases p_left,
end
end

-- We cite the paper "An Elementary Problem Equivalent to the Riemann Hypothesis"
-- by Jeffrey Lagarias, which can be found at http://www.math.lsa.umich.edu/~lagarias/doc/elementaryrh.pdf

-- We begin by defining the harmonic series
def H_n (n : ℕ) : ℝ := P_n (λm, 1/m) n

def sum_of_divisors (n : ℕ) : ℝ :=
((list.range (n+1)).filter (∣ n)).sum

def riemann_hypothesis : Prop :=
∀ (n : ℕ), sum_of_divisors n ≤ H_n n + exp (H_n n)*log (H_n n) ∧
           sum_of_divisors n = H_n n + exp (H_n n)*log (H_n n) ↔ n = 1

section
local attribute [instance] classical.prop_decidable

example : ¬riemann_hypothesis :=
begin
  dsimp [riemann_hypothesis],
  simp only [not_forall],
  use 0,
  simp,
  dsimp [sum_of_divisors, H_n, list.range, list.range_core, P_n],
  simp,
end
end

-- what went wrong?
-- Let's redefine some things to avoid the real numbers, which we can't compute with.
def sum_of_divisors' (n : ℕ) : ℕ :=
((list.range (n+1)).filter (∣ n)).sum

def P_n' (f : ℕ → ℚ) (n : ℕ) : ℚ :=
finset.sum (finset.Ico 1 (n+1)) f
def H_n' (n : ℕ) : ℚ := P_n' (λm, 1/m) n

#eval sum_of_divisors' 0
#eval H_n' 0

-- So the problem is that we _also_ have equality at n = 0!