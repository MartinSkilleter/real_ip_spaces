import data.finset
import data.real.basic
import data.real.cau_seq_completion
import data.nat.gcd

noncomputable theory

open nat
open finset
open int

example : decidable_linear_ordered_comm_group ℝ := by apply_instance

def f (x : ℝ ) : ℝ := abs x

-- n is the length of the arithmetic sequence we want, a is the starting number
-- and k is the common difference
theorem green_tao : Prop :=
∀ (n : ℕ), ∃ (a k : ℕ), ∀ (i < n), k ≠ 0 ∧ prime (a + i * k)

-- The nth partial sum of a series Σf
def P_n (f : ℕ → ℝ) (n : ℕ) : ℝ :=
finset.sum (finset.Ico 1 (n+1)) f

-- The series with f inside the sum
def converges (f : ℕ → ℝ) (L : ℝ) : Prop :=
∀ (ε > 0), ∃ (N : ℕ), ∀ (n : ℕ), n ≥ N → abs (P_n f n - L) < ε

theorem apery's_theorem : Prop :=
∃ (L : ℝ), converges (λ n, 1/(n^3)) L ∧ ∀ (p q : ℤ), (p/q : ℝ) ≠ L 


def find_prime_factors (n: ℕ) : list ℕ :=
((list.range (n+1)).filter prime).filter (∣ n)

def rad (n : ℕ) : ℕ := 
(find_prime_factors n).prod

-- We use formulation 2 of the abc conjecture from https://en.wikipedia.org/wiki/Abc_conjecture
def abc_conjecture : Prop :=
∀ (n : ℕ), ∃ (K : ℝ), ∀ (a b c : ℕ), 
n > 0 ∧ nat.gcd a b = 1 ∧ nat.gcd a c = 1 ∧ nat.gcd b c = 1 ∧ a + b = c → (c : ℝ) < K*(rad a*b*c : ℝ)^(1+1/n)
