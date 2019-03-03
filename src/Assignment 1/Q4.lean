import data.finset

open nat
open finset

def nCk (n k : ℕ) : ℕ := (fact n)/((fact k) * (fact (n - k)))

-- theorem binomial_expansion (x y n : ℕ) : (x+y)^n = sum (multiset {(nCk n k) * x^k * y^(n-k) | k : ℕ, k <= n})
