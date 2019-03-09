import data.finset
import data.nat.choose
import tactic.squeeze

open nat
open finset

theorem binomial_expansion_for_2 (n : ℕ) : 
finset.sum (finset.range (n+1)) (λ (m : ℕ), choose n m) = 2^n :=
begin
    have h := add_pow 1 1 n,
    simp only [nat.one_pow, mul_one, one_mul, nat.cast_id, nat.pow_eq_pow] at h,
    simp only [h, eq_self_iff_true],
end