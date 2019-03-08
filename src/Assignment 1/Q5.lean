def is_prime (p : ℕ) : Prop := p ≥ 2 ∧ ∀ (a b : ℕ), a*b = p → a = 1 ∨ b = 1

