import data.complex.basic

open nat
open complex

structure arithmetic : Type :=
(f : ℕ → ℂ)

notation `𝔸` := arithmetic

@[simp] theorem eta : ∀ f : 𝔸, arithmetic.mk f.f = f
| ⟨a⟩ := rfl

@[extensionality] theorem ext : ∀ {f g : 𝔸}, f.f = g.f → f = g
| ⟨_⟩ ⟨_⟩ rfl := rfl

@[extensionality] theorem ext' : ∀ {f g : 𝔸}, (∀ (n : ℕ), f.f n = g.f n) → f = g :=
begin
    intros f g h,
    have w := funext h,
    simp at w,
    exact (ext w),
end

instance : has_zero 𝔸 := ⟨arithmetic.mk (λ n, 0)⟩
instance : inhabited 𝔸 := ⟨0⟩
instance : has_add 𝔸 := ⟨λ f g, arithmetic.mk (λ n, f.f n + g.f n)⟩ 

lemma zerof (n : ℕ) : ((0 : 𝔸).f n) = 0 := by refl
lemma zerof_re (n : ℕ) : ((0 : 𝔸).f n).re = 0 := by {rw [zerof], refl}
lemma zerof_im (n : ℕ) : ((0 : 𝔸).f n).im = 0 := by {rw [zerof], refl}

theorem arithmetic_add_zero (f : 𝔸) : f + 0 = f :=
begin
    apply ext',
    intros n,
    dsimp [(+), 0],
    rw [zerof_re, zerof_im],
    have w_re : distrib.add (f.f n).re 0 = (f.f n).re := by exact add_zero _,
    have w_im : distrib.add (f.f n).im 0 = (f.f n).im := by exact add_zero _,
    rw [w_re, w_im],
    simp only [complex.eta],
end

theorem arithmetic_add_comm (f g : 𝔸) : f + g = g + f :=
begin
    apply ext',
    intros n,
    dsimp [(+)],
    have w₁ : distrib.add (f.f n).re (g.f n).re = distrib.add (g.f n).re (f.f n).re := by exact add_comm _ _,
    have w₂ : distrib.add (f.f n).im (g.f n).im = distrib.add (g.f n).im (f.f n).im := by exact add_comm _ _,
    rw [w₁, w₂],
end

theorem arithmetic_zero_add (f : 𝔸) : 0 + f = f :=
begin
    rw [arithmetic_add_comm],
    exact arithmetic_add_zero f,
end

theorem arithmetic_add_assoc (f g h : 𝔸) : (f + g) + h = f + (g + h) :=
begin
    apply ext',
    intros n,
    dsimp [(+)],
    have w₁ : distrib.add (distrib.add ((f.f n).re) ((g.f n).re)) ((h.f n).re) = distrib.add ((f.f n).re) (distrib.add ((g.f n).re) ((h.f n).re)) := by exact add_assoc _ _ _,
    have w₂ : distrib.add (distrib.add ((f.f n).im) ((g.f n).im)) ((h.f n).im) = distrib.add ((f.f n).im) (distrib.add ((g.f n).im) ((h.f n).im)) := by exact add_assoc _ _ _,
    rw [w₁, w₂],
end

instance : add_comm_monoid 𝔸 :=
{add := (+), add_assoc := arithmetic_add_assoc, zero := 0, zero_add := arithmetic_zero_add, add_zero := arithmetic_add_zero, add_comm := arithmetic_add_comm}

instance : has_one 𝔸 := ⟨arithmetic.mk (λ n, if n ≤ 1 then 1 else 0)⟩
instance : has_mul 𝔸 := ⟨λ f g, arithmetic.mk (λ n, if n ≤ 1 then (f.f n) * (g.f n) else list.sum (list.map (λ d, f.f d * g.f (n / d)) (factors n)))⟩

lemma mul_one_case_zero (f : 𝔸) : (f * 1).f 0 = f.f 0 :=
begin
    dsimp [(*)],
    simp,
    have w₁ : ((1 : 𝔸).f 0).re = 1 := by refl,
    have w₂ : ((1 : 𝔸).f 0).im = 0 := by refl,
    have w₃ : no_zero_divisors.mul ((f.f 0).re) 1 = (f.f 0).re := by exact mul_one _,
    have w₄ : (no_zero_divisors.mul ((f.f 0).im)) 0 = 0 := by exact mul_zero _,
    have w₅ : no_zero_divisors.mul ((f.f 0).im) 1 = (f.f 0).im := by exact mul_one _,
    have w₆ : (no_zero_divisors.mul ((f.f 0).re)) 0 = 0 := by exact mul_zero _,
    rw [w₁, w₂, w₃, w₄, w₅, w₆],
    simp,
end

lemma mul_one_case_one (f : 𝔸) : (f * 1).f 1 = f.f 1 :=
begin
    dsimp [(*)],
    have w : 1 ≤ 1 := by linarith,
    simp [w],
    have w₁ : ((1 : 𝔸).f 1).re = 1 := by refl,
    have w₂ : ((1 : 𝔸).f 1).im = 0 := by refl,
    have w₃ : no_zero_divisors.mul ((f.f 1).re) 1 = (f.f 1).re := by exact mul_one _,
    have w₄ : (no_zero_divisors.mul ((f.f 1).im)) 0 = 0 := by exact mul_zero _,
    have w₅ : no_zero_divisors.mul ((f.f 1).im) 1 = (f.f 1).im := by exact mul_one _,
    have w₆ : (no_zero_divisors.mul ((f.f 1).re)) 0 = 0 := by exact mul_zero _,
    rw [w₁, w₂, w₃, w₄, w₅, w₆],
    simp,
end
.

theorem mul_one (f : 𝔸) : f * 1 = f :=
begin
    apply ext',
    intros n,
    cases n,
    
    exact mul_one_case_zero f,

    cases n,

    exact mul_one_case_one f,
    
    dsimp [(*)],
    have w : n + 2 > 1 := by linarith,
    dsimp [(>)] at w,
    rw [lt_iff_not_ge] at w,
    dsimp [(≥)] at w,
    simp [w],
    
end









