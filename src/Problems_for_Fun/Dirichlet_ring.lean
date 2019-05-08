import data.complex.basic
import data.nat.totient

open nat
open complex

local notation `φ` := totient

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

instance : has_neg 𝔸 := ⟨λ f, arithmetic.mk (λ n, - f.f n)⟩

theorem arithmetic_add_left_neg (f : 𝔸) : -f + f = 0 :=
begin
    apply ext',
    intros n,
    dsimp [(+), has_neg.neg],
    have w₁ : distrib.add (add_group.neg ((f.f n).re)) ((f.f n).re) = ((0 : 𝔸).f n).re := begin
        have k₁ := sub_self (f.f n).re,
        have k₂ : distrib.add (add_group.neg ((f.f n).re)) ((f.f n).re) = -((f.f n).re) + ((f.f n).re) := by refl,
        have k₃ : (f.f n).re - (f.f n).re = (f.f n).re + -(f.f n).re := by refl,
        have k₄ : ((0 : 𝔸).f n).re = 0 := by refl,
        rw [add_comm, ←k₃, k₁, ←k₄] at k₂,
        exact k₂,
    end,
    have w₂ : distrib.add (add_group.neg ((f.f n).im)) ((f.f n).im) = ((0 : 𝔸).f n).im := begin
        have k₁ := sub_self (f.f n).im,
        have k₂ : distrib.add (add_group.neg ((f.f n).im)) ((f.f n).im) = -((f.f n).im) + ((f.f n).im) := by refl,
        have k₃ : (f.f n).im - (f.f n).im = (f.f n).im + -(f.f n).im := by refl,
        have k₄ : ((0 : 𝔸).f n).im = 0 := by refl,
        rw [add_comm, ←k₃, k₁, ←k₄] at k₂,
        exact k₂,
    end,
    rw [w₁, w₂],
    refl,
end

instance : add_comm_group 𝔸 :=
{neg := (has_neg.neg), add_left_neg := arithmetic_add_left_neg, .. (by apply_instance : add_comm_monoid 𝔸)}

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

theorem arithmetic_mul_one (f : 𝔸) : f * 1 = f :=
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
    
    sorry,
    
end

lemma mul_comm_case_zero (f g : 𝔸) : (f*g).f 0 = (g*f).f 0 :=
begin
    dsimp [(*)],
    simp,
    split,

    have k₁ : no_zero_divisors.mul ((f.f 0).re) ((g.f 0).re) = no_zero_divisors.mul ((g.f 0).re) ((f.f 0).re) := by exact mul_comm _ _,
    have k₂ : no_zero_divisors.mul ((f.f 0).im) ((g.f 0).im) = no_zero_divisors.mul ((g.f 0).im) ((f.f 0).im) := by exact mul_comm _ _,
    rw [k₁, k₂],

    rw [add_comm],
    have k₁ : no_zero_divisors.mul ((f.f 0).re) ((g.f 0).im) = no_zero_divisors.mul ((g.f 0).im) ((f.f 0).re) := by exact mul_comm _ _,
    have k₂ : no_zero_divisors.mul ((f.f 0).im) ((g.f 0).re) = no_zero_divisors.mul ((g.f 0).re) ((f.f 0).im) := by exact mul_comm _ _,
    rw [k₁, k₂],
end

lemma mul_comm_case_one (f g : 𝔸) : (f*g).f 1 = (g*f).f 1 :=
begin
    dsimp [(*)],
    have w : 1 ≤ 1 := by linarith,
    simp [w],
    split,

    have k₁ : no_zero_divisors.mul ((f.f 1).re) ((g.f 1).re) = no_zero_divisors.mul ((g.f 1).re) ((f.f 1).re) := by exact mul_comm _ _,
    have k₂ : no_zero_divisors.mul ((f.f 1).im) ((g.f 1).im) = no_zero_divisors.mul ((g.f 1).im) ((f.f 1).im) := by exact mul_comm _ _,
    rw [k₁, k₂],

    rw [add_comm],
    have k₁ : no_zero_divisors.mul ((f.f 1).re) ((g.f 1).im) = no_zero_divisors.mul ((g.f 1).im) ((f.f 1).re) := by exact mul_comm _ _,
    have k₂ : no_zero_divisors.mul ((f.f 1).im) ((g.f 1).re) = no_zero_divisors.mul ((g.f 1).re) ((f.f 1).im) := by exact mul_comm _ _,
    rw [k₁, k₂],
end

theorem arithmetic_mul_comm (f g : 𝔸) : f*g = g*f :=
begin
    apply ext',
    intros n,
    cases n,

    exact mul_comm_case_zero f g,

    cases n,

    exact mul_comm_case_one f g,

    sorry,
end

theorem arithmetic_one_mul (f : 𝔸) : 1 * f = f :=
begin
    rw [arithmetic_mul_comm],
    exact arithmetic_mul_one f,
end

lemma mul_assoc_case_zero (f g h : 𝔸) : ((f*g)*h).f 0 = (f*(g*h)).f 0 :=
begin
    dsimp [(*)],
    simp,
    split,

    
    sorry,
    sorry,
end

lemma mul_assoc_case_one (f g h : 𝔸) : ((f*g)*h).f 1 = (f*(g*h)).f 1 :=
begin
    sorry,
end

theorem arithmetic_mul_assoc (f g h : 𝔸) : (f * g) * h = f * (g * h) :=
begin
    apply ext',
    intros n,
    cases n,

    exact mul_assoc_case_zero f g h,

    cases n,

    exact mul_assoc_case_one f g h,
    
    sorry,
end

theorem arithmetic_left_distrib (f g h : 𝔸) : f * (g + h) = f * g + f * h :=
begin
    apply ext',
    intros n,

    sorry,
end

theorem arithmetic_right_distrib (f g h : 𝔸) : (f + g) * h = f * h + g * h :=
begin
    rw [arithmetic_mul_comm, arithmetic_left_distrib],
    repeat {rw [arithmetic_mul_comm h]},
end

instance : comm_ring 𝔸 :=
{mul := (*), mul_one := arithmetic_mul_one, mul_assoc := arithmetic_mul_assoc, 
 one := 1, one_mul := arithmetic_one_mul, left_distrib := arithmetic_left_distrib, 
 right_distrib := arithmetic_right_distrib, mul_comm := arithmetic_mul_comm,
 .. (by apply_instance : add_comm_group 𝔸)}

def mult (f : 𝔸) := f.f 0 = 0 ∧ f.f 1 = 1 ∧ (∀ (a b : ℕ), gcd a b = 1 → f.f (a*b) = f.f a * f.f b)

@[simp] lemma val_of_zero_one (f : 𝔸) (h : mult f) : f.f 0 = 0 :=
begin
    dsimp [mult] at h,
    cases h,
    exact h_left,
end

@[simp] lemma val_if_one_one (f : 𝔸) (h : mult f) : f.f 1 = 1 :=
begin
    dsimp [mult] at h,
    cases h,
    cases h_right,
    exact h_right_left,
end

def Φ : 𝔸 := arithmetic.mk (λ n, of_real ( φ n : ℝ))

theorem Φ_mult : mult Φ :=
begin
    dsimp [mult],
    repeat {split},

    dsimp[Φ],
    have h : φ 1 = 1 := rfl,
    rw h,
    simp,

    intros a b h,
    dsimp [Φ],
    simp,
    sorry,
    
end




