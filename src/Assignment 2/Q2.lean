-- We write quaternions in the form a + bi + cj + dk, where a,b,c,d ∈ ℝ
-- That is, we are modelling ℍ as ℝ^4
import data.real.basic tactic.ring algebra.field_power

structure quaternion : Type :=
(re : ℝ) (i : ℝ) (j : ℝ) (k : ℝ)

notation `ℍ` := quaternion

namespace quaternion

@[simp] theorem eta : ∀ q : ℍ, quaternion.mk q.re q.i q.j q.k = q :=
begin
    intros q,
    cases q,
    refl,
end

theorem ext : ∀ {p q : ℍ}, p.re = q.re → p.i = q.i → p.j = q.j → p.k = q.k → p = q
| ⟨pre, pi, pj, pk⟩ ⟨_, _, _, _⟩ rfl rfl rfl rfl := rfl
 
theorem ext_iff : ∀ {p q : ℍ}, p = q ↔ p.re = q.re ∧ p.i = q.i ∧ p.j = q.j ∧ p.k = q.k :=
begin
    intros p q,
    split,
    {sorry,
    },
    {intros h,
     apply and.rec ext,
     cases h with h₁ h₂,
     cases h₂ with h₂ h₃,
     apply and.intro h₁ h₂,
     cases h with h₁ h₂,
     cases h₂ with h₂ h₃,
     cases h₃ with h₃ h₄,
     exact h₃,
     cases h with h₁ h₂,
     cases h₂ with h₂ h₃,
     cases h₃ with h₃ h₄,
     exact h₄,
    }
end

def of_real (r : ℝ) : ℍ := ⟨r, 0, 0, 0⟩
instance : has_coe ℝ ℍ := ⟨of_real⟩

@[simp] lemma of_real_eq_coe (r : ℝ) : of_real r = r := rfl
@[simp] lemma of_real_re (r : ℝ) : (r : ℍ).re = r := rfl
@[simp] lemma of_real_i (r : ℝ) : (r : ℍ).i = 0 := rfl
@[simp] lemma of_real_j (r : ℝ) : (r : ℍ).j = 0 := rfl
@[simp] lemma of_real_k (r : ℝ) : (r : ℍ).k = 0 := rfl

@[simp] theorem of_real_inj {z w : ℝ} : (z : ℍ) = w ↔ z = w :=
begin
    split,
    intros h,
    sorry,
    intros h,
    sorry
end

instance : has_zero ℍ := ⟨(0 : ℝ)⟩
instance : inhabited ℍ := ⟨0⟩

@[simp] lemma zero_re : (0 : ℍ).re = 0 := rfl
@[simp] lemma zero_i : (0 : ℍ).i = 0 := rfl
@[simp] lemma zero_j : (0 : ℍ).j = 0 := rfl
@[simp] lemma zero_k : (0 : ℍ).k = 0 := rfl

@[simp] theorem of_real_eq_zero {p : ℝ} : (p : ℍ) = 0 ↔ p = 0 := of_real_inj
@[simp] theorem of_real_ne_zero {p : ℝ} : (p : ℍ) ≠ 0 ↔ p ≠ 0 := not_congr of_real_eq_zero

instance : has_one ℍ := ⟨(1 : ℝ)⟩

@[simp] lemma one_re : (1 : ℍ).re = 1 := rfl
@[simp] lemma one_i : (1 : ℍ).i = 0 := rfl
@[simp] lemma one_j : (1 : ℍ).j = 0 := rfl
@[simp] lemma one_k : (1 : ℍ).k = 0 := rfl
@[simp] lemma of_real_one : ((1 : ℝ) : ℍ) = 1 := rfl

def I : ℍ := ⟨0, 1, 0, 0⟩
def J : ℍ := ⟨0, 0, 1, 0⟩
def K : ℍ := ⟨0, 0, 0, 1⟩

@[simp] lemma I_re : I.re = 0 := rfl
@[simp] lemma I_i : I.i = 1 := rfl
@[simp] lemma I_j : I.j = 0 := rfl
@[simp] lemma I_k : I.k = 0 := rfl

@[simp] lemma J_re : J.re = 0 := rfl
@[simp] lemma J_i : J.i = 0 := rfl
@[simp] lemma J_j : J.j = 1 := rfl
@[simp] lemma J_k : J.k = 0 := rfl

@[simp] lemma K_re : K.re = 0 := rfl
@[simp] lemma K_i : K.i = 0 := rfl
@[simp] lemma K_j : K.j = 0 := rfl
@[simp] lemma K_k : K.k = 1 := rfl

instance : has_add ℍ := ⟨λ p q, ⟨p.re + q.re, p.i + q.i, p.j + q.j, p.k + q.k⟩⟩

@[simp] lemma add_re (p q : ℍ) : (p + q).re = p.re + q.re := rfl
@[simp] lemma add_i (p q : ℍ) : (p + q).i = p.i + q.i := rfl
@[simp] lemma add_j (p q : ℍ) : (p + q).j = p.j + q.j := rfl
@[simp] lemma add_k (p q : ℍ) : (p + q).k = p.k + q.k := rfl
@[simp] lemma of_real_add (r s : ℝ) : ((r + s : ℝ) : ℍ) = r + s := by simp [ext_iff]

instance : has_neg ℍ := ⟨λ p, ⟨-p.re, -p.i, -p.j, -p.k⟩⟩

@[simp] lemma neg_re (p : ℍ) : (-p).re = -p.re := rfl
@[simp] lemma neg_i (p : ℍ) : (-p).i = -p.i := rfl
@[simp] lemma neg_j (p : ℍ) : (-p).j = -p.j := rfl
@[simp] lemma neg_k (p : ℍ) : (-p).k = -p.k := rfl
@[simp] lemma of_real_neg (r : ℝ) : ((-r : ℝ) : ℍ) = -r := by simp [ext_iff]

instance : has_mul ℍ := ⟨λ p q, ⟨p.re*q.re - p.i*q.i - p.j*q.j - p.k*q.k,
                                 p.re*q.i + p.i*q.re + p.j*q.k - p.k*q.j,
                                 p.re*q.j - p.i*q.k + p.j*q.re + p.k*q.i,
                                 p.re*q.k + p.i*q.j - p.j*q.i + p.k*q.re⟩⟩

@[simp] lemma mul_re (p q : ℍ) : (p*q).re = p.re*q.re - p.i*q.i - p.j*q.j - p.k*q.k := rfl
@[simp] lemma mul_i (p q : ℍ) : (p*q).i = p.re*q.i + p.i*q.re + p.j*q.k - p.k*q.j := rfl
@[simp] lemma mul_j (p q : ℍ) : (p*q).j = p.re*q.j - p.i*q.k + p.j*q.re + p.k*q.i := rfl
@[simp] lemma mul_k (p q : ℍ) : (p*q).k = p.re*q.k + p.i*q.j - p.j*q.i + p.k*q.re := rfl

@[simp] lemma I_mul_I : I * I = -1 := by simp [ext_iff]
@[simp] lemma J_mul_J : J * J = -1 := by simp [ext_iff]
@[simp] lemma K_mul_K : K * K = -1 := by simp [ext_iff]

lemma I_ne_zero : (I : ℍ) ≠ 0 :=
begin
    assume h: I = 0, 
    have h₁ : (0 : ℍ) * 0 = 0, by simp [ext_iff],
    have h₂ : I * I = -1, by exact I_mul_I,
    rw h at h₂,
    rw h₁ at h₂,
    rw [ext_iff] at h₂,
    cases h₂ with h₂ h₃,
    simp [zero_re, one_re] at h₂,
    have h₃ : (0 : ℝ) ≠ -1, by norm_num,
    contradiction,
end

lemma J_ne_zero : (J : ℍ) ≠ 0 :=
begin
    assume h: J = 0, 
    have h₁ : (0 : ℍ) * 0 = 0, by simp [ext_iff],
    have h₂ : J * J = -1, by exact J_mul_J,
    rw h at h₂,
    rw h₁ at h₂,
    rw [ext_iff] at h₂,
    cases h₂ with h₂ h₃,
    simp [zero_re, one_re] at h₂,
    have h₃ : (0 : ℝ) ≠ -1, by norm_num,
    contradiction,
end

lemma K_ne_zero : (K : ℍ) ≠ 0 :=
begin
    assume h: K = 0, 
    have h₁ : (0 : ℍ) * 0 = 0, by simp [ext_iff],
    have h₂ : K * K = -1, by exact K_mul_K,
    rw h at h₂,
    rw h₁ at h₂,
    rw [ext_iff] at h₂,
    cases h₂ with h₂ h₃,
    simp [zero_re, one_re] at h₂,
    have h₃ : (0 : ℝ) ≠ -1, by norm_num,
    contradiction,
end

def conj (p : ℍ) : ℍ := ⟨p.re, -p.i, -p.j, -p.k⟩

theorem conj_prod_re : ∀ (p : ℍ), ∃ (r : ℝ), (r : ℍ) = (conj p) * p :=
begin
    intros p,
    use p.re^2+p.i^2+p.j^2+p.k^2,

    
    sorry
end

end quaternion
