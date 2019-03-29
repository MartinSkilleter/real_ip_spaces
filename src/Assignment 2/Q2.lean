-- We write quaternions in the form a + bi + cj + dk, where a,b,c,d ∈ ℝ
-- That is, we are modelling ℍ as ℝ^4
import data.real.basic tactic.ring algebra.field_power
import ring_theory.algebra
import algebra.pi_instances
import tactic.basic

structure quaternion : Type :=
(re : ℝ) (i : ℝ) (j : ℝ) (k : ℝ)

notation `ℍ` := quaternion

noncomputable theory

namespace quaternion

@[simp] theorem eta : ∀ q : ℍ, quaternion.mk q.re q.i q.j q.k = q :=
begin
    intros q,
    cases q,
    refl,
end

theorem ext : ∀ {p q : ℍ}, p.re = q.re → p.i = q.i → p.j = q.j → p.k = q.k → p = q
| ⟨pre, pi, pj, pk⟩ ⟨_, _, _, _⟩ rfl rfl rfl rfl := rfl
 
@[extensionality] theorem ext_iff : ∀ {p q : ℍ}, p = q ↔ p.re = q.re ∧ p.i = q.i ∧ p.j = q.j ∧ p.k = q.k :=
begin
    intros p q,
    split,
    {intros h,
     have h_re : p.re = q.re, by rw h,
     have h_i : p.i = q.i, by rw h,
     have h_j : p.j = q.j, by rw h,
     have h_k : p.k = q.k, by rw h,
     split,
     exact h_re,
     split,
     exact h_i,
     split,
     exact h_j,
     exact h_k,
    },
    {rintro ⟨h₁, ⟨h₂, ⟨h₃, h₄⟩⟩⟩,
     exact ext h₁ h₂ h₃ h₄,
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
⟨congr_arg re, congr_arg _⟩

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

-- Question 2d)
def conj : ℍ → ℍ := λ p, ⟨p.re, -p.i, -p.j, -p.k⟩

@[simp] lemma conj_re (p : ℍ) : (conj p).re = p.re := rfl
@[simp] lemma conj_i (p : ℍ) : (conj p).i = -p.i := rfl
@[simp] lemma conj_j (p : ℍ) : (conj p).j = -p.j := rfl
@[simp] lemma conj_k (p : ℍ) : (conj p).k = -p.k := rfl

@[simp] lemma conj_of_real (r : ℝ) : conj r = r := by simp [ext_iff]

@[simp] lemma conj_zero : conj 0 = 0 := by simp [ext_iff]
@[simp] lemma conj_one : conj 1 = 1 := by simp [ext_iff]
@[simp] lemma conj_I : conj I = -I := by simp [ext_iff]
@[simp] lemma conj_J : conj J = -J := by simp [ext_iff]
@[simp] lemma conj_K : conj K = -K := by simp [ext_iff]

@[simp] lemma conj_add (p q : ℍ) : conj (p + q) = conj p + conj q := by simp [ext_iff]

@[simp] lemma conj_neg (p : ℍ) : conj (-p) = -conj p := rfl

@[simp] lemma conj_mul (p q : ℍ) : conj (p * q) = conj q * conj p := by simp [ext_iff, mul_comm, add_comm]

@[simp] lemma conj_conj (p : ℍ) : conj (conj p) = p := by simp [ext_iff]

lemma conj_bijective : function.bijective conj :=
⟨function.injective_of_has_left_inverse ⟨conj, conj_conj⟩,
function.surjective_of_has_right_inverse ⟨conj, conj_conj⟩⟩ 

lemma conj_inj {p q : ℍ} : conj p = conj q ↔ p = q := conj_bijective.1.eq_iff

@[simp] lemma conj_eq_zero {p : ℍ} : conj p = 0 ↔ p = 0 :=
begin
    split,
    intros h,
    have w : conj 0 = 0, exact conj_zero,
    rw ←w at h,
    apply conj_inj.1 h,
    intros h,
    have w : conj p = conj 0, by apply conj_inj.2 h,
    rw conj_zero at w,
    exact w,
end

@[simp] lemma eq_conj_iff_real (p : ℍ) : conj p = p ↔ ∃ (r : ℝ), p = r :=
begin
    split,
    intros h,
    simp [ext_iff],
    simp [ext_iff] at h,
    cases h with h₁ h₂,
    cases h₂ with h₂ h₃,
    split,

    apply eq_zero_of_neg_eq,
    exact h₁,

    split,
    apply eq_zero_of_neg_eq,
    exact h₂,

    apply eq_zero_of_neg_eq,
    exact h₃,

    intros h,
    simp [ext_iff] at h,
    cases h with h₁ h₂,
    cases h₂ with h₂ h₃,
    simp [ext_iff],
    sorry,


end

-- Question 2b)
def quaternion_ring : ring ℍ :=
by refine { add := (+),
           mul := (*),
           neg := has_neg.neg,
           zero := 0,
           one := 1,
           .. };
  {intros, apply ext_iff.2; repeat {split; simp; ring}}

def norm_sq (p : ℍ) : ℝ := p.re * p.re + p.i * p.i + p.j * p.j + p.k * p.k
def norm_conj (p : ℍ) : ℝ := (conj p * p).re

theorem norm_sq_is_norm_conj : ∀ (p : ℍ), norm_sq p = norm_conj p :=
begin
    intro,
    dsimp [norm_sq, norm_conj],
    ring,
end

@[simp] lemma norm_sq_of_real (r : ℝ) : norm_sq r = r * r :=
by simp [norm_sq]

@[simp] lemma norm_sq_zero : norm_sq 0 = 0 := by simp [norm_sq]
@[simp] lemma norm_sq_one : norm_sq 1 = 1 := by simp [norm_sq]
@[simp] lemma norm_sq_I : norm_sq I = 1 := by simp [norm_sq]
@[simp] lemma norm_sq_J : norm_sq J = 1 := by simp [norm_sq]
@[simp] lemma norm_sq_K : norm_sq K = 1 := by simp [norm_sq]

lemma norm_sq_nonneg (p : ℍ) : 0 ≤ norm_sq p :=
add_nonneg (add_nonneg (add_nonneg (mul_self_nonneg _) (mul_self_nonneg _)) (mul_self_nonneg _)) (mul_self_nonneg _)

@[simp] lemma norm_sq_eq_zero {p : ℍ} : norm_sq p = 0 ↔ p = 0 :=
begin
    split,
    intros h,
    simp [norm_sq] at h,
    sorry,

    intros p,
    have h : norm_sq 0 = 0, by exact norm_sq_zero,
    rw ←p at h,
    exact h,
end

@[simp] lemma norm_sq_pos {p : ℍ} : 0 < norm_sq p ↔ p ≠ 0 :=
begin
    split,
    intros h,
    sorry,
    sorry
end

@[simp] lemma norm_sq_neg (p : ℍ) : norm_sq (-p) = norm_sq p := by simp [norm_sq]

@[simp] lemma norm_sq_conj (p : ℍ) : norm_sq (conj p) = norm_sq p := by simp [norm_sq]

@[simp] lemma norm_sq_mul (p q : ℍ) : norm_sq (p * q) = norm_sq p * norm_sq q :=
by dsimp [norm_sq]; ring

-- Question 2e)
theorem conj_prod_re : ∀ (p : ℍ), ∃ (r : ℝ), (r : ℍ) = (conj p) * p :=
begin
    intros p,
    use p.re^2+p.i^2+p.j^2+p.k^2,
    simp only [ext_iff],
    repeat {try {split}, simp, ring},
end

def id_coerc : ℝ → ℍ := λ r, ⟨r, 0, 0, 0⟩

section ring_section

local attribute [instance] quaternion_ring

instance id_is_ring_hom : is_ring_hom id_coerc :=
begin
    split,
    refl,
    repeat {intros x y,
    simp only [ext_iff],
    repeat {try {split}, dsimp [id_coerc], ring}},
end

theorem id_commutes : ∀ (r : ℝ) (p : ℍ), p * id_coerc r = id_coerc r * p :=
begin
    intros r p,
    simp only [ext_iff],
    repeat {try {split}, dsimp [id_coerc], ring},
end

def smul : ℝ → ℍ → ℍ := λ r p, id r * p

infix `•` := smul

end ring_section

lemma add_inv : ∀ (a : ℍ), -a + a = 0 :=
begin
    simp only [ext_iff,
 quaternion.neg_re,
 quaternion.add_i,
 forall_const,
 quaternion.zero_i,
 quaternion.zero_j,
 quaternion.zero_re,
 quaternion.neg_i,
 eq_self_iff_true,
 add_left_neg,
 quaternion.zero_k,
 and_self,
 quaternion.neg_j,
 quaternion.add_k,
 quaternion.add_j,
 quaternion.add_re,
 quaternion.neg_k],
end

lemma zero_add : ∀ (a : ℍ), 0 + a = a :=
begin
    simp only [ext_iff,
 quaternion.add_i,
 forall_const,
 quaternion.zero_i,
 quaternion.zero_j,
 quaternion.zero_re,
 eq_self_iff_true,
 zero_add,
 quaternion.zero_k,
 and_self,
 quaternion.add_k,
 quaternion.add_j,
 quaternion.add_re],
end

lemma add_comm : ∀ (a b : ℍ), a + b = b + a :=
begin
    simp only [ext_iff,
 quaternion.add_i,
 forall_const,
 add_comm,
 eq_self_iff_true,
 and_self,
 quaternion.add_k,
 add_right_inj,
 quaternion.add_j,
 quaternion.add_re],
end

lemma add_assoc : ∀ (a b c : ℍ), a + b + c = a + (b + c) :=
begin
    simp [ext_iff],
end

-- Why is this necessary? Surely zero_add and add_comm give this already?
lemma add_zero : ∀ (a : ℍ), a + 0 = a :=
begin
    simp only [ext_iff,
 quaternion.add_i,
 add_zero,
 forall_const,
 quaternion.zero_i,
 quaternion.zero_j,
 quaternion.zero_re,
 eq_self_iff_true,
 quaternion.zero_k,
 and_self,
 quaternion.add_k,
 quaternion.add_j,
 quaternion.add_re],
end

instance quaternion_add_comm_group : @add_comm_group ℍ :=
begin
    split,
    exact add_inv,
    exact add_comm,
    exact add_assoc,
    exact zero_add,
    exact add_zero,
end

instance : semimodule ℝ ℍ :=
begin
    sorry,
end


-- Question 2c)
instance quaternion_algebra : @algebra ℝ ℍ _ (quaternion_ring) := 
sorry

instance : has_inv ℍ := ⟨λ p, (1/norm_sq p) • conj p⟩
def inv (p : ℍ) : ℍ := (1/(norm_sq p)) • conj p

theorem left_inv_mul : ∀ (p : ℍ), p ≠ 0 → inv p * p = 1 :=
begin
    sorry,
end

theorem right_inv_mul : ∀ (p : ℍ), p ≠ 0 → p * inv p = 1 :=
begin
    intros p h,
    simp [ext_iff],
    split,
    dsimp [inv, norm_sq, (•)],
    ring,
    repeat {rw ←real.comm_ring.left_distrib},
    sorry,
    repeat {try {split}, dsimp [inv, norm_sq, (•)], ring},
end

instance : division_ring ℍ :=
begin
    split,
    intros p,
    exact right_inv_mul p,
    intros p,
    exact left_inv_mul p,

    repeat {sorry},
end


end quaternion
