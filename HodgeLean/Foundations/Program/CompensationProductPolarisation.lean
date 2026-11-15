import HodgeLean.Foundations.Program.CompensationProductLinear
import HodgeLean.Blocks.HodgeStructure.Polarisation
import HodgeLean.Blocks.HodgeStructure.ExteriorPower

/-! # Polarizations from complementary rational projections -/

noncomputable section
set_option maxHeartbeats 400000
open scoped TensorProduct
open HodgeBlocks

namespace HodgeLean.Foundations.Program

variable {U V Z : Type*} [AddCommGroup U] [Module ℚ U]
  [AddCommGroup V] [Module ℚ V] [AddCommGroup Z] [Module ℚ Z]

/-- Complexification commutes with the sum of two pulled-back bilinear forms.
Source: Mathlib `LinearMap.BilinForm.baseChange_tmul`. -/
theorem cp_baseChange_sumPull (B : LinearMap.BilinForm ℚ U) (C : LinearMap.BilinForm ℚ V)
    (p : Z →ₗ[ℚ] U) (q : Z →ₗ[ℚ] V) (x y : ℂ ⊗[ℚ] Z) :
    LinearMap.BilinForm.baseChange ℂ (B.compl₁₂ p p + C.compl₁₂ q q) x y =
      B.baseChange ℂ (p.baseChange ℂ x) (p.baseChange ℂ y) +
        C.baseChange ℂ (q.baseChange ℂ x) (q.baseChange ℂ y) := by
  induction x using TensorProduct.inductionOn with
  | tmul a x =>
    induction y using TensorProduct.inductionOn with
    | tmul b y =>
      simp only [LinearMap.baseChange_tmul, LinearMap.BilinForm.baseChange_tmul,
        LinearMap.add_apply, LinearMap.compl₁₂_apply, add_smul]
    | add y z hy hz => simp only [map_add, hy, hz]; ring
  | add x z hx hz => simp only [map_add, LinearMap.add_apply, hx, hz]; ring

/-- Complexification of a rational multiple of a bilinear form.
Source: Mathlib `LinearMap.BilinForm.baseChange_tmul`. -/
theorem cp_baseChange_smul (B : LinearMap.BilinForm ℚ U) (c : ℚ) (x y : ℂ ⊗[ℚ] U) :
    LinearMap.BilinForm.baseChange ℂ (c • B) x y = (c : ℂ) * B.baseChange ℂ x y := by
  induction x using TensorProduct.inductionOn with
  | tmul a x =>
    induction y using TensorProduct.inductionOn with
    | tmul b y =>
      simp only [LinearMap.BilinForm.baseChange_tmul, LinearMap.smul_apply,
        smul_eq_mul, Algebra.smul_def, RingHom.map_mul]
      rw [show algebraMap ℚ ℂ c = (c : ℂ) from map_ratCast (algebraMap ℚ ℂ) c]
      ring
    | add y z hy hz => simp only [map_add, hy, hz]; ring
  | add x z hx hz => simp only [map_add, LinearMap.add_apply, hx, hz]; ring

/-- Positive rational multiples of a polarization are polarizations.
Source: Cattani–El Zein–Griffiths–Lê, *Hodge Theory*, Definition 3.1.8. -/
theorem cp_polarisation_smul [Module.Finite ℚ U] {n : ℤ} (M : QHodgeStructure n U)
    (P : Polarisation M) (c : ℚ) (hc : 0 < c) :
    ∃ Q : Polarisation M, Q.form = c • P.form := by
  refine ⟨{ form := c • P.form
            nondegenerate := WeilHermitian.nondegenerate_smul hc.ne' P.nondegenerate
            symm := ?_
            orthogonal := ?_
            hermitian_real := ?_
            positive := ?_ }, rfl⟩
  · intro x y
    change c * P.form x y = (-1 : ℚ) ^ n * (c * P.form y x)
    rw [P.symm]
    ring
  · intro a b d e h x hx y hy
    rw [cp_baseChange_smul, P.orthogonal a b d e h x hx y hy, mul_zero]
  · intro a b hab x hx
    rw [cp_baseChange_smul, mul_left_comm]
    simp only [Complex.mul_im, Complex.ratCast_re, Complex.ratCast_im,
      P.hermitian_real a b hab x hx, mul_zero, zero_mul, zero_add]
  · intro a b hab x hx hne
    rw [cp_baseChange_smul, mul_left_comm]
    simp only [Complex.mul_re, Complex.ratCast_re, Complex.ratCast_im, zero_mul, sub_zero]
    exact mul_pos (by exact_mod_cast hc) (P.positive a b hab x hx hne)

/-- A sum of polarizations pulled back along jointly injective Hodge projections is a
polarization whenever its rational form is nondegenerate.
Source: Cattani–El Zein–Griffiths–Lê, *Hodge Theory*, Definition 3.1.8. -/
theorem cp_polarisation_sum [Module.Finite ℚ U] [Module.Finite ℚ V] [Module.Finite ℚ Z]
    {n : ℤ} (MU : QHodgeStructure n U) (MV : QHodgeStructure n V) (MZ : QHodgeStructure n Z)
    (PU : Polarisation MU) (PV : Polarisation MV) (p : Z →ₗ[ℚ] U) (q : Z →ₗ[ℚ] V)
    (hp : ∀ pq x, x ∈ MZ.H pq → p.baseChange ℂ x ∈ MU.H pq)
    (hq : ∀ pq x, x ∈ MZ.H pq → q.baseChange ℂ x ∈ MV.H pq)
    (hinj : ∀ x, p.baseChange ℂ x = 0 → q.baseChange ℂ x = 0 → x = 0)
    (hnd : (PU.form.compl₁₂ p p + PV.form.compl₁₂ q q).Nondegenerate) :
    ∃ PZ : Polarisation MZ, PZ.form = PU.form.compl₁₂ p p + PV.form.compl₁₂ q q := by
  refine ⟨{ form := PU.form.compl₁₂ p p + PV.form.compl₁₂ q q
            nondegenerate := hnd
            symm := ?_
            orthogonal := ?_
            hermitian_real := ?_
            positive := ?_ }, rfl⟩
  · intro x y
    change PU.form (p x) (p y) + PV.form (q x) (q y) =
      (-1 : ℚ) ^ n * (PU.form (p y) (p x) + PV.form (q y) (q x))
    rw [PU.symm, PV.symm, mul_add]
  · intro a b c d h x hx y hy
    rw [cp_baseChange_sumPull, PU.orthogonal a b c d h _ (hp _ _ hx) _ (hp _ _ hy),
      PV.orthogonal a b c d h _ (hq _ _ hx) _ (hq _ _ hy), add_zero]
  · intro a b hab x hx
    rw [cp_baseChange_sumPull, ← sigmaQ_baseChange, ← sigmaQ_baseChange, mul_add,
      Complex.add_im, PU.hermitian_real a b hab _ (hp _ _ hx),
      PV.hermitian_real a b hab _ (hq _ _ hx), add_zero]
  · intro a b hab x hx hne
    rw [cp_baseChange_sumPull, ← sigmaQ_baseChange, ← sigmaQ_baseChange, mul_add, Complex.add_re]
    have hU : 0 ≤ (Iexp (a - b) * PU.form.baseChange ℂ (p.baseChange ℂ x)
        (sigmaQ U (p.baseChange ℂ x))).re := by
      by_cases h : p.baseChange ℂ x = 0
      · simp only [h, map_zero, LinearMap.zero_apply, mul_zero, Complex.zero_re, le_refl]
      · exact (PU.positive a b hab _ (hp _ _ hx) h).le
    have hV : 0 ≤ (Iexp (a - b) * PV.form.baseChange ℂ (q.baseChange ℂ x)
        (sigmaQ V (q.baseChange ℂ x))).re := by
      by_cases h : q.baseChange ℂ x = 0
      · simp only [h, map_zero, LinearMap.zero_apply, mul_zero, Complex.zero_re, le_refl]
      · exact (PV.positive a b hab _ (hq _ _ hx) h).le
    by_cases h : p.baseChange ℂ x = 0
    · exact add_pos_of_nonneg_of_pos hU
        (PV.positive a b hab _ (hq _ _ hx) (fun hq0 => hne (hinj x h hq0)))
    · exact add_pos_of_pos_of_nonneg (PU.positive a b hab _ (hp _ _ hx) h) hV

end HodgeLean.Foundations.Program
