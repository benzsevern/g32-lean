import HodgeLean.Foundations.Program.SchoenCycleC11LowerHelpers

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open AlgebraicGeometry
open scoped LinearAlgebra.Projectivization
namespace HodgeLean.Foundations.Program

/-- Coordinates normalized at a specified homogeneous coordinate.
Source: Hartshorne, Algebraic Geometry, I.2, affine charts of projective space. -/
def s2e_c11_normalizedCoordinates {n : ℕ} (i : Fin (n + 1)) :
    Projectivization ℂ (ComplexProjectiveSpace.CoordinateSpace n) →
      ComplexProjectiveSpace.CoordinateSpace n :=
  Projectivization.lift (fun v => (v.1 i)⁻¹ • v.1) (by
    intro a b c h
    have hc : c ≠ 0 := by
      intro hc
      apply a.2
      rw [h, hc, zero_smul]
    rw [h]
    funext j
    simp only [Pi.smul_apply, smul_eq_mul, mul_inv_rev]
    calc
      (b.1 i)⁻¹ * c⁻¹ * (c * b.1 j) =
          (b.1 i)⁻¹ * (c⁻¹ * c) * b.1 j := by ring
      _ = (b.1 i)⁻¹ * b.1 j := by rw [inv_mul_cancel₀ hc, mul_one])

/-- Evaluation of normalized projective coordinates on a representative.
Source: Hartshorne, Algebraic Geometry, I.2, affine coordinates. -/
theorem s2e_c11_normalizedCoordinates_mk {n : ℕ} (i : Fin (n + 1))
    (v : ComplexProjectiveSpace.CoordinateSpace n) (hv : v ≠ 0) :
    s2e_c11_normalizedCoordinates i (Projectivization.mk ℂ v hv) = (v i)⁻¹ • v := rfl

/-- The normalized diagonal coordinate detects the standard chart.
Source: Hartshorne, Algebraic Geometry, I.2, homogeneous coordinate charts. -/
theorem s2e_c11_normalizedCoordinates_nonzero {n : ℕ} (i : Fin (n + 1))
    (v : ComplexProjectiveSpace.CoordinateSpace n) (hv : v ≠ 0) :
    s2e_c11_normalizedCoordinates i (Projectivization.mk ℂ v hv) i ≠ 0 ↔ v i ≠ 0 := by
  simp only [s2e_c11_normalizedCoordinates_mk, Pi.smul_apply, smul_eq_mul,
    mul_ne_zero_iff, ne_eq, inv_eq_zero, and_self]

/-- The nonzero normalized diagonal coordinate defines an open chart.
Source: Mathlib, quotient topology; Hartshorne, Algebraic Geometry, I.2. -/
theorem s2e_c11_normalizedChart_isOpen {n : ℕ} (i : Fin (n + 1)) :
    IsOpen {p : Projectivization ℂ (ComplexProjectiveSpace.CoordinateSpace n) |
      s2e_c11_normalizedCoordinates i p i ≠ 0} := by
  have hq : Topology.IsQuotientMap (Projectivization.mk' ℂ :
      {v : ComplexProjectiveSpace.CoordinateSpace n // v ≠ 0} →
        Projectivization ℂ (ComplexProjectiveSpace.CoordinateSpace n)) :=
    isQuotientMap_quotient_mk'
  apply hq.isOpen_preimage.mp
  have ho : IsOpen {v : {v : ComplexProjectiveSpace.CoordinateSpace n // v ≠ 0} |
      v.1 i ≠ 0} := isOpen_ne.preimage ((continuous_apply i).comp continuous_subtype_val)
  simpa only [Set.preimage_ofPred_eq, Projectivization.mk'_eq_mk,
    s2e_c11_normalizedCoordinates_nonzero] using ho

/-- Insert a unit coordinate into an affine tuple.
Source: Hartshorne, Algebraic Geometry, I.2, normalized homogeneous representatives. -/
def s2e_c11_chartVector {n : ℕ} (i : Fin (n + 1))
    (z : {j : Fin (n + 1) // j ≠ i} → ℂ) : ComplexProjectiveSpace.CoordinateSpace n :=
  fun j => if h : j = i then 1 else z ⟨j, h⟩

/-- The inserted coordinate is one.
Source: Hartshorne, Algebraic Geometry, I.2, normalized homogeneous representatives. -/
theorem s2e_c11_chartVector_self {n : ℕ} (i : Fin (n + 1))
    (z : {j : Fin (n + 1) // j ≠ i} → ℂ) : s2e_c11_chartVector i z i = 1 := by
  simp [s2e_c11_chartVector]

/-- An inserted unit coordinate gives a nonzero representative.
Source: Hartshorne, Algebraic Geometry, I.2, normalized homogeneous representatives. -/
theorem s2e_c11_chartVector_ne_zero {n : ℕ} (i : Fin (n + 1))
    (z : {j : Fin (n + 1) // j ≠ i} → ℂ) : s2e_c11_chartVector i z ≠ 0 := by
  intro h
  have hi := congrFun h i
  rw [s2e_c11_chartVector_self] at hi
  exact one_ne_zero hi

/-- Inserting the unit coordinate varies continuously with the affine tuple.
Source: Mathlib, continuity of finite coordinate functions. -/
theorem s2e_c11_chartVector_continuous {n : ℕ} (i : Fin (n + 1)) :
    Continuous (s2e_c11_chartVector (n := n) i) := by
  apply continuous_pi
  intro j
  by_cases h : j = i
  · simpa only [s2e_c11_chartVector, dif_pos h] using
      (continuous_const : Continuous (fun _ : ({j : Fin (n + 1) // j ≠ i} → ℂ) => (1 : ℂ)))
  · simpa only [s2e_c11_chartVector, dif_neg h] using (continuous_apply (⟨j, h⟩ : {j : Fin (n + 1) // j ≠ i}))

/-- The explicit normalized-coordinate maps identify a standard chart with affine space.
Source: Hartshorne, Algebraic Geometry, I.2, affine projective charts. -/
def s2e_c11_normalizedChartHomeomorph {n : ℕ} (i : Fin (n + 1)) :
    {p : Projectivization ℂ (ComplexProjectiveSpace.CoordinateSpace n) //
      s2e_c11_normalizedCoordinates i p i ≠ 0} ≃ₜ
      ({j : Fin (n + 1) // j ≠ i} → ℂ) where
  toFun p j := s2e_c11_normalizedCoordinates i p.1 j.1
  invFun z := ⟨Projectivization.mk ℂ (s2e_c11_chartVector i z)
    (s2e_c11_chartVector_ne_zero i z),
      (s2e_c11_normalizedCoordinates_nonzero _ _ _).mpr
        (by rw [s2e_c11_chartVector_self]; exact one_ne_zero)⟩
  left_inv := by
    rintro ⟨p, hp⟩
    apply Subtype.ext
    induction p using Projectivization.ind with
    | _ v hv =>
      have hi := (s2e_c11_normalizedCoordinates_nonzero i v hv).mp hp
      apply (Projectivization.mk_eq_mk_iff' ℂ _ v _ hv).mpr
      refine ⟨(v i)⁻¹, ?_⟩
      funext j
      change (v i)⁻¹ * v j = s2e_c11_chartVector i
        (fun j => s2e_c11_normalizedCoordinates i (Projectivization.mk ℂ v hv) j.1) j
      by_cases hj : j = i
      · subst j
        rw [s2e_c11_chartVector_self, inv_mul_cancel₀ hi]
      · simp only [s2e_c11_chartVector, dif_neg hj,
          s2e_c11_normalizedCoordinates_mk, Pi.smul_apply, smul_eq_mul]
  right_inv := by
    intro z
    funext j
    change s2e_c11_normalizedCoordinates i
      (Projectivization.mk ℂ (s2e_c11_chartVector i z) _) j.1 = z j
    rw [s2e_c11_normalizedCoordinates_mk, s2e_c11_chartVector_self, inv_one, one_smul]
    simp only [s2e_c11_chartVector, dif_neg j.2]
  continuous_toFun := by
    have hq : Topology.IsQuotientMap (Projectivization.mk' ℂ :
        {v : ComplexProjectiveSpace.CoordinateSpace n // v ≠ 0} →
          Projectivization ℂ (ComplexProjectiveSpace.CoordinateSpace n)) :=
      isQuotientMap_quotient_mk'
    apply (hq.restrictPreimage_isOpen (s2e_c11_normalizedChart_isOpen i)).continuous_iff.mpr
    apply continuous_pi
    intro j
    have hc : Continuous (fun v : {v : {v : ComplexProjectiveSpace.CoordinateSpace n //
        v ≠ 0} // s2e_c11_normalizedCoordinates i (Projectivization.mk' ℂ v) i ≠ 0} =>
        v.1.1 i) := (continuous_apply i).comp
          (continuous_subtype_val.comp continuous_subtype_val)
    have hd : Continuous (fun v : {v : {v : ComplexProjectiveSpace.CoordinateSpace n //
        v ≠ 0} // s2e_c11_normalizedCoordinates i (Projectivization.mk' ℂ v) i ≠ 0} =>
        v.1.1 j.1) := (continuous_apply j.1).comp
          (continuous_subtype_val.comp continuous_subtype_val)
    exact (hc.inv₀ (fun v => (s2e_c11_normalizedCoordinates_nonzero i v.1.1 v.1.2).mp
      v.2)).mul hd
  continuous_invFun := by
    apply Continuous.subtype_mk
    exact continuous_quot_mk.comp ((s2e_c11_chartVector_continuous i).subtype_mk
      (s2e_c11_chartVector_ne_zero i))

end HodgeLean.Foundations.Program
