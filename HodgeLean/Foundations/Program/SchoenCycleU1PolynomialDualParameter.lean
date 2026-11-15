import HodgeLean.Foundations.Program.SchoenCycleU1PolynomialParameterRegular
import HodgeLean.Foundations.Program.SchoenCycleU1SpecSectionEvaluation

/-! # The actual dual-number polynomial parameter and its neighbourhoods -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry Filter Topology
namespace HodgeLean.Foundations.Program

/-- The specified polynomial parameter restricted to the actual dual-number
first-order neighbourhood of its origin.
Source: Hartshorne, Algebraic Geometry, II.8, the parameter ε. -/
def s2e_u1_polynomialDualParameter :
    s2e_u1_specOver (DualNumber ℂ) ⟶ s2e_u1_specOver (Polynomial ℂ) :=
  s2e_u1_specOverMap (Polynomial.aeval (TrivSqZeroExt.inr (1 : ℂ) : DualNumber ℂ))

/-- Every principal parameter neighbourhood of zero contains the entire
actual dual-number parameter map, since its denominator stays a unit.
Source: Hartshorne, Algebraic Geometry, II.2 and II.8; Mathlib,
`TrivSqZeroExt.isUnit_iff_isUnit_fst` and `AlgebraicGeometry.SpecMap_preimage_basicOpen`. -/
theorem s2e_u1_polynomialDualParameter_basicOpen
    (r : Γ((s2e_u1_specOver (Polynomial ℂ)).left, ⊤))
    (h0 : (s2e_u1_polynomialParameterPoint 0).underlying ∈
      (s2e_u1_specOver (Polynomial ℂ)).left.basicOpen r) :
    ⊤ ≤ s2e_u1_polynomialDualParameter.left ⁻¹ᵁ
      (s2e_u1_specOver (Polynomial ℂ)).left.basicOpen r := by
  let q := (Scheme.ΓSpecIso (CommRingCat.of (Polynomial ℂ))).hom.hom r
  have hq0 : q.eval 0 ≠ 0 := by
    have hn := (Point.mem_overOpen_basicOpen_iff_evaluate_ne_zero r
      (s2e_u1_polynomialParameterPoint 0) (by trivial)).mp h0
    rwa [s2e_u1_polynomialParameterPoint_evaluate_top] at hn
  have hj := DFunLike.congr_fun s2e_u1_polynomialFunction_jet q
  change s2e_u1_analyticGermJet (s2e_u1_analyticGerm (fun t => q.eval t)
    (s2e_u1_polynomialFunction q).property) = (Polynomial.aeval (TrivSqZeroExt.inr (1 : ℂ) : DualNumber ℂ)).toRingHom q at hj
  have hv : ((Polynomial.aeval (TrivSqZeroExt.inr (1 : ℂ) : DualNumber ℂ)).toRingHom q).fst = q.eval 0 := by
    rw [← hj]
    change (s2e_u1_analyticGermJet (s2e_u1_analyticGerm (fun t => q.eval t)
      (s2e_u1_polynomialFunction q).property)).fst = _
    rw [s2e_u1_analyticGermJet_representative]
    simp only [TrivSqZeroExt.fst_add, TrivSqZeroExt.fst_inl, TrivSqZeroExt.fst_inr, add_zero]
  have hdu : IsUnit ((Polynomial.aeval (TrivSqZeroExt.inr (1 : ℂ) : DualNumber ℂ)).toRingHom q) := by
    apply TrivSqZeroExt.isUnit_iff_isUnit_fst.mpr
    apply isUnit_iff_ne_zero.mpr
    rwa [hv]
  change ⊤ ≤ (Spec.map (CommRingCat.ofHom
    (Polynomial.aeval (TrivSqZeroExt.inr (1 : ℂ) : DualNumber ℂ)).toRingHom)) ⁻¹ᵁ
      (Spec (CommRingCat.of (Polynomial ℂ))).basicOpen r
  rw [basicOpen_eq_of_affine', SpecMap_preimage_basicOpen]
  intro x _
  change (Polynomial.aeval (TrivSqZeroExt.inr (1 : ℂ) : DualNumber ℂ)).toRingHom q ∉ x.asIdeal
  intro hm
  exact x.isPrime.ne_top (x.asIdeal.eq_top_of_isUnit_mem hm hdu)

/-- Every actual parameter open containing the origin contains the whole
dual-number parameter map, by a principal affine neighbourhood inside it.
Source: Hartshorne, Algebraic Geometry, II.2, principal neighbourhood bases. -/
theorem s2e_u1_polynomialDualParameter_open
    (U : (s2e_u1_specOver (Polynomial ℂ)).left.Opens)
    (h0 : (s2e_u1_polynomialParameterPoint 0).underlying ∈ U) :
    ⊤ ≤ s2e_u1_polynomialDualParameter.left ⁻¹ᵁ U := by
  let X := s2e_u1_specOver (Polynomial ℂ)
  have hXa : IsAffineOpen (⊤ : X.left.Opens) := by
    change IsAffineOpen (⊤ : (Spec (CommRingCat.of (Polynomial ℂ))).Opens)
    exact isAffineOpen_top _
  obtain ⟨r, hrU, hr0⟩ := hXa.exists_basicOpen_le
    (⟨(s2e_u1_polynomialParameterPoint 0).underlying, h0⟩ : U) (by trivial)
  have hrD := s2e_u1_polynomialDualParameter_basicOpen r hr0
  intro z hz
  exact hrU (hrD hz)

end HodgeLean.Foundations.Program
