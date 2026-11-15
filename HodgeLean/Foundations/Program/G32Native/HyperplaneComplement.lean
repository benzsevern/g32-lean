import HodgeLean.Foundations.Program.G32Native.Defs
import HodgeLean.Foundations.Program.SchoenCycleProjectivePoints
import HodgeLean.Foundations.Program.SchoenCycleC11Sub2
import Mathlib.Analysis.Convex.Contractible
import HodgeLean.Foundations.Program.HurwitzFamilyMarkedB62cLocalLifting
import HodgeLean.Foundations.Program.G32Native.RelativeComplement
import HodgeLean.Foundations.Program.SchoenCycleC2SupportHelpers

/-! # The actual coordinate hyperplane and its affine complement -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.ComplexProjectiveSpace
open HodgeLean.Adapters HodgeLean.Foundations.Program
namespace HodgeLean.Foundations.Program.G32Native
open HodgeLean.Foundations.Program.G32Native.TowerOrbit
attribute [local instance] MvPolynomial.gradedAlgebra

/-- The actual coordinate ideal vanishes exactly when its homogeneous coordinate does. -/
theorem coordinate_hyperplane_membership (k : ℕ) (v : CoordinateSpace k) (hv : v ≠ 0) :
    (vectorToComplexPoint v hv).underlying ∈ (s2e_hyperplaneIdeal k).support ↔ v 0 = 0 := by
  have hs := Scheme.IdealSheafData.coe_support_vanishingIdeal
    (X := (ProjectiveSpace (Fin (k + 1)) (Spec ↧ℂ)))
    (⟨(projectiveSpaceBasicOpen k (MvPolynomial.X 0)).carrierᶜ,
      (projectiveSpaceBasicOpen k (MvPolynomial.X 0)).isOpen.isClosed_compl⟩)
  change _ ∈ (s2e_hyperplaneIdeal k).support.carrier ↔ _
  rw [show (s2e_hyperplaneIdeal k).support.carrier =
    (projectiveSpaceBasicOpen k (MvPolynomial.X 0)).carrierᶜ from hs]
  change ¬ ((vectorToProjectiveSpace v hv ≫ pullback.snd _ _)
    (IsLocalRing.closedPoint ℂ) ∈ Proj.basicOpen (UniversalGrading k) (MvPolynomial.X 0)) ↔ _
  rw [vectorToProjectiveSpace_toProj]
  change ¬ IsLocalRing.closedPoint ℂ ∈
    chartIntegralProj v hv ⁻¹ᵁ Proj.basicOpen (UniversalGrading k) (MvPolynomial.X 0) ↔ _
  rw [chartIntegralProj_preimage_basicOpen v hv (MvPolynomial.X 0) zero_lt_one
    (MvPolynomial.isHomogeneous_X _ _)]
  simp [coordinateEvaluationHom]
  split_ifs with h
  · change (¬ False) ↔ v 0 = 0
    simp [h]
  · change (¬ True) ↔ v 0 = 0
    simp [h]

#print axioms coordinate_hyperplane_membership
/-- The complement of the actual coordinate hyperplane has its usual affine chart. -/
theorem coordinate_hyperplane_complement_chart (k : ℕ) :
    Nonempty (
      {x : ComplexPoint (Over.mk (ProjectiveSpace.toBase (Fin (k + 1)) (Spec ↧ℂ))) //
        x.underlying ∉ (s2e_hyperplaneIdeal k).support}
      ≃ₜ ({j : Fin (k + 1) // j ≠ 0} → ℂ)) := by
  obtain ⟨U, hU, ⟨HU⟩⟩ := s2e_c11_classical_projective_chart k 0
  let E := s2e_projectivePointHomeomorph k
  have h (p : Projectivization ℂ (CoordinateSpace k)) :
      p ∈ U ↔ (E p).underlying ∉ (s2e_hyperplaneIdeal k).support := by
    induction p using Projectivization.ind with
    | h v hv =>
      rw [hU v hv]
      change v 0 ≠ 0 ↔ (vectorToComplexPoint v hv).underlying ∉ _
      exact (not_congr (coordinate_hyperplane_membership k v hv)).symm
  exact ⟨(E.subtype h).symm.trans HU⟩

#print axioms coordinate_hyperplane_complement_chart
/-- The actual coordinate hyperplane has contractible complement. -/
theorem coordinate_hyperplane_complement_contractible (k : ℕ) :
    ContractibleSpace
      {x : ComplexPoint (Over.mk (ProjectiveSpace.toBase (Fin (k + 1)) (Spec ↧ℂ))) //
        x.underlying ∉ (s2e_hyperplaneIdeal k).support} := by
  obtain ⟨E⟩ := coordinate_hyperplane_complement_chart k
  exact E.contractibleSpace

#print axioms coordinate_hyperplane_complement_contractible
/-- Forgetting support at the actual coordinate hyperplane is bijective in positive degrees. -/
theorem coordinate_hyperplane_forget_bijective (k n : ℕ) (hn : n ≠ 0) :
    Function.Bijective
      (AlgebraicTopology.Singular.relativeCohomologyToAbsolute ℚ
        (TopPair.ofSubset
          (X := TopCat.of (ComplexPoint
            (Over.mk (ProjectiveSpace.toBase (Fin (k + 1)) (Spec ↧ℂ)))))
          {x | x.underlying ∉ (s2e_hyperplaneIdeal k).support}) (n + 1)) := by
  letI := coordinate_hyperplane_complement_contractible k
  apply relative_to_absolute_bijective
  · exact @b6m_contractible_homology_isZero ℚ _ _ _
      (coordinate_hyperplane_complement_contractible k) n hn
  · exact @b6m_contractible_homology_isZero ℚ _ _ _
      (coordinate_hyperplane_complement_contractible k) (n + 1) (by omega)

#print axioms coordinate_hyperplane_forget_bijective
/-- The specified pulled-back coordinate hyperplane retains a contractible complement. -/
theorem model_hyperplane_complement_contractible
    {Q : Over (Spec ↧ℂ)} {k : ℕ}
    (eQ : Q ≅ Over.mk (ProjectiveSpace.toBase (Fin (k + 1)) (Spec ↧ℂ))) :
    ContractibleSpace
      {x : ComplexPoint Q //
        x.underlying ∉ ((s2e_hyperplaneIdeal k).comap eQ.hom.left).support} := by
  let E := Point.isoMapHomeomorph eQ
  have h (x : ComplexPoint Q) :
      x.underlying ∉ ((s2e_hyperplaneIdeal k).comap eQ.hom.left).support ↔
        (E x).underlying ∉ (s2e_hyperplaneIdeal k).support := by
    rw [Scheme.IdealSheafData.support_comap]
    change (¬ eQ.hom.left x.underlying ∈ (s2e_hyperplaneIdeal k).support) ↔ _
    rw [show (E x).underlying = eQ.hom.left x.underlying from Point.underlying_map _ _]
  letI := coordinate_hyperplane_complement_contractible k
  exact (E.subtype (q := fun x => x.underlying ∉ (s2e_hyperplaneIdeal k).support) h).contractibleSpace

#print axioms model_hyperplane_complement_contractible
/-- The actual component-cycle support map for the specified hyperplane is bijective. -/
theorem model_hyperplane_classToAbsolute_bijective
    {Q : Over (Spec ↧ℂ)} {k : ℕ}
    (eQ : Q ≅ Over.mk (ProjectiveSpace.toBase (Fin (k + 1)) (Spec ↧ℂ)))
    [IsIntegral (s2c_subscheme Q ((s2e_hyperplaneIdeal k).comap eQ.hom.left)).left]
    (n : ℕ) (hn : 0 < n) :
    Function.Bijective (s2e_classToAbsolute Q
      (s2e_componentCycle
        (s2c_subschemeι Q ((s2e_hyperplaneIdeal k).comap eQ.hom.left)) ℚ) n) := by
  let I := (s2e_hyperplaneIdeal k).comap eQ.hom.left
  letI : IsClosedImmersion (s2c_subschemeι Q I).left :=
    inferInstanceAs (IsClosedImmersion I.subschemeι)
  have hs : a3b4_cycleSupport Q.hom
      (s2e_componentCycle (s2c_subschemeι Q I) ℚ) =
        {x | x.underlying ∈ I.support} := by
    rw [s2e_componentCycle_analytic_support]
    change Point.underlying ⁻¹' Set.range I.subschemeι = _
    rw [Scheme.IdealSheafData.range_subschemeι]
    rfl
  unfold s2e_classToAbsolute
  change Function.Bijective
    (AlgebraicTopology.Singular.relativeCohomologyToAbsolute ℚ
      (TopPair.ofSubset (X := TopCat.of (ComplexPoint Q))
        (a3b4_cycleSupport Q.hom (s2e_componentCycle (s2c_subschemeι Q I) ℚ))ᶜ) (2 * n))
  rw [hs]
  have hd : 2 * n = (2 * n - 1) + 1 := by omega
  rw [hd]
  apply relative_to_absolute_bijective
  · exact @b6m_contractible_homology_isZero ℚ _ _ _
      (model_hyperplane_complement_contractible eQ) (2 * n - 1) (by omega)
  · exact @b6m_contractible_homology_isZero ℚ _ _ _
      (model_hyperplane_complement_contractible eQ) ((2 * n - 1) + 1) (by omega)

#print axioms model_hyperplane_classToAbsolute_bijective
end HodgeLean.Foundations.Program.G32Native
