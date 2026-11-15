import HodgeConjecture.Lemmas.AlgebraicGeometry.ComplexPoint.Projective
import HodgeConjecture.Lemmas.AlgebraicGeometry.ComplexPoint.ProjectiveHausdorff
import HodgeLean.Foundations.SegreProjectiveProofs
import HodgeLean.Foundations.Program.SchoenCycleC11LowerHelpers
import HodgeLean.Foundations.Program.SchoenCycleC11CoordinateHelpers
import Mathlib.Topology.Homotopy.Lifting

/-! # Projective topology for the section construction
Implication from projective coordinates to the required topological properties.
HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.ComplexPoint
namespace HodgeLean.Foundations.Program

attribute [local instance] MvPolynomial.gradedAlgebra

/-- Projective zero-space has its structural isomorphism over every base scheme.
Source: Hartshorne, Algebraic Geometry, Proposition II.2.5(b). -/
theorem s2e_c11_projective_zero_structure (T : Scheme.{0}) :
    IsIso (ProjectiveSpace.toBase (Fin 1) T) := by
  have : IsIso (terminal.from (g3c_P 0)) := spec_g3c_isIso_terminal_from_P_zero_aux
  change IsIso (pullback.fst (terminal.from T) (terminal.from (g3c_P 0)))
  infer_instance

/-- A complex scheme isomorphic to the base has a one-point analytic space.
Source: Mathlib, Over morphism identities and Homeomorph.homeomorphOfUnique. -/
theorem s2e_c11_point_homeomorph_of_structure_isIso
    (X : Over (Spec ↧ℂ)) [IsIso X.hom] :
    Nonempty (Point ℂ X ≃ₜ PUnit) := by
  let p : Point ℂ X := Over.homMk (inv X.hom) (IsIso.inv_hom_id X.hom)
  letI : Unique (Point ℂ X) :=
    { default := p
      uniq := fun q ↦ by
        apply Over.OverMorphism.ext
        apply (cancel_mono X.hom).mp
        exact (Over.w q).trans (Over.w p).symm }
  exact ⟨Homeomorph.homeomorphOfUnique _ _⟩

/-- The nonzero-vector quotient gives local path connectivity of classical projective space.
Source: Mathlib, IsOpen.locallyPathConnectedSpace and Quotient.locallyPathConnectedSpace. -/
theorem s2e_c11_classical_projective_locally_path_connected_direct (k : ℕ) :
    LocallyPathConnectedSpace
      (Projectivization ℂ (ComplexProjectiveSpace.CoordinateSpace k)) := by
  have hopen : IsOpen {v : ComplexProjectiveSpace.CoordinateSpace k | v ≠ 0} :=
    isOpen_ne_fun continuous_id continuous_const
  have : LocallyPathConnectedSpace {v : ComplexProjectiveSpace.CoordinateSpace k // v ≠ 0} :=
    hopen.locallyPathConnectedSpace
  change LocallyPathConnectedSpace
    (Quotient (projectivizationSetoid ℂ (ComplexProjectiveSpace.CoordinateSpace k)))
  infer_instance

/-- The compact coordinate surjection transports local path connectivity to scheme points.
Source: Mathlib, Continuous.isClosedMap and IsQuotientMap.locallyPathConnectedSpace. -/
theorem s2e_c11_projective_points_locally_path_connected (k : ℕ) :
    LocallyPathConnectedSpace
      (Point ℂ (Over.mk (ProjectiveSpace.toBase (Fin (k + 1)) (Spec ↧ℂ)))) := by
  have := s2e_c11_classical_projective_locally_path_connected_direct k
  have hq := ComplexProjectiveSpace.continuous_projectivizationToComplexPoint
    (n := k)
  exact (hq.isClosedMap.isQuotientMap hq
    ComplexProjectiveSpace.surjective_projectivizationToComplexPoint).locallyPathConnectedSpace

/-- Projective dimension zero supplies both topology requirements independently of the positive case.
Source: Hartshorne, Algebraic Geometry, Proposition II.2.5(b); Mathlib homotopy invariance. -/
theorem s2e_c11_projective_zero_topology :
    SimplyConnectedSpace
      (Point ℂ (Over.mk (ProjectiveSpace.toBase (Fin 1) (Spec ↧ℂ)))) ∧
    LocallyPathConnectedSpace
      (Point ℂ (Over.mk (ProjectiveSpace.toBase (Fin 1) (Spec ↧ℂ)))) := by
  have : IsIso (Over.mk (ProjectiveSpace.toBase (Fin 1) (Spec ↧ℂ))).hom :=
    s2e_c11_projective_zero_structure (Spec ↧ℂ)
  obtain ⟨e⟩ := s2e_c11_point_homeomorph_of_structure_isIso
    (Over.mk (ProjectiveSpace.toBase (Fin 1) (Spec ↧ℂ)))
  exact ⟨e.toHomotopyEquiv.simplyConnectedSpace,
    s2e_c11_projective_points_locally_path_connected 0⟩

/-- The scheme point comparison preserves and detects homogeneous coordinate ratios.
Source: Hartshorne, Algebraic Geometry, II.2, standard projective charts;
checked coordinate-membership and same-chart ratio suppliers. -/
theorem s2e_c11_projective_coordinate_comparison_injective (k : ℕ) :
    Function.Injective (ComplexProjectiveSpace.projectivizationToComplexPoint (n := k)) := by
  open ComplexProjectiveSpace in
    intro p q hpq
    induction p using Projectivization.ind with
    | h v hv =>
      induction q using Projectivization.ind with
      | h w hw =>
        have hvec : vectorToComplexPoint v hv = vectorToComplexPoint w hw := hpq
        have hproj : chartIntegralProj v hv = chartIntegralProj w hw := by
          rw [← vectorToProjectiveSpace_toProj v hv, ← vectorToProjectiveSpace_toProj w hw]
          exact congrArg (fun z ↦ z.left ≫ pullback.snd
            (terminal.from (Spec ↧ℂ)) (terminal.from (Proj (UniversalGrading k)))) hvec
        let i := coordinateIndex v hv
        let j := coordinateIndex w hw
        have hi : v i ≠ 0 := coordinateIndex_ne_zero v hv
        have hj : w j ≠ 0 := coordinateIndex_ne_zero w hw
        have hm : chartIntegralProj v hv (IsLocalRing.closedPoint ℂ) ∈
            Proj.basicOpen (UniversalGrading k) (MvPolynomial.X i) := by
          rw [chartIntegralProj_eq_chartIntegralProjAt v hv i hi]
          exact (s2e_c11_chart_coordinate_membership v i i hi).mpr hi
        have hwi : w i ≠ 0 := by
          apply (s2e_c11_chart_coordinate_membership w j i hj).mp
          rw [← chartIntegralProj_eq_chartIntegralProjAt w hw j hj, ← hproj]
          exact hm
        have hsame : chartIntegralProjAt v i hi = chartIntegralProjAt w i hwi := by
          rw [← chartIntegralProj_eq_chartIntegralProjAt v hv i hi,
            ← chartIntegralProj_eq_chartIntegralProjAt w hw i hwi]
          exact hproj
        have hrat := s2e_c11_same_chart_ratios v w i hi hwi hsame
        apply (Projectivization.mk_eq_mk_iff' ℂ v w hv hw).mpr
        refine ⟨v i * (w i)⁻¹, ?_⟩
        ext l
        change (v i * (w i)⁻¹) * w l = v l
        calc
          (v i * (w i)⁻¹) * w l = (w l * (w i)⁻¹) * v i := by ring
          _ = (v l * (v i)⁻¹) * v i := by rw [hrat l]
          _ = v l := by rw [mul_assoc, inv_mul_cancel₀ hi, mul_one]

/-- The actual scheme-point coordinate comparison is a homeomorphism.
Source: Hartshorne, Algebraic Geometry, Appendix B; compact-to-Hausdorff comparison. -/
def s2e_c11_projective_point_homeomorph (k : ℕ) :
    Projectivization ℂ (ComplexProjectiveSpace.CoordinateSpace k) ≃ₜ
      Point ℂ (Over.mk (ProjectiveSpace.toBase (Fin (k + 1)) (Spec ↧ℂ))) := by
  let e := Equiv.ofBijective (ComplexProjectiveSpace.projectivizationToComplexPoint (n := k))
    ⟨s2e_c11_projective_coordinate_comparison_injective k,
      ComplexProjectiveSpace.surjective_projectivizationToComplexPoint⟩
  have hc : Continuous e := ComplexProjectiveSpace.continuous_projectivizationToComplexPoint
  exact e.toHomeomorphOfContinuousClosed hc hc.isClosedMap

end HodgeLean.Foundations.Program
