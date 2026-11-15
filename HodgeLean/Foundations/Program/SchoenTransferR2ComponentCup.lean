import HodgeLean.Foundations.Program.SchoenTransferR2ComponentDeformation
import HodgeLean.Foundations.Program.SchoenTransferR2DeformationCup
import HodgeLean.Foundations.Program.SchoenCycleC2ComponentUniquenessHelpers
import HodgeLean.Foundations.Program.SchoenCyclePushDefs
import HodgeLean.Foundations.Program.SchoenTransferR2RelativeLift
import HodgeLean.Adapters.CycleClassDivisorProduct3

/-! # Restriction detects pairings with a retained smooth component

HC no distance; AV milestone no distance.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry AlgebraicTopology.Singular
open HodgeLean.Adapters TopologicalSpace
namespace HodgeLean.Foundations.Program

/-- A class vanishing on the actual component has zero cup with its normalized
component class, even when the ambient scheme is singular away from that component.
Source: Fulton, Intersection Theory, second edition, §19.1; Hatcher, §3.3,
Thom isomorphism and the projection formula.
HC no distance; AV milestone no distance. -/
theorem s4_assembly_component_cup_eq_zero
    {Q W : Over (Spec ↧ℂ)} [IsIntegral Q.left] [Smooth Q.hom] [IsProjective Q.hom]
    [LocallyOfFiniteType W.hom] [QuasiCompact W.hom] [IsSeparated W.hom]
    (ι : Q ⟶ W) [IsClosedImmersion ι.left] (k : ℕ)
    (U : W.left.Opens) (hU : Set.range ι.left ⊆ U)
    (hsm : Smooth (U.ι ≫ W.hom))
    (hcodim : ∀ x ∈ (s2e_componentCycle ι ℚ).support, Order.coheight x = k)
    (c : s2e_supportedClass W (s2e_componentCycle ι ℚ) k)
    (hc : a3b4_IsCycleClass W.hom (s2e_componentCycle ι ℚ) k c)
    (u : Cohomology ℚ (TopCat.of (ComplexPoint W)) (2 * k))
    (hu : s2e_pullback ℚ ι (2 * k) u = 0) :
    HodgeLean.Foundations.Singular.cup (TopCat.of (ComplexPoint W))
      (show 2 * k + 2 * k = 2 * (2 * k) by omega)
      (s2e_classToAbsolute W (s2e_componentCycle ι ℚ) k c) u = 0 := by
  let X := TopCat.of (ComplexPoint W)
  let j : TopCat.of (ComplexPoint Q) ⟶ X := TopCat.ofHom (Point.continuousMap ι)
  have hj : Topology.IsClosedEmbedding (Point.map ι) :=
    ComplexPoint.isClosedEmbedding_map_of_closedImmersion ι
  have hsupp : a3b4_cycleSupport W.hom (s2e_componentCycle ι ℚ) =
      Set.range (Point.map ι) := by
    rw [s2e_componentCycle_analytic_support,
      ComplexPoint.range_map_of_isImmersion_of_comm W Q ι]
  let S : Closeds X := ⟨a3b4_cycleSupport W.hom (s2e_componentCycle ι ℚ),
    hsupp ▸ hj.isClosed_range⟩
  obtain ⟨F, ⟨H⟩, _, V, hV, hF⟩ :=
    s4_assembly_component_ambient_deformation ι k U hU hsm hcodim
  have hz := s4_assembly_deformation_cup_eq_zero X (TopCat.of (ComplexPoint Q)) j
    hj.isEmbedding S hsupp V (by
      change a3b4_cycleSupport W.hom (s2e_componentCycle ι ℚ) ⊆ (V : Set (ComplexPoint W))
      rw [hsupp]
      exact hV) F H
    (by
      intro x hx
      change F x ∈ a3b4_cycleSupport W.hom (s2e_componentCycle ι ℚ)
      rw [hsupp]
      exact hF hx) (2 * k) (2 * k) c u hu
  have hzero (N : ℕ) (hN : 2 * k + 2 * k = N) :
      HodgeLean.Foundations.Singular.cup X hN
        (s2e_classToAbsolute W (s2e_componentCycle ι ℚ) k c) u = 0 := by
    subst N
    exact hz
  exact hzero _ _

#print axioms s4_assembly_component_cup_eq_zero
end HodgeLean.Foundations.Program
