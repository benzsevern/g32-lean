import HodgeLean.Foundations.Program.G32Native.EulerModel.NativeCoordinateSingleton
import HodgeLean.Foundations.Program.G32Native.EulerModel.ProjectiveHyperplaneClassTransport

/-! # Every canonical native coordinate hyperplane has the supplied exact normalization -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry TopologicalSpace
open HodgeLean.Adapters HodgeLean.RealDefs HodgeLean.Foundations.Program
namespace HodgeLean.Foundations.Program.G32Native.EulerModel

/-- Every canonical native coordinate hyperplane has exactly the absolute class of the same supplied normalized leading-coordinate coclass. -/
theorem nativeCoordinateSingleton_normalized (k : ℕ) (hk : 0 < k)
    [IsIntegral (Over.mk (ProjectiveSpace.toBase (Fin (k + 1)) (Spec ↧ℂ))).left]
    [Smooth (Over.mk (ProjectiveSpace.toBase (Fin (k + 1)) (Spec ↧ℂ))).hom]
    [IsProjective (Over.mk (ProjectiveSpace.toBase (Fin (k + 1)) (Spec ↧ℂ))).hom] :
    let PP := Over.mk (ProjectiveSpace.toBase (Fin (k + 1)) (Spec ↧ℂ))
    let j0 := s2c_subschemeι PP (s2e_s2b_residueIdeal k 0)
    ∃ (h0 : IsIntegral (s2c_subscheme PP (s2e_s2b_residueIdeal k 0)).left),
      letI := h0
      ∀ (c0 : s2e_supportedClass PP (s2e_componentCycle j0 ℚ) 1),
        a3b4_IsCycleClass PP.hom (s2e_componentCycle j0 ℚ) 1 c0 →
        ∀ (j : Fin (k + 1)) (hj : ({j} : Finset (Fin (k + 1))).card ≤ k),
          cupComparison PP 2 (coordinate_class_at_degree PP k (Iso.refl PP) {j} hj 1
            (Finset.card_singleton j)) =
              s2e_classToAbsolute PP (s2e_componentCycle j0 ℚ) 1 c0 := by
  classical
  let PP := Over.mk (ProjectiveSpace.toBase (Fin (k + 1)) (Spec ↧ℂ))
  let j0 := s2c_subschemeι PP (s2e_s2b_residueIdeal k 0)
  obtain ⟨h0, _, _, _⟩ := nativeResidueHyperplane_class k hk 0
  letI := h0
  refine ⟨h0, ?_⟩
  intro c0 hc0 j hj
  obtain ⟨hI, _, _, cI, hcI⟩ := nativeResidueHyperplane_class k hk j
  letI := hI
  obtain ⟨_, hcmp⟩ := nativeCoordinateSingleton_cupComparison k hk j
  have heq := hcmp cI hcI
  have hperm := nativeResidueHyperplane_absolute_permutation k hk (Equiv.swap 0 j) 0
  have hswap : (Equiv.swap 0 j).symm 0 = j := by simp
  rw [hswap] at hperm
  obtain ⟨_, _, htransport⟩ := hperm
  exact heq.trans (htransport cI c0 hcI hc0)

#print axioms nativeCoordinateSingleton_normalized
end HodgeLean.Foundations.Program.G32Native.EulerModel
