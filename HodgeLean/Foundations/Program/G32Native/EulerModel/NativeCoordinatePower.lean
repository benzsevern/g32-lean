import HodgeLean.Foundations.Program.G32Native.EulerModel.NativeCoordinateNormalization
import HodgeLean.Foundations.Program.G32Native.EulerModel.CoordinatePowerExact

/-! # Coefficient-one coordinate powers on the actual native projective space -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry TopologicalSpace
open HodgeLean.Adapters HodgeLean.RealDefs HodgeLean.Foundations.Program
namespace HodgeLean.Foundations.Program.G32Native.EulerModel

/-- Every positive-codimension native coordinate intersection is exactly the corresponding cup power of the same supplied normalized leading-hyperplane coclass. -/
theorem nativeCoordinatePower_normalized (k : ℕ) (hk : 0 < k)
    [IsIntegral (Over.mk (ProjectiveSpace.toBase (Fin (k + 1)) (Spec ↧ℂ))).left]
    [Smooth (Over.mk (ProjectiveSpace.toBase (Fin (k + 1)) (Spec ↧ℂ))).hom]
    [IsProjective (Over.mk (ProjectiveSpace.toBase (Fin (k + 1)) (Spec ↧ℂ))).hom] :
    let PP := Over.mk (ProjectiveSpace.toBase (Fin (k + 1)) (Spec ↧ℂ))
    let j0 := s2c_subschemeι PP (s2e_s2b_residueIdeal k 0)
    ∃ (h0 : IsIntegral (s2c_subscheme PP (s2e_s2b_residueIdeal k 0)).left),
      letI := h0
      ∀ (c0 : s2e_supportedClass PP (s2e_componentCycle j0 ℚ) 1),
        a3b4_IsCycleClass PP.hom (s2e_componentCycle j0 ℚ) 1 c0 →
        ∀ (n : ℕ) (T : Finset (Fin (k + 1))) (hT : T.card ≤ k)
          (hn : T.card = n), 0 < n →
          cupComparison PP (2 * n) (coordinate_class_at_degree PP k (Iso.refl PP) T hT n hn) =
            s2e_hyperplanePower (TopCat.of (ComplexPoint PP))
              (s2e_classToAbsolute PP (s2e_componentCycle j0 ℚ) 1 c0) n := by
  let PP := Over.mk (ProjectiveSpace.toBase (Fin (k + 1)) (Spec ↧ℂ))
  let j0 := s2c_subschemeι PP (s2e_s2b_residueIdeal k 0)
  obtain ⟨h0, hH⟩ := nativeCoordinateSingleton_normalized k hk
  letI := h0
  refine ⟨h0, ?_⟩
  intro c0 hc0 n T hT hn hpos
  exact coordinate_power_of_singleton_normalization PP k (Iso.refl PP)
    (s2e_classToAbsolute PP (s2e_componentCycle j0 ℚ) 1 c0)
    (hH c0 hc0) n T hT hn hpos

#print axioms nativeCoordinatePower_normalized
end HodgeLean.Foundations.Program.G32Native.EulerModel
