import HodgeLean.Foundations.Program.G32Native.BlowupRatioGenerators
import HodgeLean.Foundations.Program.G32Native.BlowupChartProjectiveMap
import HodgeLean.Foundations.Program.G32Native.SpecNormalizedProjectiveImmersion
import HodgeLean.Foundations.Program.G32Native.NormalizedProjectiveChartImmersion

/-! Immersions given by the base map and normalized blow-up coordinates. -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace HodgeLean.Foundations.Program
attribute [local instance] MvPolynomial.gradedAlgebra

/-- Normalized generator ratios together with the affine base give a projective-space immersion. -/
theorem g32l4_blowUp_chart_graph_immersion {R : Type} [CommRing R]
    (I : Ideal R) (m : ℕ) (g : Fin (m + 1) → I)
    (hg : Ideal.span (Set.range (fun k => (g k : R))) = I) (p : Fin (m + 1)) :
    IsImmersion (pullback.lift
      (Spec.map (CommRingCat.ofHom (algebraMap R (affineBlowUpAlgebra I (g p)))))
      (g32l4_blowUp_chart_projectiveMap I m g p)
      (show (Spec.map (CommRingCat.ofHom (algebraMap R (affineBlowUpAlgebra I (g p))))) ≫
          terminal.from (Spec (.of R)) =
        g32l4_blowUp_chart_projectiveMap I m g p ≫ terminal.from
          (Proj (MvPolynomial.homogeneousSubmodule (Fin (m + 1)) (ULift.{0} ℤ))) from
        Subsingleton.elim _ _) :
      Spec (.of (affineBlowUpAlgebra I (g p))) ⟶ ProjectiveSpace (Fin (m + 1)) (Spec (.of R))) := by
  exact g32l4_spec_normalized_projective_immersion m
    (fun k => affineBlowUpAlgebra.ratio I (g p) (g k)) p
    (g32l4_blowUp_coordinate_self I (g p))
    (g32l4_blowUp_ratios_adjoin_top I (g p) g hg)

end HodgeLean.Foundations.Program
