import HodgeLean.Foundations.Program.G32Native.ProjectiveIdealTransitions
import HodgeLean.Foundations.Program.G32Native.BlowupCompatibleGeneratorMap

/-! Finite global projective coordinates for blow-ups of polynomial projective space. -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry MvPolynomial TopologicalSpace
open AlgebraicGeometry.ProjSpace AlgebraicGeometry.Scheme.IdealSheafData
namespace HodgeLean.Foundations.Program
attribute [local instance] MvPolynomial.gradedAlgebra

/-- Every centre on a locally Noetherian polynomial projective space has compatible global blow-up coordinates. -/
theorem g32l4_polynomial_blowUp_coordinate_map (R : Type) [CommRing R] (n : ℕ)
    [IsLocallyNoetherian (Proj (homogeneousSubmodule (Fin (n + 1)) R))]
    (I : (Proj (homogeneousSubmodule (Fin (n + 1)) R)).IdealSheafData) :
    ∃ m : ℕ, ∃ g : ∀ i : Fin (n + 1), Fin (m + 1) →
        I.ideal (g32l4_standardProjectiveAffine R n i),
      (∀ i, Ideal.span (Set.range (fun k => (g i k).val)) =
        I.ideal (g32l4_standardProjectiveAffine R n i)) ∧
      ∃ f : I.blowUp ⟶ Proj (homogeneousSubmodule (Fin (m + 1)) (ULift.{0} ℤ)),
        ∀ i k, blowUp.chart I (g32l4_standardProjectiveAffine R n i) (g i k) ≫ f =
          g32l4_blowUp_chart_projectiveMap
            (I.ideal (g32l4_standardProjectiveAffine R n i)) m (g i) k := by
  obtain ⟨d, m, g, hg, ht⟩ := g32l4_projective_ideal_compatible_generators R n I
  have hU : ⨆ i, (g32l4_standardProjectiveAffine R n i).1 = ⊤ :=
    Proj.iSup_basicOpen_eq_top _ (MvPolynomial.X : Fin (n + 1) → _)
      (irrelevant_le_span_X R n)
  obtain ⟨f, hf⟩ := g32l4_blowUp_compatible_generator_map I
    (g32l4_standardProjectiveAffine R n) hU m g hg (fun i j => ⟨_, ht i j⟩)
  exact ⟨m, g, hg, f, hf⟩

end HodgeLean.Foundations.Program
