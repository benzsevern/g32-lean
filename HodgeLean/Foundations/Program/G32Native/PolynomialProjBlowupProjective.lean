import HodgeLean.Foundations.Program.G32Native.PolynomialProjProjective
import HodgeLean.Foundations.Program.G32Native.PolynomialBlowupCoordinateMap
import HodgeLean.Foundations.Program.G32Native.BlowupGraphClosedImmersion
import HodgeLean.Foundations.Program.G32Native.ProjectiveSpaceProjectiveBase
import HodgeLean.Foundations.Program.SchoenSelectedGeometryProjectiveSubscheme
import HodgeLean.Ported.Hironaka.Scheme.IdealSheaf.Order.Semicontinuity
import Mathlib.Basic.Complex.Basic
import HodgeLean.Ported.NYLL.SchemeTheory.ProjectiveSpace.TwistingSheafGlobalGeneration
import HodgeLean.Ported.Hironaka.Scheme.BlowUp.Defs

/-! Global finite projective presentations of blow-ups of polynomial projective space. -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace HodgeLean.Foundations.Program

attribute [local instance] MvPolynomial.gradedAlgebra

/-- A blow-up of polynomial projective space has a finite native projective presentation. -/
theorem g32l4_polynomialProj_blowUp_projective (n : ℕ)
    (I : (Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) ℂ)).IdealSheafData) :
    IsProjective (I.blowUpπ ≫ ProjSpace.π ℂ n) := by
  letI : IsProjective (ProjSpace.π ℂ n) := g32l4_polynomialProj_isProjective ℂ n
  letI := (ProjSpace.π ℂ n).isLocallyNoetherian_of_field
  obtain ⟨m, g, hg, f, hf⟩ := g32l4_polynomial_blowUp_coordinate_map ℂ n I
  have hU : ⨆ i, (g32l4_standardProjectiveAffine ℂ n i).1 = ⊤ :=
    Proj.iSup_basicOpen_eq_top _ (MvPolynomial.X : Fin (n + 1) → _)
      (ProjSpace.irrelevant_le_span_X ℂ n)
  let X := Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) ℂ)
  let j : I.blowUp ⟶ ProjectiveSpace (Fin (m + 1)) X :=
    pullback.lift I.blowUpπ f (Subsingleton.elim _ _)
  haveI : IsClosedImmersion j := g32l4_blowUp_graph_closedImmersion I
    (g32l4_standardProjectiveAffine ℂ n) hU m g hg f hf
  haveI : IsProjective (ProjectiveSpace.toBase (Fin (m + 1)) X ≫ ProjSpace.π ℂ n) :=
    g32l4_projectiveSpace_over_projective (ProjSpace.π ℂ n) m
  have h := s0_projective_comp_closedImmersion j
    (ProjectiveSpace.toBase (Fin (m + 1)) X ≫ ProjSpace.π ℂ n)
  simpa only [j, ProjectiveSpace.toBase, pullback.lift_fst_assoc] using h

end HodgeLean.Foundations.Program
