import HodgeLean.Foundations.BundleThom.AnalyticNormalFramesHelpers
import HodgeLean.Foundations.TubularEuler.NormalAlgebraicAtlasHelpers

/-! # Actual normal fibres in transverse rank zero

The selected frame identifies the original conormal with the empty coordinate space.
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
set_option maxRecDepth 2048
open CategoryTheory AlgebraicGeometry Bundle
namespace HodgeLean.Foundations.TubularEuler
open BundleThom

theorem normalFibre_subsingleton_of_rank_zero
    {Q : Over (Spec ↧ℂ)} {V : Scheme} (j : Q.left ⟶ V)
    (sV : V ⟶ Spec ↧ℂ) (hj : j ≫ sV = Q.hom)
    [IsClosedImmersion j] [SmoothOfRelativeDimension 0 Q.hom]
    [SmoothOfRelativeDimension 0 sV] (x : ComplexPoint Q) :
    Subsingleton (i1_normalFibre j x) := by
  obtain ⟨e⟩ := i1_conormalFibre_coordinates_nonempty j 0 sV hj x
  letI : Subsingleton (i1_conormalFibre j x) := e.injective.subsingleton
  refine ⟨fun f g => LinearMap.ext fun v => ?_⟩
  have hv : v = 0 := Subsingleton.elim _ _
  rw [hv, map_zero, map_zero]

def zeroRankNormalProjectionHomeomorph
    {Q : Over (Spec ↧ℂ)} {V : Scheme} (j : Q.left ⟶ V)
    (sV : V ⟶ Spec ↧ℂ) (hj : j ≫ sV = Q.hom)
    [IsClosedImmersion j] [SmoothOfRelativeDimension 0 Q.hom]
    [SmoothOfRelativeDimension 0 sV] :
    letI := i1_normalTotalTopology j 0
    TotalSpace (Fin 0 → ℂ) (i1_normalFibre j) ≃ₜ ComplexPoint Q := by
  letI := i1_normalTotalTopology j 0
  letI (x : ComplexPoint Q) := i1_normalFibreTopology j x
  let frames := i1_smoothConormalFrameAt j 0 sV hj
  letI := normalFramedFiberBundle j 0 frames
  letI := normalFramedVectorBundle j 0 frames
  letI (x : ComplexPoint Q) : Subsingleton (i1_normalFibre j x) :=
    normalFibre_subsingleton_of_rank_zero j sV hj x
  refine {
    toEquiv := {
      toFun := Bundle.TotalSpace.proj
      invFun := Bundle.zeroSection (Fin 0 → ℂ) (i1_normalFibre j)
      left_inv := ?_
      right_inv := fun _ => rfl }
    continuous_toFun := i1_normalProjection_continuous j 0
    continuous_invFun := Bundle.Trivialization.continuous_zeroSection ℂ }
  rintro ⟨x, v⟩
  exact congrArg (fun w => (⟨x, w⟩ : Bundle.TotalSpace (Fin 0 → ℂ) (i1_normalFibre j)))
    (Subsingleton.elim 0 v)

#print axioms normalFibre_subsingleton_of_rank_zero
#print axioms zeroRankNormalProjectionHomeomorph

end HodgeLean.Foundations.TubularEuler
