import HodgeLean.Foundations.Program.SchoenReducedClosedImages
import HodgeLean.Foundations.Program.SchoenHomogeneousQuotientProjPoints
import HodgeLean.Foundations.Program.SchoenProjReduced

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open AlgebraicGeometry CategoryTheory
namespace HodgeLean.Foundations.Program

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- An integral scheme closed in an actual Proj is the Proj quotient by its generic image homogeneous prime. -/
theorem s2_integralClosedProj_presentation {A : Type} [CommRing A]
    (𝒜 : ℕ → AddSubgroup A) [GradedRing 𝒜] (X : Scheme.{0}) [IsIntegral X]
    (f : X ⟶ Proj 𝒜) [IsClosedImmersion f] :
    let p := f (genericPoint X)
    letI := s2_homogeneousQuotientGrading 𝒜 p.asHomogeneousIdeal
    ∃ e : X ≅ Proj (s2_homogeneousQuotientPiece 𝒜 p.asHomogeneousIdeal),
      e.hom ≫ s2_homogeneousQuotientProjMap 𝒜 p.asHomogeneousIdeal = f := by
  let p := f (genericPoint X)
  let I := p.asHomogeneousIdeal
  letI := s2_homogeneousQuotientGrading 𝒜 I
  haveI : I.toIdeal.IsPrime := p.isPrime
  haveI : IsReduced (Proj (s2_homogeneousQuotientPiece 𝒜 I)) :=
    s2_proj_isReduced_of_domain _
  let g := s2_homogeneousQuotientProjMap 𝒜 I
  haveI : IsClosedImmersion g := s2_homogeneousQuotientProjMap_isClosedImmersion 𝒜 I
  have hrange : Set.range f = Set.range g := by
    rw [s2_closedImmersion_range_genericPoint f]
    ext q
    rw [s2_homogeneousQuotientProjMap_mem_range_iff]
    exact (ProjectiveSpectrum.le_iff_mem_closure 𝒜 p q).symm
  exact s2_reducedClosedImmersion_iso_of_range_eq f g hrange

end HodgeLean.Foundations.Program
