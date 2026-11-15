import HodgeConjecture.Definitions.AlgebraicGeometry.ProjectiveSpace
import Mathlib.Basic.Complex.Basic

/-! # An explicit projective presentation of the complex point

The single homogeneous coordinate is evaluated at one on its standard affine
chart. Base change gives a section of projective space over Spec ℂ. Its structure
morphism is separated, so the section is a closed immersion.
HC no distance; AV milestone no distance.
-/

noncomputable section

namespace HodgeLean.Foundations
open CategoryTheory Limits AlgebraicGeometry MvPolynomial
attribute [local instance] MvPolynomial.gradedAlgebra

private abbrev A := MvPolynomial (Fin 1) (ULift ℤ)
private abbrev grading := homogeneousSubmodule (Fin 1) (ULift ℤ)
private abbrev x : A := MvPolynomial.X 0
private abbrev S := Submonoid.powers x

private def ev : A →+* ℂ :=
  MvPolynomial.eval₂Hom ((Int.castRingHom ℂ).comp ULift.ringEquiv.toRingHom) (fun _ => 1)

private theorem ev_units (s : S) : IsUnit (ev s) := by
  obtain ⟨n, hn⟩ := s.property
  have : ev s = 1 := by
    rw [← hn, map_pow]
    simp [ev, x]
  rw [this]
  exact isUnit_one

private def chartEval : HomogeneousLocalization grading S →+* ℂ :=
  (IsLocalization.lift (S := Localization S) ev_units).comp (algebraMap _ (Localization S))

private def projPoint : Spec ↧ℂ ⟶ Proj grading :=
  Spec.map (CommRingCat.ofHom chartEval) ≫
    ⟨(projIsoSpec grading x (isHomogeneous_X (ULift ℤ) 0) (by decide)).inv ≫
      (Proj.toLocallyRingedSpace grading).ofRestrict
        (ProjectiveSpectrum.basicOpen grading x).isOpenEmbedding⟩

private def pointSection : Spec ↧ℂ ⟶ ℙ(Fin 1; Spec ↧ℂ) :=
  pullback.lift (𝟙 _) projPoint (by apply terminalIsTerminal.hom_ext)

private theorem pointSection_comp : pointSection ≫ ProjectiveSpace.toBase (Fin 1) (Spec ↧ℂ) = 𝟙 _ := by
  apply pullback.lift_fst

private instance : IsClosedImmersion pointSection := by
  have : IsClosedImmersion (pointSection ≫ ProjectiveSpace.toBase (Fin 1) (Spec ↧ℂ)) := by
    rw [pointSection_comp]
    infer_instance
  exact IsClosedImmersion.of_comp pointSection (ProjectiveSpace.toBase (Fin 1) (Spec ↧ℂ))

/-- The identity of Spec ℂ admits an explicit projective presentation of ambient
dimension zero, using the standard chart of the one-variable Proj.
Source: Mathlib `AlgebraicGeometry.projIsoSpec` and `IsClosedImmersion.of_comp`;
upstream `HodgeConjecture/Definitions/AlgebraicGeometry/ProjectiveSpace.lean`
at `2ead713`, `ProjectiveSpace.Presentation`. -/
theorem isProjective_specComplex_id : IsProjective (𝟙 (Spec ↧ℂ)) :=
  ⟨⟨{ ambientDimension := 0, immersion := pointSection, immersion_toBase := pointSection_comp }⟩⟩

example : IsProjective (𝟙 (Spec ↧ℂ)) := isProjective_specComplex_id

end HodgeLean.Foundations

#print axioms HodgeLean.Foundations.isProjective_specComplex_id
