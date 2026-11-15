import HodgeConjecture.Lemmas.AlgebraicGeometry.ComplexPoint.SmoothCoordinates
import HodgeLean.Foundations.Program.SchoenTowerL1aIdealPullback
import HodgeConjecture.Lemmas.AlgebraicGeometry.ComplexPoint.Open
import Mathlib.RingTheory.Localization.Away.Basic

/-! # Localization on actual principal open schemes

Implication from an affine scheme and a global section to the localization
structure on the actual open scheme's global sections.
HC no distance; AV milestone no distance.
-/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- The actual inclusion pullback on global sections of a principal open is localization away from its defining section.
Source: Hartshorne, Algebraic Geometry, II.2, the structure sheaf on principal affine opens. -/
theorem s2v_l1a_openScheme_sections_localization
    (X : Scheme) [IsAffine X] (d : Γ(X, ⊤)) :
    let O := X.basicOpen d
    letI := O.ι.appTop.hom.toAlgebra
    IsLocalization.Away d Γ(O.toScheme, ⊤) := by
  let A := Γ(X, ⊤)
  let O := X.basicOpen d
  let B := Γ(O.toScheme, ⊤)
  let C := Γ(X, O)
  letI : Algebra A B := O.ι.appTop.hom.toAlgebra
  letI : Algebra A C := (X.presheaf.map (homOfLE (show O ≤ ⊤ from le_top)).op).hom.toAlgebra
  letI : IsLocalization.Away d C := (isAffineOpen_top X).isLocalization_basicOpen d
  let e : B ≃ₐ[A] C :=
    { O.topIso.commRingCatIsoToRingEquiv with
      commutes' := fun a => congrArg (fun f : Γ(X, ⊤) ⟶ C => f a)
        (Scheme.Opens.ι_appTop_topIso_hom O) }
  exact IsLocalization.isLocalization_of_algEquiv (Submonoid.powers d) e.symm

end HodgeLean.Foundations.Program
