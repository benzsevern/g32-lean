import HodgeLean.Foundations.Program.SchoenComplexSegreEmbedding
import HodgeLean.Foundations.Program.SchoenPolynomialProjectivePermutations

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry MvPolynomial
open HodgeLean.Foundations HodgeLean.Adapters HodgeLean.RealDefs
namespace HodgeLean.Foundations.Program

attribute [local instance] MvPolynomial.gradedAlgebra

/-- The actual polynomial Proj scalar-extension comparison as an isomorphism over its coefficient spectrum. -/
def s2_polynomialProjectiveSpaceOverIso (R ι : Type) [CommRing R] :
    Over.mk (Proj.toSpecZero (homogeneousSubmodule ι R) ≫
      Spec.map (ProjectiveSpace.degreeZeroEquiv ι R).symm.toCommRingCatIso.hom) ≅
    (s2_terminalBaseChange (Spec (.of R))).obj
      (Proj (homogeneousSubmodule ι (ULift.{0} ℤ))) :=
  Over.isoMk (s2_polynomialProjectiveSpaceIso R ι)
    (s2_polynomialProjectiveSpaceIso_toBase R ι)

/-- The actual complex Segre morphism expressed in polynomial Proj coordinates over the complex field. -/
def s2_polynomialSegreMap (d n : ℕ) :
    g3_power ((s2_terminalBaseChange (Spec ↧ℂ)).obj (g3c_P d)) n ⟶
      Over.mk (Proj.toSpecZero (homogeneousSubmodule (Fin n → Fin (d + 1)) ℂ) ≫
        Spec.map (ProjectiveSpace.degreeZeroEquiv (Fin n → Fin (d + 1)) ℂ).symm.toCommRingCatIso.hom) :=
  s2_complexSegreMap d n ≫
    (s2_polynomialProjectiveSpaceOverIso ℂ (Fin n → Fin (d + 1))).inv

/-- The actual polynomial-coordinate complex Segre morphism is a scheme closed immersion. -/
theorem s2_polynomialSegreMap_isClosedImmersion (d n : ℕ) :
    IsClosedImmersion (s2_polynomialSegreMap d n).left := by
  letI := s2_complexSegreMap_isClosedImmersion d n
  haveI : IsIso (s2_polynomialProjectiveSpaceOverIso ℂ (Fin n → Fin (d + 1))).inv.left := by
    change IsIso ((Over.forget (Spec ↧ℂ)).map
      (s2_polynomialProjectiveSpaceOverIso ℂ (Fin n → Fin (d + 1))).inv)
    infer_instance
  change IsClosedImmersion ((s2_complexSegreMap d n).left ≫
    (s2_polynomialProjectiveSpaceOverIso ℂ (Fin n → Fin (d + 1))).inv.left)
  exact IsClosedImmersion.comp _ _

/-- The actual polynomial-coordinate complex Segre morphism intertwines retained factor permutations with the polynomial Proj coordinate maps. -/
theorem s2_polynomialSegreMap_permute (d n : ℕ) (σ : Equiv.Perm (Fin n)) :
    (s2_permute ((s2_terminalBaseChange (Spec ↧ℂ)).obj (g3c_P d)) n σ).left ≫
        (s2_polynomialSegreMap d n).left =
      (s2_polynomialSegreMap d n).left ≫ s2_segreCoordinateMap ℂ d n σ := by
  let e := s2_polynomialProjectiveSpaceIso ℂ (Fin n → Fin (d + 1))
  apply (cancel_mono e.hom).mp
  change ((s2_permute ((s2_terminalBaseChange (Spec ↧ℂ)).obj (g3c_P d)) n σ).left ≫
      ((s2_complexSegreMap d n).left ≫ e.inv)) ≫ e.hom =
    ((s2_complexSegreMap d n).left ≫ e.inv ≫ s2_segreCoordinateMap ℂ d n σ) ≫ e.hom
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [s2_polynomialProjectiveSpaceIso_permute]
  dsimp only [e]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  exact congrArg (fun f => f.left) (s2_complexSegreMap_permute d n σ)

end HodgeLean.Foundations.Program
