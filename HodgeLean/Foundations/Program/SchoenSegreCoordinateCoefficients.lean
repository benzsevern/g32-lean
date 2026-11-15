import HodgeLean.Foundations.Program.SchoenSegreCoordinateRenames
import HodgeLean.Foundations.Program.SchoenPolynomialProjectiveSpace
import HodgeLean.Foundations.Program.SchoenProjMapBase

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry MvPolynomial
namespace HodgeLean.Foundations.Program

attribute [local instance] MvPolynomial.gradedAlgebra

/-- Every actual Segre coordinate rename fixes its degree-zero polynomial coefficients. -/
theorem s2_segreCoordinateRename_degreeZero (R : Type) [CommRing R] (d n : ℕ)
    (σ : Equiv.Perm (Fin n)) (a : homogeneousSubmodule (Fin n → Fin (d + 1)) R 0) :
    s2_segreCoordinateRename R d n σ (a : MvPolynomial (Fin n → Fin (d + 1)) R) = a := by
  have ha := (ProjectiveSpace.degreeZeroEquiv (Fin n → Fin (d + 1)) R).symm_apply_apply a
  have ha' : C ((ProjectiveSpace.degreeZeroEquiv (Fin n → Fin (d + 1)) R) a) =
      (a : MvPolynomial (Fin n → Fin (d + 1)) R) := congrArg Subtype.val ha
  rw [← ha']
  change MvPolynomial.rename _ (C _) = _
  exact MvPolynomial.rename_C _ _

/-- Actual Segre coordinate scheme maps preserve the polynomial degree-zero structure morphism. -/
theorem s2_segreCoordinateMap_toSpecZero (R : Type) [CommRing R] (d n : ℕ)
    (σ : Equiv.Perm (Fin n)) :
    s2_segreCoordinateMap R d n σ ≫
        Proj.toSpecZero (homogeneousSubmodule (Fin n → Fin (d + 1)) R) =
      Proj.toSpecZero (homogeneousSubmodule (Fin n → Fin (d + 1)) R) := by
  have h := s2_projMap_toSpecZero _ _ (s2_segreCoordinateRename R d n σ)
    (b54_irrelevant_le_map_of_surjective _ (s2_segreCoordinateRename_surjective R d n σ))
    (RingHom.id _) (fun a => (s2_segreCoordinateRename_degreeZero R d n σ a).symm)
  simpa only [s2_segreCoordinateMap, CommRingCat.ofHom_id, Spec.map_id,
    Category.comp_id] using h

/-- Integral polynomial coordinates commute with actual Segre coordinate renames over every coefficient ring. -/
theorem s2_polynomialIntegralCoordinates_rename (R : Type) [CommRing R] (d n : ℕ)
    (σ : Equiv.Perm (Fin n)) :
    (s2_segreCoordinateRename R d n σ).comp
        (s2_polynomialIntegralCoordinates R (Fin n → Fin (d + 1))) =
      (s2_polynomialIntegralCoordinates R (Fin n → Fin (d + 1))).comp
        (s2_segreCoordinateRename (ULift.{0} ℤ) d n σ) := by
  apply GradedRingHom.ext
  suffices h : ((s2_segreCoordinateRename R d n σ).comp
      (s2_polynomialIntegralCoordinates R (Fin n → Fin (d + 1)))).toRingHom =
    ((s2_polynomialIntegralCoordinates R (Fin n → Fin (d + 1))).comp
      (s2_segreCoordinateRename (ULift.{0} ℤ) d n σ)).toRingHom from
    fun x => RingHom.congr_fun h x
  apply MvPolynomial.ringHom_ext
  · intro c
    let F := ((s2_segreCoordinateRename R d n σ).comp
      (s2_polynomialIntegralCoordinates R (Fin n → Fin (d + 1)))).toRingHom
    let G := ((s2_polynomialIntegralCoordinates R (Fin n → Fin (d + 1))).comp
      (s2_segreCoordinateRename (ULift.{0} ℤ) d n σ)).toRingHom
    have H : (F.comp C).comp (ULift.ringEquiv.symm : ℤ ≃+* ULift.{0} ℤ).toRingHom =
        (G.comp C).comp (ULift.ringEquiv.symm : ℤ ≃+* ULift.{0} ℤ).toRingHom :=
      Subsingleton.elim _ _
    exact RingHom.congr_fun H c.down
  · intro b
    simp only [GradedRingHom.coe_toRingHom, GradedRingHom.comp_apply,
      s2_polynomialIntegralCoordinates_X, s2_segreCoordinateRename_X]

end HodgeLean.Foundations.Program
