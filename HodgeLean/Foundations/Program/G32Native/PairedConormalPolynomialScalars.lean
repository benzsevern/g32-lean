import HodgeLean.Ported.NYLL.SchemeTheory.ProjectiveSpace.TwistingSheafPolynomialSections
import HodgeLean.Ported.NYLL.SchemeTheory.ProjectiveSpace.TwistingSheafCechComparison

/-! # Structural scalar compatibility of the actual polynomial chart coefficients -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry MvPolynomial HomogeneousLocalization Opposite
open AlgebraicCurves.Cohomology.Cech.Proofs.OModulePresheaf_cechFinite_unit_of_isClosedImmersion_proj.AlgebraicGeometry.ProjSpace
namespace HodgeLean.Foundations.Program.G32Native
attribute [local instance] MvPolynomial.gradedAlgebra
variable (R : Type) [CommRing R] (k : ℕ)
local notation "𝒜" => MvPolynomial.homogeneousSubmodule (Fin (k + 1)) R
local notation "P" => Proj 𝒜
local notation "sP" => (𝟙 P) ≫ ProjSpace.π R k

/-- Multiplying the homogeneous numerator uses the original structural scalar on the chart. -/
theorem conormal_homogeneousRatioSection_smul (d : ℕ) (p : 𝒜 d)
    (i : Fin (k + 1)) (r : R) :
    ProjSpace.homogeneousRatioSection R k d (r • p) i =
      ((sP).constToPresheaf.app (op (ProjSpace.standardOpen R k i))).hom r *
        ProjSpace.homogeneousRatioSection R k d p i := by
  letI := ClosedImmCech.canonicalAlg sP (ProjSpace.standardOpen R k i)
  have hb :
      (Proj.awayToSection 𝒜 (X i)).hom
        ((HomogeneousLocalization.fromZeroRingHom 𝒜 _) (ProjSpace.grad0Equiv R k r)) =
      ((sP).constToPresheaf.app (op (ProjSpace.standardOpen R k i))).hom r := by
    have h := ClosedImmCech.canonicalAlg_eq (A := R) (n := k) (𝟙 P) {i} (Finset.singleton_nonempty i) r
    have hp : (∏ j ∈ ({i} : Finset (Fin (k + 1))), (X j : MvPolynomial (Fin (k + 1)) R)) = X i := by simp
    rw [hp] at h
    simp only [Scheme.Hom.id_app, CommRingCat.id_apply] at h
    exact h
  rw [← hb]
  unfold ProjSpace.homogeneousRatioSection
  rw [← map_mul]
  apply congrArg (Proj.awayToSection 𝒜 (X i)).hom
  apply HomogeneousLocalization.val_injective
  have hv : (HomogeneousLocalization.fromZeroRingHom 𝒜
      (Submonoid.powers (X i)) (ProjSpace.grad0Equiv R k r)).val =
      Localization.mk (C r) 1 := rfl
  rw [HomogeneousLocalization.val_mul, Away.val_mk, Away.val_mk, hv,
    Localization.mk_mul, SetLike.val_smul, MvPolynomial.smul_eq_C_mul, one_mul]

end HodgeLean.Foundations.Program.G32Native
