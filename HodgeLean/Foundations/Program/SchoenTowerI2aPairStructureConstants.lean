import HodgeLean.Foundations.Program.SchoenTowerI2aEtalePairReesChart
import Mathlib.AlgebraicGeometry.GammaSpecAdjunction

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- The paired coefficient square retains the actual scalar structure map
on the source spectrum after passing to its global sections.
Source: Mathlib, `Scheme.ΓSpecIso_inv_naturality` and `MvPolynomial.eval₂Hom_C`. -/
theorem s2v_i2a_paired_chart_structure_constants
    (A R C : Type) [CommRing A] [CommRing R] [CommRing C] (n : ℕ) (i j : Fin n)
    (d : MvPolynomial (Fin n) A →+* R) (a : MvPolynomial (Fin n) A →+* C)
    (φ : R →+* C)
    (hsq : φ.comp d = a.comp (MvPolynomial.eval₂Hom MvPolynomial.C
      (fun l => if l = j then MvPolynomial.X i * MvPolynomial.X j else MvPolynomial.X l))) :
    ((Scheme.ΓSpecIso (CommRingCat.of C)).inv.hom.comp a).comp MvPolynomial.C =
      ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫
        (Spec.map (CommRingCat.ofHom φ) ≫
          Spec.map (CommRingCat.ofHom (d.comp MvPolynomial.C))).appTop).hom := by
  classical
  have hC : a.comp MvPolynomial.C = φ.comp (d.comp MvPolynomial.C) := by
    ext r
    have H := RingHom.congr_fun hsq (MvPolynomial.C r)
    simpa only [RingHom.comp_apply, MvPolynomial.eval₂Hom_C] using H.symm
  rw [RingHom.comp_assoc, hC]
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  exact congrArg CommRingCat.Hom.hom
    (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (φ.comp (d.comp MvPolynomial.C))))

end HodgeLean.Foundations.Program
