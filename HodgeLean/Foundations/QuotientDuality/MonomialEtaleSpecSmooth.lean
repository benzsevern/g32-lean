import Mathlib.AlgebraicGeometry.AffineSpace
import Mathlib.AlgebraicGeometry.Morphisms.Etale

/-! Relative dimensions of schemes with etale polynomial parameters. -/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.QuotientDuality

theorem etale_polynomial_spec_smooth
    (k A : Type) [CommRing k] [CommRing A] (n : ℕ)
    (j : k →+* A) (b : MvPolynomial (Fin n) k →+* A)
    (hb : b.Etale) (hbase : b.comp MvPolynomial.C = j) :
    SmoothOfRelativeDimension n (Spec.map (CommRingCat.ofHom j)) := by
  let t := Spec.map (CommRingCat.ofHom b)
  let p := Spec.map (CommRingCat.ofHom (MvPolynomial.C : k →+* MvPolynomial (Fin n) k))
  letI : Etale t := HasRingHomProperty.Spec_iff.mpr hb
  letI : SmoothOfRelativeDimension 0 t :=
    (Etale.iff_smoothOfRelativeDimension_zero (f := t)).mp inferInstance
  letI : SmoothOfRelativeDimension n p := by
    dsimp [p]
    rw [← AffineSpace.SpecIso_inv_over (n := Fin n) (CommRingCat.of k)]
    letI : SmoothOfRelativeDimension n
        (AffineSpace (Fin n) (Spec (CommRingCat.of k)) ↘ Spec (CommRingCat.of k)) :=
      AffineSpace.smoothOfRelativeDimension_of_card_eq _ (by simp)
    simpa only [Nat.zero_add] using
      (smoothOfRelativeDimension_comp
        (f := (AffineSpace.SpecIso (Fin n) (CommRingCat.of k)).inv)
        (n := 0) (m := n)
        (AffineSpace (Fin n) (Spec (CommRingCat.of k)) ↘ Spec (CommRingCat.of k)))
  have heq : t ≫ p = Spec.map (CommRingCat.ofHom j) := by
    change Spec.map _ ≫ Spec.map _ = _
    rw [← Spec.map_comp]
    exact congrArg Spec.map (congrArg CommRingCat.ofHom hbase)
  rw [← heq]
  have H : SmoothOfRelativeDimension (0 + n) (t ≫ p) :=
    smoothOfRelativeDimension_comp (f := t) (n := 0) (m := n) p
  simpa only [Nat.zero_add] using H

#print axioms etale_polynomial_spec_smooth
end HodgeLean.Foundations.QuotientDuality
