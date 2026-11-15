import HodgeLean.Foundations.Program.SchoenCycleComplexPointAugmentation
import HodgeConjecture.Lemmas.AlgebraicGeometry.ComplexPoint.Basic

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- A section whose actual stalk value has nonunit pullback vanishes at the marked complex point.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.2, printed p. 13;
Hartshorne, Algebraic Geometry, II.2. -/
theorem s2e_section_evaluate_zero_of_nonunit_pullback
    (X : Over (Spec ↧ℂ)) [IsIntegral X.left] (x : ComplexPoint X)
    (V : X.left.Opens) (hxV : x.underlying ∈ V) (s : Γ(X.left, V))
    (R : Type) [CommRing R] (f : X.left.presheaf.stalk x.underlying →+* R)
    (h : ¬ IsUnit (f (X.left.presheaf.germ V x.underlying hxV s))) :
    Point.evaluate V s x = 0 := by
  letI : Algebra ℂ (X.left.presheaf.stalk x.underlying) :=
    (HodgeLean.Foundations.Curves.stalkC x.underlying).toAlgebra
  let ε := s2e_complex_point_augmentation X x
  have hsur : Function.Surjective ε := fun c => ⟨algebraMap ℂ _ c, ε.commutes c⟩
  have hker := IsLocalRing.ker_eq_maximalIdeal ε.toRingHom hsur
  have hg : X.left.presheaf.germ V x.underlying hxV s ∈
      IsLocalRing.maximalIdeal (X.left.presheaf.stalk x.underlying) := by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    exact fun hu => h (hu.map f)
  rw [← hker] at hg
  change x.stalkHom.hom (X.left.presheaf.germ V x.underlying hxV s) = 0 at hg
  simpa only [Point.evaluate, dif_pos hxV] using hg

#print axioms s2e_section_evaluate_zero_of_nonunit_pullback
end HodgeLean.Foundations.Program
