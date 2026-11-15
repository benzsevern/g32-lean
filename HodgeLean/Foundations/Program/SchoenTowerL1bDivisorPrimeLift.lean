import HodgeLean.Foundations.Program.SchoenTowerL1bDivisorSpecialization
import HodgeLean.Foundations.Program.SchoenTowerL1bDivisorGenericStalk
import HodgeLean.Foundations.Program.SchoenTowerL1bDivisorStalkSpectrum

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry IsLocalRing
namespace HodgeLean.Foundations.Program

/-- An actual point over a specified stalk prime gives an injective pullback that detects its units. -/
theorem s2v_l1b_divisor_prime_stalk_lift
    {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y]
    (f : X ⟶ Y) [IsDominant f] (x : Y)
    (p : Y.presheaf.stalk x) (q : Spec (Y.presheaf.stalk x))
    (hq : q.asIdeal = Ideal.span {p}) (y : X)
    (hy : f y = (Y.fromSpecStalk x) q) :
    ∃ φ : Y.presheaf.stalk x →+* X.presheaf.stalk y,
      Function.Injective φ ∧ (∀ r, IsUnit (φ r) ↔ ¬ p ∣ r) ∧
      ∀ r, s2v_l1b_functionFieldPullback f (algebraMap _ Y.functionField r) =
        algebraMap _ X.functionField (φ r) := by
  have hgen : f y ⤳ x := by
    have H : (Y.fromSpecStalk x) q ∈ Set.range (Y.fromSpecStalk x) := ⟨q, rfl⟩
    rw [Scheme.range_fromSpecStalk] at H
    simpa only [hy, Set.mem_setOf_eq] using H
  let φ : Y.presheaf.stalk x ⟶ X.presheaf.stalk y :=
    Y.presheaf.stalkSpecializes hgen ≫ f.stalkMap y
  have hsquare : Spec.map φ ≫ Y.fromSpecStalk x = X.fromSpecStalk y ≫ f := by
    dsimp only [φ]
    rw [Spec.map_comp, Category.assoc, Scheme.SpecMap_stalkSpecializes_fromSpecStalk,
      Scheme.SpecMap_stalkMap_fromSpecStalk]
  have hpoint : Spec.map φ (closedPoint (X.presheaf.stalk y)) = q := by
    apply (Y.fromSpecStalk x).isEmbedding.injective
    have H := congrArg (fun k : Spec (X.presheaf.stalk y) ⟶ Y =>
      k (closedPoint (X.presheaf.stalk y))) hsquare
    have H' : (Y.fromSpecStalk x) (Spec.map φ (closedPoint (X.presheaf.stalk y))) = f y := by
      simpa only [Scheme.Hom.comp_apply, Scheme.fromSpecStalk_closedPoint] using H
    exact H'.trans hy
  have hcomap : Ideal.comap φ.hom (maximalIdeal (X.presheaf.stalk y)) = Ideal.span {p} := by
    have H := congrArg (fun z : Spec (Y.presheaf.stalk x) => z.asIdeal) hpoint
    exact H.trans hq
  have hgeneric (r : Y.presheaf.stalk x) :
      s2v_l1b_functionFieldPullback f (algebraMap _ Y.functionField r) =
        algebraMap _ X.functionField (φ.hom r) := by
    change _ = algebraMap _ X.functionField
      ((f.stalkMap y).hom ((Y.presheaf.stalkSpecializes hgen).hom r))
    rw [← s2v_l1b_divisor_generic_stalk, s2v_l1b_divisor_specialization_function_field]
  refine ⟨φ.hom, ?_, ?_, hgeneric⟩
  · intro a b hab
    apply IsFractionRing.injective (Y.presheaf.stalk x) Y.functionField
    apply (s2v_l1b_functionFieldPullback f).hom.injective
    rw [hgeneric, hgeneric, hab]
  · intro r
    have H : r ∈ Ideal.comap φ.hom (maximalIdeal (X.presheaf.stalk y)) ↔
        r ∈ Ideal.span {p} := by rw [hcomap]
    simp only [Ideal.mem_comap, mem_maximalIdeal, mem_nonunits_iff, Ideal.mem_span_singleton] at H
    simpa only [not_not] using not_congr H

end HodgeLean.Foundations.Program
