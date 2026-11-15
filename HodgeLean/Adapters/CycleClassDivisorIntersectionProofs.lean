import HodgeLean.Adapters.CycleClassDivisorIntersectionDefs
import HodgeLean.Adapters.CycleClassDivisorPowers

/-! # Proof obligations for the first divisor-intersection primitives
HC no distance; AV milestone no distance.
-/

noncomputable section
set_option maxRecDepth 2048
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint TopologicalSpace
open HodgeLean.RealDefs
namespace HodgeLean.Adapters

/-- The inverse translate of a pure rational cycle has the same class.
Source: Fulton, Intersection Theory, second edition, §1.7 and §19.1;
ccm6_homPullback_cycleClass and ccm8_translation_pullback. -/
theorem ccm11_translated_cycleClass_aux (X : Over (Spec ↧ℂ))
    [GrpObj X] [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    (t : ComplexPoint X) (q : ℕ) (c : AlgebraicCycle X.left ℚ)
    (hc : ∀ x : X.left, c x ≠ 0 → Order.coheight x = q) :
    ccm3_cycleClass X q (ccm3_flatPullback (GrpObj.mulRight t).hom.left c) =
      ccm3_cycleClass X q c := by
  rw [← ccm6_homPullback_cycleClass (GrpObj.mulRight t).hom q c hc]
  exact ccm8_translation_pullback X t (2 * q) (ccm3_cycleClass X q c)

/-- The intersection has finitely many generic components on a Noetherian scheme.
Source: Fulton, Intersection Theory, second edition, §1.5;
Mathlib NoetherianSpace.finite_irreducibleComponents and genericPoints.finite. -/
theorem ccm11_intersection_components_finite_aux (X : Scheme) [IsNoetherian X]
    (I J : X.IdealSheafData) :
    Set.Finite {y : (I ⊔ J).subscheme |
      closure ({y} : Set (I ⊔ J).subscheme) ∈
        irreducibleComponents (I ⊔ J).subscheme} := by
  let Y := (I ⊔ J).subscheme
  haveI : IsLocallyNoetherian Y :=
    LocallyOfFiniteType.isLocallyNoetherian (I ⊔ J).subschemeι
  haveI : CompactSpace Y :=
    (quasiCompact_iff_compactSpace (I ⊔ J).subschemeι).1 inferInstance
  letI : IsNoetherian Y :=
    { toIsLocallyNoetherian := inferInstance
      toCompactSpace := inferInstance }
  exact genericPoints.finite
    TopologicalSpace.NoetherianSpace.finite_irreducibleComponents

private theorem ccm11_isArtinianRing_stalk_of_mem_irreducibleComponents
    {Y : Scheme} [IsLocallyNoetherian Y] (y : Y)
    (hy : closure ({y} : Set Y) ∈ irreducibleComponents Y) :
    IsArtinianRing (Y.presheaf.stalk y) := by
  letI : IsNoetherianRing (Y.presheaf.stalk y) := inferInstance
  have hzero : Order.coheight y = 0 := by
    rw [Order.coheight_eq_zero]
    refine fun z hyz ↦ ?_
    have hzy : z ⤳ y := hyz
    show y ⤳ z
    apply specializes_iff_closure_subset.mpr
    have hz : IsIrreducible (closure ({z} : Set Y)) := isIrreducible_singleton.closure
    exact hy.2 hz (specializes_iff_closure_subset.mp hzy)
  letI : Ring.KrullDimLE 0 (Y.presheaf.stalk y) :=
    krullDimLE_of_coheight_le hzero.le
  exact IsNoetherianRing.isArtinianRing_of_krullDimLE_zero

/-- A generic component has positive finite length, including nonreduced intersections.
Source: Fulton, Intersection Theory, second edition, §1.5;
Stacks Project, Tag 02QS, Lemma 42.9.1. -/
theorem ccm11_intersectionLength_finite_pos_aux (X : Scheme) [IsLocallyNoetherian X]
    (I J : X.IdealSheafData) (y : (I ⊔ J).subscheme)
    (hy : closure ({y} : Set (I ⊔ J).subscheme) ∈
      irreducibleComponents (I ⊔ J).subscheme) :
    0 < ccm11_intersectionLength X I J y ∧
      ccm11_intersectionLength X I J y < ⊤ := by
  let Y := (I ⊔ J).subscheme
  haveI : IsLocallyNoetherian Y :=
    LocallyOfFiniteType.isLocallyNoetherian (I ⊔ J).subschemeι
  haveI : IsArtinianRing (Y.presheaf.stalk y) :=
    ccm11_isArtinianRing_stalk_of_mem_irreducibleComponents y hy
  exact ⟨Module.length_pos, Module.length_ne_top.lt_top⟩

/-- Each generic component occurs with its actual local length.
Source: Fulton, Intersection Theory, second edition, §1.5 and §2.3;
Stacks Project, Tag 02QS. -/
theorem ccm11_intersectionCycle_coeff_aux (X : Scheme) [IsNoetherian X]
    (I J : X.IdealSheafData) (y : (I ⊔ J).subscheme)
    (hy : closure ({y} : Set (I ⊔ J).subscheme) ∈
      irreducibleComponents (I ⊔ J).subscheme) :
    ccm11_intersectionCycle X I J ((I ⊔ J).subschemeι y) =
      ((ccm11_intersectionLength X I J y).toNat : ℚ) := by
  classical
  let S := {y : (I ⊔ J).subscheme |
    closure ({y} : Set (I ⊔ J).subscheme) ∈
      irreducibleComponents (I ⊔ J).subscheme}
  have hS : S.Finite := ccm11_intersection_components_finite_aux X I J
  rw [ccm11_intersectionCycle, finsum_eq_sum_of_support_subset (s := hS.toFinset)]
  · simp only [Function.locallyFinsuppWithin.coe_sum, Finset.sum_apply]
    rw [Finset.sum_eq_single y]
    · simp only [if_pos hy, Function.locallyFinsuppWithin.single_apply, ↓reduceIte]
    · intro y' hy'S hy'ne
      have hιne : (I ⊔ J).subschemeι y' ≠ (I ⊔ J).subschemeι y := by
        exact fun h => hy'ne (Subtype.ext h)
      split
      · rw [Function.locallyFinsuppWithin.single_apply, if_neg hιne.symm]
      · rfl
    · intro hyS
      exact (hyS (hS.mem_toFinset.mpr hy)).elim
  · intro y' hy'
    by_contra hy'S
    have hncomp : ¬ closure ({y'} : Set (I ⊔ J).subscheme) ∈
        irreducibleComponents (I ⊔ J).subscheme :=
      fun h => hy'S (hS.mem_toFinset.mpr h)
    change (if closure ({y'} : Set (I ⊔ J).subscheme) ∈
        irreducibleComponents (I ⊔ J).subscheme then
          Function.locallyFinsuppWithin.single ((I ⊔ J).subschemeι y')
            ((ccm11_intersectionLength X I J y').toNat : ℚ)
        else 0) ≠ 0 at hy'
    rw [if_neg hncomp] at hy'
    exact hy' rfl

end HodgeLean.Adapters
