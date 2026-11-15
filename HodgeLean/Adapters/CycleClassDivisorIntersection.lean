import HodgeLean.Adapters.CycleClassDivisorIntersectionProofs

/-! # First divisor-intersection primitives: frozen specification

The translation statement is an implication from the existing group and pure-cycle
data. The intersection statements concern the actual sum of two ideal sheaves.
They give neither expected codimension nor a cup-product comparison. No general
position, smooth transverse intersection, O6 or C9 theorem is claimed here.
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
theorem ccm11_translated_cycleClass (X : Over (Spec ↧ℂ))
    [GrpObj X] [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    (t : ComplexPoint X) (q : ℕ) (c : AlgebraicCycle X.left ℚ)
    (hc : ∀ x : X.left, c x ≠ 0 → Order.coheight x = q) :
    ccm3_cycleClass X q (ccm3_flatPullback (GrpObj.mulRight t).hom.left c) =
      ccm3_cycleClass X q c :=
  ccm11_translated_cycleClass_aux X t q c hc

/-- The intersection has finitely many generic components on a Noetherian scheme.
Source: Fulton, Intersection Theory, second edition, §1.5;
Mathlib NoetherianSpace.finite_irreducibleComponents and genericPoints.finite. -/
theorem ccm11_intersection_components_finite (X : Scheme) [IsNoetherian X]
    (I J : X.IdealSheafData) :
    Set.Finite {y : (I ⊔ J).subscheme |
      closure ({y} : Set (I ⊔ J).subscheme) ∈
        irreducibleComponents (I ⊔ J).subscheme} :=
  ccm11_intersection_components_finite_aux X I J

/-- A generic component has positive finite length, including nonreduced intersections.
Source: Fulton, Intersection Theory, second edition, §1.5;
Stacks Project, Tag 02QS, Lemma 42.9.1. -/
theorem ccm11_intersectionLength_finite_pos (X : Scheme) [IsLocallyNoetherian X]
    (I J : X.IdealSheafData) (y : (I ⊔ J).subscheme)
    (hy : closure ({y} : Set (I ⊔ J).subscheme) ∈
      irreducibleComponents (I ⊔ J).subscheme) :
    0 < ccm11_intersectionLength X I J y ∧
      ccm11_intersectionLength X I J y < ⊤ :=
  ccm11_intersectionLength_finite_pos_aux X I J y hy

/-- Each generic component occurs with its actual local length.
Source: Fulton, Intersection Theory, second edition, §1.5 and §2.3;
Stacks Project, Tag 02QS. -/
theorem ccm11_intersectionCycle_coeff (X : Scheme) [IsNoetherian X]
    (I J : X.IdealSheafData) (y : (I ⊔ J).subscheme)
    (hy : closure ({y} : Set (I ⊔ J).subscheme) ∈
      irreducibleComponents (I ⊔ J).subscheme) :
    ccm11_intersectionCycle X I J ((I ⊔ J).subschemeι y) =
      ((ccm11_intersectionLength X I J y).toNat : ℚ) :=
  ccm11_intersectionCycle_coeff_aux X I J y hy

open HodgeLean.Foundations HodgeLean.Foundations.Curves

local instance ccm11_decidableEqE : DecidableEq E.left := Classical.typeDecidableEq _

/-- W1: a nonzero point cycle and a finite-point translation on the cubic.
Source: cubicInfinity_isClosed and the constructed cubic group. -/
example : ccm3_cycleClass E 1
    (ccm3_flatPullback
      (GrpObj.mulRight (Over.homMk finitePoint finitePoint_over : ComplexPoint E)).hom.left
      (Function.locallyFinsuppWithin.single cubicInfinity (1 : ℚ))) =
    ccm3_cycleClass E 1 (Function.locallyFinsuppWithin.single cubicInfinity (1 : ℚ)) := by
  classical
  apply ccm11_translated_cycleClass
  intro x hx
  by_cases h : x = cubicInfinity
  · subst x
    exact coheight_eq_one_of_isClosed E cubicInfinity cubicInfinity_isClosed
  · exact (hx (by simp [Function.locallyFinsuppWithin.single_apply, h])).elim

/-- The point cycle used in W1 is nonzero.
Source: evaluation of a singleton cycle at its support. -/
example : (Function.locallyFinsuppWithin.single cubicInfinity (1 : ℚ) :
    AlgebraicCycle E.left ℚ) ≠ 0 := by
  classical
  intro h
  have := congrArg (fun c : AlgebraicCycle E.left ℚ => c cubicInfinity) h
  simp [Function.locallyFinsuppWithin.single_apply] at this

/-- W2: the actual closed intersection on a Noetherian complex point.
Source: Noetherianity of the spectrum of a field. -/
example := ccm11_intersection_components_finite (Spec ↧ℂ) ⊥ ⊥

/-- The whole closed subscheme of the complex point is irreducible.
Source: the zero ideal has full support, and a field spectrum is irreducible. -/
private instance ccm11_pointIntersection_irreducible :
    IrreducibleSpace ((⊥ ⊔ ⊥ : (Spec ↧ℂ).IdealSheafData).subscheme) := by
  change IrreducibleSpace (((⊥ ⊔ ⊥ : (Spec ↧ℂ).IdealSheafData).support : Set (Spec ↧ℂ)))
  have hs : ((⊥ ⊔ ⊥ : (Spec ↧ℂ).IdealSheafData).support : Set (Spec ↧ℂ)) = Set.univ := by
    rw [sup_idem, Scheme.IdealSheafData.support_bot]
    rfl
  rw [← isIrreducible_iff_irreducibleSpace, hs]
  exact IrreducibleSpace.isIrreducible_univ _

/-- The constructed generic point is a component generic point.
Source: genericPoint_closure and irreducibleComponents_eq_singleton. -/
private theorem ccm11_pointIntersection_component :
    closure ({genericPoint ((⊥ ⊔ ⊥ : (Spec ↧ℂ).IdealSheafData).subscheme)} :
      Set ((⊥ ⊔ ⊥ : (Spec ↧ℂ).IdealSheafData).subscheme)) ∈
      irreducibleComponents ((⊥ ⊔ ⊥ : (Spec ↧ℂ).IdealSheafData).subscheme) := by
  rw [genericPoint_closure, irreducibleComponents_eq_singleton]
  exact Set.mem_singleton _

/-- W3: all length premises instantiated on the complex point.
Source: the zero ideal and the constructed generic-point witness. -/
example := ccm11_intersectionLength_finite_pos (Spec ↧ℂ) ⊥ ⊥
  (genericPoint ((⊥ ⊔ ⊥ : (Spec ↧ℂ).IdealSheafData).subscheme))
  ccm11_pointIntersection_component

/-- W4: all coefficient premises instantiated on the same actual intersection.
Source: the zero ideal and the constructed generic-point witness. -/
example := ccm11_intersectionCycle_coeff (Spec ↧ℂ) ⊥ ⊥
  (genericPoint ((⊥ ⊔ ⊥ : (Spec ↧ℂ).IdealSheafData).subscheme))
  ccm11_pointIntersection_component

end HodgeLean.Adapters
