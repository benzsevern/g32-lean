import HodgeLean.Adapters.KleimanProductProofs

/-!
# Kleiman products and cycle-class multiplication (FROZEN SPEC)

This specification gives the implication from general translated intersections on smooth
projective complex commutative group varieties to multiplication of rational cycle classes.
It also packages the resulting restriction to the Pohlmann--Weil cup algebra.
HC no distance; AV milestone no distance.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint TopologicalSpace
open AlgebraicTopology.Singular HodgeLean.RealDefs
open scoped ContDiff Manifold

namespace HodgeLean.Adapters

/-- On an open where a holomorphic map `f` to `ℂ^p` cuts out the analytic support of a
codimension-`p` prime and is a submersion along it, the restricted supported prime class is the
pullback along `f` of the normalized class of `(ℂ^p, ℂ^p \ {0})`.
Source: Bott--Tu, *Differential Forms in Algebraic Topology*, §6, Thom classes in normal
coordinates; Griffiths--Harris, *Principles of Algebraic Geometry*, chapter 0 §4, complex
orientation; Fulton, *Intersection Theory*, second edition, §19.1. -/
alias hc9k_prime_supportedClass_chart := hc9k_prime_supportedClass_chart_aux

example := hc9k_prime_supportedClass_chart

/-- Non-vacuity of the prime chart premises: on the complex point, the unique prime has
codimension zero and the empty coordinate map on the whole space satisfies all three of them.
Source: `ccm16_point`; `contMDiff_const`. -/
example : ∀ z : ccm16_point.left, Order.coheight z = 0 ∧
    (∀ u : (⊤ : Opens (ComplexPoint ccm16_point)),
      (ContinuousMap.const _ (0 : Fin 0 → ℂ)) u = 0 ↔
        u.1 ∈ cycleComponentAnalyticClosedSupport ccm16_point z) ∧
    ContMDiff 𝓘(ℂ, Fin 0 → ℂ) 𝓘(ℂ, Fin 0 → ℂ) ω
      (ContinuousMap.const (⊤ : Opens (ComplexPoint ccm16_point)) (0 : Fin 0 → ℂ)) ∧
    (∀ u : (⊤ : Opens (ComplexPoint ccm16_point)),
      Function.Surjective (mfderiv 𝓘(ℂ, Fin 0 → ℂ) 𝓘(ℂ, Fin 0 → ℂ)
        (ContinuousMap.const (⊤ : Opens (ComplexPoint ccm16_point)) (0 : Fin 0 → ℂ)) u)) := by
  intro z
  have : Subsingleton ccm16_point.left := inferInstanceAs (Subsingleton (PrimeSpectrum ℂ))
  refine ⟨Order.coheight_eq_zero.mpr fun b _ => (Subsingleton.elim b z).le, fun u => ?_,
    contMDiff_const, fun _ _ => ⟨0, Subsingleton.elim (α := Fin 0 → ℂ) _ _⟩⟩
  refine iff_of_true rfl ?_
  change Point.underlying u.1 ∈ closure {z}
  rw [Subsingleton.elim (Point.underlying u.1) z]
  exact subset_closure rfl

/-- The constant normal map `1` no longer satisfies the prime chart premises unless the open
misses the support, so the constant-map instance of the earlier statement is excluded.
Source: `one_ne_zero`. -/
example (M : Type) [TopologicalSpace M] (U : Opens M) (S : Set M) (p : ℕ) (hp : 0 < p)
    (hzero : ∀ u : U, (ContinuousMap.const U (1 : Fin p → ℂ)) u = 0 ↔ u.1 ∈ S) :
    ∀ u : U, u.1 ∉ S := fun u hu =>
  one_ne_zero (congrFun ((hzero u).mpr hu) ⟨0, hp⟩)

/-- On an open where holomorphic normal charts `f` for `x` and `h` for `y` are submersions along
their supports, where the zeros of `(f, h)` are exactly the analytic support of one
codimension-`p + q` intersection component, and where `(f, h)` is itself a submersion at each of
those zeros, the restricted component class is the pullback along `(f, h)` of the normalized class
of `(ℂ^(p+q), ℂ^(p+q) \ {0})`. The statement carries weight one: under the transverse
premises of the supported intersection product the local length is one by
`hc9k_transverse_generic_length_one`. The identity "local degree = length" for a general
pair `(f, h)` is not stated here; with `f = z₁` and `h = z₁ - z₂²` on a surface the length is
two and `(f, h)` is nowhere a submersion.
Source: SGA 1, Exposé XII, Proposition 3.1; Bott--Tu, *Differential Forms in Algebraic Topology*,
§6, Thom classes in normal coordinates and products of Thom classes; Fulton, *Intersection
Theory*, second edition, §19.2. -/
alias hc9k_intersection_supportedClass_chart :=
  hc9k_intersection_supportedClass_chart_aux

example := hc9k_intersection_supportedClass_chart

/-- On the empty open the intersection chart identity holds outright: both sides lie in the
same zero group.
Source: `neighborhoodSupportRelativeCohomology_subsingleton`. -/
example (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    (p q : ℕ) (x y : X.left)
    (w : (ccm3_primeIdeal X.left x ⊔ ccm3_primeIdeal X.left y).subscheme)
    (hwcodim : Order.coheight ((ccm3_primeIdeal X.left x ⊔
      ccm3_primeIdeal X.left y).subschemeι w) = p + q)
    (f : C((⊥ : Opens (ComplexPoint X)), Fin p → ℂ))
    (h : C((⊥ : Opens (ComplexPoint X)), Fin q → ℂ))
    (hzero : ∀ u : (⊥ : Opens (ComplexPoint X)), hc9k_appendCoordinates f h u = 0 ↔
      u.1 ∈ cycleComponentAnalyticClosedSupport X
        ((ccm3_primeIdeal X.left x ⊔ ccm3_primeIdeal X.left y).subschemeι w)) :
    relativeCohomologyMap ℚ (2 * (p + q))
        (neighborhoodSupportInclusionPairMap
          (show ((⊥ : Opens (ComplexPoint X)) : Set (ComplexPoint X)) ⊆
            (⊤ : Opens (ComplexPoint X)) from le_top)
          (cycleComponentAnalyticClosedSupport X
            ((ccm3_primeIdeal X.left x ⊔ ccm3_primeIdeal X.left y).subschemeι w) :
              Set (ComplexPoint X)))
        (supportedSingularClass X
          (cycleComponentAnalyticClosedSupport X
            ((ccm3_primeIdeal X.left x ⊔ ccm3_primeIdeal X.left y).subschemeι w))
          (2 * (p + q))
          (cycleComponentSupportedInjectiveClass X
            ((ccm3_primeIdeal X.left x ⊔ ccm3_primeIdeal X.left y).subschemeι w)
            hwcodim)) =
      relativeCohomologyMap ℚ (2 * (p + q))
        (hc9k_normalCoordinatePair ⊥
          (cycleComponentAnalyticClosedSupport X
            ((ccm3_primeIdeal X.left x ⊔ ccm3_primeIdeal X.left y).subschemeι w))
          (p + q) (hc9k_appendCoordinates f h) (fun u => (hzero u).mp))
        (normalizedPointCoclass (p + q)) :=
  have := neighborhoodSupportRelativeCohomology_subsingleton (TopCat.of (ComplexPoint X))
    (cycleComponentAnalyticClosedSupport X
      ((ccm3_primeIdeal X.left x ⊔ ccm3_primeIdeal X.left y).subschemeι w) :
        Set (ComplexPoint X)) (2 * (p + q))
    ((⊥ : Opens (ComplexPoint X)) : Set (ComplexPoint X)) (fun _ hz => hz.elim)
  Subsingleton.elim _ _

/-- The pair-submersion premise is not vacuous: on `ℂ^0` the empty pair is a submersion at
every point.
Source: `Fin.elim0`. -/
example (M : Type) [TopologicalSpace M] [ChartedSpace (Fin 0 → ℂ) M]
    (g : M → Fin (0 + 0) → ℂ) (u : M) :
    Function.Surjective (mfderiv 𝓘(ℂ, Fin 0 → ℂ) 𝓘(ℂ, Fin (0 + 0) → ℂ) g u) :=
  fun _ => ⟨0, funext fun i => Fin.elim0 i⟩

/-- At a point of one intersection component that avoids both singular loci and every other
component, holomorphic normal charts for both primes exist on a common open, and the zeros of
the pair are exactly that component there.
Source: Griffiths--Harris, *Principles of Algebraic Geometry*, chapter 0 §2, the holomorphic
implicit function theorem; Grothendieck, SGA 1, Exposé XII, Proposition 3.1, smoothness of the
analytification; Hartshorne, *Algebraic Geometry*, I, Proposition 1.5, finiteness of irreducible
components. -/
alias hc9k_exists_transverse_chart := hc9k_exists_transverse_chart_aux

example := hc9k_exists_transverse_chart

/-- At a point of a component of the translated intersection with `t` in the transverse locus,
where the point avoids the singular loci of both primes and of the component, the pair `(f, h)`
of holomorphic normal charts is a submersion. The intersection scheme is smooth there of
dimension `dim X - (p + q)` and is cut out by the ideals of the two primes, so its étale
coordinates together with `(f, h)` detect every tangent vector.
Source: Kleiman, Compositio Math. 28 (1974), Theorem 2; Hartshorne, *Algebraic Geometry*,
I, Theorem 5.1 (Jacobian criterion) and III, Proposition 10.4; SGA 1, Exposé XII,
Proposition 3.1; Stacks Project, Tag 02GU (étale maps are unramified). -/
alias hc9k_transverse_chart_submersion := hc9k_transverse_chart_submersion_aux

example := hc9k_transverse_chart_submersion

/-- Degree `2 * p` supported classes on a finite union of pure codimension-`p` components are
determined by one germ on each component away from the component boundary.
Source: Bredon, *Sheaf Theory*, II.9 and VI.9, localization with supports; Bott--Tu, §6,
the Thom isomorphism. -/
alias hc9k_supportedClass_eq_of_generic_germs :=
  hc9k_supportedClass_eq_of_generic_germs_aux

example := hc9k_supportedClass_eq_of_generic_germs

/-- On `ℂ^(p+q)`, the relative cup of the normal classes of the first `p` and the last `q`
coordinates is the normalized class of their common zero, the origin, with coefficient `+1`.
For `p = 1` this is `ccm17_coordinate_product`.
Source: Bott--Tu, *Differential Forms in Algebraic Topology*, §6, Thom classes of direct sums;
Bredon, *Sheaf Theory*, V, orientation and duality; Griffiths--Harris, *Principles of
Algebraic Geometry*, chapter 0 §4, complex orientation. -/
alias hc9k_coordinate_product_general := hc9k_coordinate_product_general_aux

example := hc9k_coordinate_product_general

/-- The general coordinate intersection class is nonzero, here for `p = 2` and `q = 1`, so the
general coordinate product is not an identity in a zero group.
Source: `normalizedRelativeCoclass_pairing_self`; `standardComplexLocalClass_ne_zero_for_chart`. -/
example : hc9k_coordinateIntersectionClass 2 1 ≠ 0 := by
  have hn : normalizedPointCoclass 3 ≠ 0 := by
    intro h
    have he := normalizedRelativeCoclass_pairing_self (standardComplexLocalClass ℚ 3)
      (standardComplexLocalClass_ne_zero_for_chart 3)
    change relativeCohomologyEquivDualHomology ℚ (puncturedPair ℂ 3) 6
      (normalizedPointCoclass 3) (standardComplexLocalClass ℚ 3) = 1 at he
    rw [h, map_zero, LinearMap.zero_apply] at he
    exact zero_ne_one he
  intro h
  apply hn
  let e : TopPair.ofSubset (X := TopCat.of (Fin (2 + 1) → ℂ))
      ((ccm17_zeroSupport (TopCat.of (Fin (2 + 1) → ℂ)) 2 (hc9k_coordinateHead 2 1) ⊓
        ccm17_zeroSupport (TopCat.of (Fin (2 + 1) → ℂ)) 1 (hc9k_coordinateTail 2 1)) :
          Set _)ᶜ ≅ puncturedPair ℂ (2 + 1) :=
    TopPair.isoOfSubset (Homeomorph.refl _)
      (fun z => not_congr (hc9k_coordinate_intersection_zero 2 1 z).symm)
  have hm : hc9k_coordinateIntersectionPair 2 1 = e.hom := rfl
  change relativeCohomologyMap ℚ 6 (hc9k_coordinateIntersectionPair 2 1)
    (normalizedPointCoclass 3) = 0 at h
  have hh := congrArg (relativeCohomologyMap ℚ 6 e.inv) h
  rw [hm, map_zero, ← LinearMap.comp_apply, ← relativeCohomologyMap_comp,
    Iso.inv_hom_id, relativeCohomologyMap_id] at hh
  exact hh

/-- At `p = q = 0` the general coordinate product is an identity between degree-zero classes of
the point `ℂ^0`, whose coordinate intersection is the whole point.
Source: `hc9k_coordinate_intersection_zero`. -/
example : (0 : Fin (0 + 0) → ℂ) ∈
    (ccm17_zeroSupport (TopCat.of (Fin (0 + 0) → ℂ)) 0 (hc9k_coordinateHead 0 0) ⊓
      ccm17_zeroSupport (TopCat.of (Fin (0 + 0) → ℂ)) 0 (hc9k_coordinateTail 0 0)) :=
  (hc9k_coordinate_intersection_zero 0 0 0).mpr rfl

/-- After a translate in the transverse locus whose intersection components all have generic
points off both singular filtrations, the supported cup of the two prime classes is the
local-length-weighted sum of the supported classes of the intersection components.
Source: Fulton, *Intersection Theory*, second edition, Proposition 7.1, §§8.2 and 19.1;
Bott--Tu, §6. -/
alias hc9k_supported_intersection_product := hc9k_supported_intersection_product_aux

example := hc9k_supported_intersection_product

/-- Forgetting support from the weighted component sum gives the rational cycle class of the
scheme-theoretic prime intersection.
Source: Fulton, *Intersection Theory*, second edition, §§1.5 and 19.1. -/
alias hc9k_forget_supported_intersectionCycle :=
  hc9k_forget_supported_intersectionCycle_aux

example := hc9k_forget_supported_intersectionCycle

/-- A transverse generic local intersection has multiplicity one.
Source: Fulton, *Intersection Theory*, second edition, §§7.1 and 8.2; Stacks Project,
Tags 00NN and 0B01. -/
alias hc9k_transverse_generic_length_one := hc9k_transverse_generic_length_one_aux

example := hc9k_transverse_generic_length_one

/-- The cycle class of a transverse prime intersection is the cup product of the two prime
cycle classes, with codimension recorded as `p + q`.
Source: Fulton, *Intersection Theory*, second edition, §8.2 and Corollary 19.2; Bott--Tu,
§6, products of Thom classes. -/
alias hc9k_prime_intersection_cycleClass := hc9k_prime_intersection_cycleClass_aux

example := hc9k_prime_intersection_cycleClass

/-- Summing the prime-component identities gives the class of the bilinear intersection cycle.
Source: Fulton, *Intersection Theory*, second edition, §§1.3, 8.1, and 19.1. -/
alias hc9k_local_to_global_cycleClass := hc9k_local_to_global_cycleClass_aux

example := hc9k_local_to_global_cycleClass

/-- Translation invariance replaces the class of the translated second cycle by its original
class inside the cup product.
Source: Fulton, *Intersection Theory*, second edition, §§1.7 and 19.1; Kleiman,
Compositio Math. 28 (1974), §1. -/
alias hc9k_translation_replaces_second_class := hc9k_translation_replaces_second_class_aux

example := hc9k_translation_replaces_second_class

/-- Cup products of classes represented by rational pure-codimension cycles lie in the
algebraic cycle-class span in the summed codimension.
Source: Fulton, *Intersection Theory*, second edition, §8.3 and Corollary 19.2. -/
alias hc9k_rational_cycles_multiply := hc9k_rational_cycles_multiply_aux

example := hc9k_rational_cycles_multiply

/-- Cycle classes multiply on every smooth projective complex commutative group variety.
Source: Fulton, *Intersection Theory*, second edition, Corollary 19.2; Kleiman,
Compositio Math. 28 (1974), Theorem 2. -/
alias hc9k_cycleClassMultiplicative := hc9k_cycleClassMultiplicative_aux

example := hc9k_cycleClassMultiplicative

/-- Algebraic classes in the pulled-Weil cup algebra multiply to algebraic classes.
Source: Pohlmann--Weil, Theorem 4.2, conclusion; Fulton, *Intersection Theory*, second edition,
Corollary 19.2. -/
alias hc9k_papw_PWCupClosed := hc9k_papw_PWCupClosed_aux

example := hc9k_papw_PWCupClosed

end HodgeLean.Adapters
