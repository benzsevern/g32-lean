import HodgeLean.Adapters.CycleClassSmoothChartsProofs

/-! # Smooth morphisms in complex charts

An implication from algebraic smoothness to analytic derivative surjectivity,
via an anchored étale-local section and étale derivative invertibility.
Finite component supports are separated on the explicit boundary complement;
boundary vanishing and restriction are implications from distinctness and coheight.
The geometric and disjoint-support obligations remain open.
The supported-prime comparison is frozen as an open geometric obligation.
HC no distance; AV milestone no distance.
-/

noncomputable section
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open HodgeLean.RealDefs AlgebraicTopology.Singular TopologicalSpace
namespace HodgeLean.Adapters

/-- Étale maps have invertible derivatives in the existing complex charts.
Source: complex inverse function theorem applied to an étale presentation;
`AlgebraicGeometry.LocalEtaleCoordinates`. -/
theorem ccm5_etale_chart_derivative_bijective
    (X Z : Over (Spec ↧ℂ)) (f : X ⟶ Z) (d e : ℕ)
    [SmoothOfRelativeDimension d X.hom] [SmoothOfRelativeDimension e Z.hom]
    [Etale f.left] (z : ComplexPoint X) :
    Function.Bijective (fderiv ℂ (inclusionInComplexCharts Z X f d e z)
      (localChart X d z z)) :=
  ccm5_etale_chart_derivative_bijective_aux X Z f d e z

/-- A smooth morphism has an étale-local section through each given complex point.
Source: Stacks Project, Lemma 37.38.5 (Slicing smooth morphisms),
https://stacks.math.columbia.edu/tag/055S. -/
theorem ccm5_smooth_etale_local_section
    (X Z : Over (Spec ↧ℂ)) (f : X ⟶ Z) (e : ℕ)
    [SmoothOfRelativeDimension e Z.hom] [Smooth f.left] (z : ComplexPoint X) :
    ∃ (W : Over (Spec ↧ℂ)) (s : W ⟶ X) (t : W ⟶ Z)
      (_ : SmoothOfRelativeDimension e W.hom) (w : ComplexPoint W),
      Etale t.left ∧ s ≫ f = t ∧ Point.map s w = z :=
  ccm5_smooth_etale_local_section_aux X Z f e z

/-- Chain rule in the existing absolute charts.
Source: `HasFDerivAt.comp` and the chart inverse identities. -/
theorem ccm5_chart_derivative_comp
    (X Y Z : Over (Spec ↧ℂ)) (f : X ⟶ Y) (g : Y ⟶ Z)
    (d e k : ℕ) [SmoothOfRelativeDimension d X.hom]
    [SmoothOfRelativeDimension e Y.hom] [SmoothOfRelativeDimension k Z.hom]
    (z : ComplexPoint X) :
    (fderiv ℂ (inclusionInComplexCharts Z Y g e k (Point.map f z))
      (localChart Y e (Point.map f z) (Point.map f z))).comp
      (fderiv ℂ (inclusionInComplexCharts Y X f d e z) (localChart X d z z)) =
    fderiv ℂ (inclusionInComplexCharts Z X (f ≫ g) d k z) (localChart X d z z) :=
  ccm5_chart_derivative_comp_aux X Y Z f g d e k z

/-- Algebraic smoothness implies surjectivity of the analytic chart derivative.
Source: the étale-local section, the étale inverse function theorem, and the chain rule. -/
theorem ccm5_smooth_chart_derivative_surjective
    (X Z : Over (Spec ↧ℂ)) (f : X ⟶ Z) (d e : ℕ)
    [SmoothOfRelativeDimension d X.hom] [SmoothOfRelativeDimension e Z.hom]
    [Smooth f.left] (z : ComplexPoint X) :
    Function.Surjective (fderiv ℂ (inclusionInComplexCharts Z X f d e z)
      (localChart X d z z)) :=
  ccm5_smooth_chart_derivative_surjective_aux X Z f d e z

/-- Finite disjoint closed supports split supported cohomology in every degree
under the canonical sum of enlargement maps.
Source: Bredon, *Sheaf Theory*, second edition, Chapter II, cohomology with supports. -/
theorem ccm5_disjoint_supportSum_bijective
    (T : TopCat.{0}) (F : TopCat.Sheaf AddCommGrpCat T)
    (r : ℕ) (S : Fin r → TopologicalSpace.Closeds T)
    (hS : Pairwise (fun i j => Disjoint (S i) (S j))) (n : ℕ) :
    Function.Bijective (ccm5_supportSum T F r S n) :=
  ccm5_disjoint_supportSum_bijective_aux T F r S hS n

/-- The removed boundary has no supported cohomology below degree `2(q+1)`.
Source: stratified local support vanishing, extending
`cycleComponentSingularBoundaryRelH_isZero_of_lt` to the finite boundary union. -/
theorem ccm5_componentBoundary_vanishing
    (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    (r q : ℕ) (x : Fin r → X.left) (hx : Function.Injective x)
    (hc : ∀ i, Order.coheight (x i) = q) (n : ℕ) (hn : n < 2 * (q + 1)) :
    Subsingleton (TopCat.Sheaf.supportH (TopCat.of (ComplexPoint X))
      (ccm5_componentBoundary X r x)
      ((TopCat.Sheaf.constantFunctor (TopCat.of (ComplexPoint X))).obj
        (AddCommGrpCat.of ℚ)) n) :=
  ccm5_componentBoundary_vanishing_aux X r q x hx hc n hn

/-- Removing the boundary preserves the degree `2q` supported group of the union.
Source: the localization sequence and boundary vanishing in degrees `2q` and `2q+1`. -/
theorem ccm5_componentRestriction_bijective
    (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    (r q : ℕ) (x : Fin r → X.left) (hx : Function.Injective x)
    (hc : ∀ i, Order.coheight (x i) = q) :
    Function.Bijective (ccm5_componentRestriction X r x (2 * q)) :=
  ccm5_componentRestriction_bijective_aux X r q x hx hc

/-- The component sum on the good open is bijective in every degree.
Source: finite disjoint-support additivity after removing the defined boundary. -/
theorem ccm5_separated_supportSum_bijective
    (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    (r : ℕ) (x : Fin r → X.left) (n : ℕ) :
    Function.Bijective (ccm5_supportSum
      (TopCat.of (ccm5_componentBoundary X r x).compl)
      ((TopCat.Sheaf.constantFunctor
        (TopCat.of (ccm5_componentBoundary X r x).compl)).obj (AddCommGrpCat.of ℚ))
      r (ccm5_separatedComponentSupport X r x) n) :=
  ccm5_separated_supportSum_bijective_aux X r x n

/-- The complete inverse support is the union over every nonzero coefficient.
Source: inverse-image ideal support and generic points of irreducible components. -/
theorem ccm5_inverseAnalyticSupport_eq_component_union
    {X Z : Over (Spec ↧ℂ)}
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    [IsIntegral Z.left] [Smooth Z.hom] [IsProjective Z.hom]
    (f : X ⟶ Z) (x : Z.left) :
    (ccm4_inverseAnalyticSupport f (cycleComponentAnalyticClosedSupport Z x) :
        Set (ComplexPoint X)) =
      ⋃ z : {z : X.left // ccm3_flatPullbackPrime f.left x z ≠ 0},
        (cycleComponentAnalyticClosedSupport X z.1 : Set (ComplexPoint X)) :=
  ccm5_inverseAnalyticSupport_eq_component_union_aux f x


/-- The finite enumeration covers the entire inverse analytic support.
Source: generic-component support union and `ccm5_primeEnumeration`. -/
theorem ccm5_inverseAnalyticSupport_eq_enumerated_union
    {X Z : Over (Spec ↧ℂ)}
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    [IsIntegral Z.left] [Smooth Z.hom] [IsProjective Z.hom]
    (f : X ⟶ Z) (x : Z.left) :
    (ccm4_inverseAnalyticSupport f (cycleComponentAnalyticClosedSupport Z x) :
        Set (ComplexPoint X)) =
      ⋃ i, (cycleComponentAnalyticClosedSupport X
        (ccm5_primeEnumeration f x i).1 : Set (ComplexPoint X)) :=
  ccm5_inverseAnalyticSupport_eq_enumerated_union_aux f x

/-- Lowest-degree supported classes are detected off the component boundary.
Source: boundary localization, disjoint-support additivity and local purity. -/
theorem ccm5_primeGoodOpen_germs_injective
    {X Z : Over (Spec ↧ℂ)}
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    [IsIntegral Z.left] [Smooth Z.hom] [IsProjective Z.hom]
    (f : X ⟶ Z) [Smooth f.left] (q : ℕ) (x : Z.left)
    (hx : Order.coheight x = q) :
    Function.Injective (fun u => fun a : ccm5_primeGoodOpen f x =>
      ccm5_supportGerm X
        (ccm4_inverseAnalyticSupport f (cycleComponentAnalyticClosedSupport Z x))
        (2 * q) a.1 u) :=
  ccm5_primeGoodOpen_germs_injective_aux f q x hx

/-- Restriction preserves the germ at a point of the remaining open.
Source: `supportRelativeCohomologyGerm_restrict`. -/
theorem ccm5_supportGerm_restriction
    (X : Over (Spec ↧ℂ))
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    (S : Closeds (ComplexPoint X)) (U : Opens (ComplexPoint X))
    (n : ℕ) (a : ComplexPoint X) (ha : a ∈ U)
    (u : TopCat.Sheaf.supportH (TopCat.of (ComplexPoint X)) S
      ((TopCat.Sheaf.constantFunctor (TopCat.of (ComplexPoint X))).obj
        (AddCommGrpCat.of ℚ)) n) :
    supportRelativeCohomologyGerm (TopCat.of (ComplexPoint X))
      (S : Set (ComplexPoint X)) n U a ha
      (relativeCohomologyMap ℚ n
        (neighborhoodSupportInclusionPairMap (show (U : Set (ComplexPoint X)) ⊆
          (⊤ : Opens (ComplexPoint X)) from le_top) (S : Set (ComplexPoint X)))
        (supportedSingularClass X S n u)) = ccm5_supportGerm X S n a u :=
  ccm5_supportGerm_restriction_aux X S U n a ha u

/-- Support enlargement commutes with passage to the local relative class.
Source: `supportedSingularClass_restrict`. -/
theorem ccm5_supportGerm_enlarge
    (X : Over (Spec ↧ℂ))
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    {S T : Closeds (ComplexPoint X)} (h : S ≤ T) (n : ℕ) (a : ComplexPoint X)
    (u : TopCat.Sheaf.supportH (TopCat.of (ComplexPoint X)) S
      ((TopCat.Sheaf.constantFunctor (TopCat.of (ComplexPoint X))).obj
        (AddCommGrpCat.of ℚ)) n) :
    ccm5_supportGerm X T n a (supportEnlarge X h n u) =
      supportRelativeCohomologyGerm (TopCat.of (ComplexPoint X))
        (T : Set (ComplexPoint X)) n ⊤ a (by trivial)
        (relativeCohomologyMap ℚ n
          (neighborhoodSupportEnlargePairMap _ (SetLike.coe_subset_coe.mpr h))
          (supportedSingularClass X S n u)) :=
  ccm5_supportGerm_enlarge_aux X h n a u

/-- The extended component class has its normalized smooth coclass germ.
Source: component normalization and naturality of the supported singular comparison. -/
theorem ccm5_componentClass_normalized_germ
    (X : Over (Spec ↧ℂ))
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    (q : ℕ) (x : X.left) (hx : Order.coheight x = q)
    (a : ComplexPoint X) (ha : a ∈ cycleComponentSmoothSupportAmbientOpen X x) :
    ccm5_supportGerm X (cycleComponentAnalyticClosedSupport X x) (2 * q) a
      (cycleComponentSupportedInjectiveClass X x hx) =
      (supportRelativeCohomologySheaf (TopCat.of (ComplexPoint X))
        (cycleComponentSupport X x) (2 * q)).presheaf.germ
        (cycleComponentSmoothSupportAmbientOpen X x) a ha
        (cycleComponentSmoothSupportCoclassSection X x hx) :=
  ccm5_componentClass_normalized_germ_aux X q x hx a ha

/-- Smooth pullback preserves normalized component germs on the separated open.
Source: complex submersion charts, normal-projection coclass functoriality,
and generic length of a reduced smooth inverse-image component. -/
theorem ccm5_submersion_normalized_germ
    {X Z : Over (Spec ↧ℂ)}
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    [IsIntegral Z.left] [Smooth Z.hom] [IsProjective Z.hom]
    (f : X ⟶ Z) [Smooth f.left] (q : ℕ) (x : Z.left)
    (hx : Order.coheight x = q) (a : ccm5_primeGoodOpen f x) :
    ccm5_supportGerm X
      (ccm4_inverseAnalyticSupport f (cycleComponentAnalyticClosedSupport Z x))
      (2 * q) a.1
      (ccm4_supportedPullback f (cycleComponentAnalyticClosedSupport Z x) (2 * q)
        (cycleComponentSupportedInjectiveClass Z x hx)) =
      ∑ᶠ z : {z : X.left // ccm3_flatPullbackPrime f.left x z ≠ 0},
        ccm5_supportGerm X
          (ccm4_inverseAnalyticSupport f (cycleComponentAnalyticClosedSupport Z x))
          (2 * q) a.1
          (ccm3_flatPullbackPrime f.left x z.1 •
            supportEnlarge X (ccm4_flatPullbackPrime_support_le_aux f x z.1 z.2) (2 * q)
              (cycleComponentSupportedInjectiveClass X z.1
                (ccm3_flatPullbackPrime_codimension f q x hx z.1 z.2))) :=
  ccm5_submersion_normalized_germ_aux f q x hx a

/-- Supported pullback of a prime cycle with its actual generic-length coefficients.
Source: Fulton, *Intersection Theory*, second edition, §1.7; complex local orientations. -/
theorem ccm5_ccm4_supportedPullback_prime {X Z : Over (Spec ↧ℂ)}
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    [IsIntegral Z.left] [Smooth Z.hom] [IsProjective Z.hom]
    (f : X ⟶ Z) [Smooth f.left] (q : ℕ) (x : Z.left)
    (hx : Order.coheight x = q) :
    ccm4_supportedPullback f (cycleComponentAnalyticClosedSupport Z x) (2 * q)
        (cycleComponentSupportedInjectiveClass Z x hx) =
      ∑ᶠ z : {z : X.left // ccm3_flatPullbackPrime f.left x z ≠ 0},
        ccm3_flatPullbackPrime f.left x z.1 •
          supportEnlarge X (ccm4_flatPullbackPrime_support_le_aux f x z.1 z.2) (2 * q)
            (cycleComponentSupportedInjectiveClass X z.1
              (ccm3_flatPullbackPrime_codimension f q x hx z.1 z.2)) :=
  ccm5_ccm4_supportedPullback_prime_aux f q x hx

end HodgeLean.Adapters
