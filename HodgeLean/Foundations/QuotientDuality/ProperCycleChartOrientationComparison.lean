import HodgeLean.Foundations.QuotientDuality.ProperCycleComplexLocalCapLinearity
import HodgeLean.RealDefs.Port.AlgebraicTopology.LocalHomology.ChartPointClassNormalization

/-! # Original compressed chart orientations in actual global coordinates -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicTopology AlgebraicTopology.Singular
namespace HodgeLean.Foundations.QuotientDuality

/-- The original compressed chart class of an actual global coordinate homeomorphism is exactly its inverse transport of the translated original standard complex class.
Source: Hatcher, Algebraic Topology, section 3.3; chartTargetPointPairMap_localClass, original point-neighborhood normalization.
HC no distance; AV milestone no distance. -/
lemma properCycle_homeomorph_chart_local_class
    (d : ℕ) {M : TopCat.{0}} (e : M ≃ₜ (Fin d → ℂ)) (x : M) :
    relativeHomologyMap ℚ (2 * d)
      (TopPair.isoOfSubset (X := M) (Y := TopCat.of (Fin d → ℂ)) (A := ({x} : Set M)ᶜ) (B := ({e x} : Set (Fin d → ℂ))ᶜ)
        e (fun _ => not_congr e.injective.eq_iff)).inv
      (relativeHomologyMap ℚ (2 * d) (translationPointComplementPairMap (Fin d → ℂ) (e x))
        (standardComplexLocalClass ℚ d)) =
      localClassOfChart d e.toOpenPartialHomeomorph x (by trivial) := by
  let e' := e.toOpenPartialHomeomorph
  let eP := TopPair.isoOfSubset (X := M) (Y := TopCat.of (Fin d → ℂ)) (A := ({x} : Set M)ᶜ) (B := ({e x} : Set (Fin d → ℂ))ᶜ)
    e (fun _ => not_congr e.injective.eq_iff)
  let j : pointComplementPair (e x) ≅ neighborhoodPointComplementPair e'.target (e' x) :=
    TopPair.isoOfSubset (Homeomorph.Set.univ (Fin d → ℂ)).symm (fun _ => Iff.rfl)
  let T := translationPointComplementPairMap (Fin d → ℂ) (e x)
  let P := T ≫ j.hom
  have hp : P ≫ neighborhoodPointComplementPairMap e'.target (e' x) = T := by
    ext z : 2 <;> rfl
  have hi : j.hom ≫ chartTargetInverseAtSourcePairMap d e' x = eP.inv := by
    ext z : 2 <;> rfl
  have h := chartTargetPointPairMap_localClass d e' x (by trivial) P
    (by rw [hp]; rfl)
  have hc : P ≫ chartTargetInverseAtSourcePairMap d e' x = T ≫ eP.inv := by
    dsimp only [P]
    rw [Category.assoc, hi]
  rw [hc, relativeHomologyMap_comp, LinearMap.comp_apply] at h
  exact h

/-- Zero translation is the actual identity of the original standard point-complement pair.
Source: Hatcher, Algebraic Topology, section 2.1, maps of point-complement pairs.
HC no distance; AV milestone no distance. -/
lemma properCycle_translation_point_pair_zero (d : ℕ) :
    translationPointComplementPairMap (Fin d → ℂ) 0 = 𝟙 (pointComplementPair (0 : Fin d → ℂ)) := by
  apply MorphismProperty.Arrow.Hom.ext
  · ext z
    apply Subtype.ext
    exact add_zero z.1
  · ext z
    exact add_zero (show Fin d → ℂ from z)

/-- At an actual zero coordinate the original compressed chart class is exactly inverse transport of the original standard class, without translating its point pair.
Source: Hatcher, Algebraic Topology, section 3.3; chartTargetPointPairMap_localClass, original point-neighborhood normalization.
HC no distance; AV milestone no distance. -/
lemma properCycle_homeomorph_zero_chart_local_class
    (d : ℕ) {M : TopCat.{0}} (e : M ≃ₜ (Fin d → ℂ)) (x : M) (he : e x = 0) :
    let eP : pointComplementPair x ≅ puncturedPair ℂ d :=
      TopPair.isoOfSubset e (by
        intro z
        change (e z ≠ 0) ↔ z ≠ x
        apply not_congr
        rw [← he]
        exact e.injective.eq_iff)
    relativeHomologyMap ℚ (2 * d) eP.inv (standardComplexLocalClass ℚ d) =
      localClassOfChart d e.toOpenPartialHomeomorph x (by trivial) := by
  dsimp only
  let e' := e.toOpenPartialHomeomorph
  let eP : pointComplementPair x ≅ puncturedPair ℂ d :=
    TopPair.isoOfSubset e (by
      intro z
      change (e z ≠ 0) ↔ z ≠ x
      apply not_congr
      rw [← he]
      exact e.injective.eq_iff)
  let j : pointComplementPair (e x) ≅ neighborhoodPointComplementPair e'.target (e' x) :=
    TopPair.isoOfSubset (Homeomorph.Set.univ (Fin d → ℂ)).symm (fun _ => Iff.rfl)
  let T := translationPointComplementPairMap (Fin d → ℂ) (e x)
  let P := T ≫ j.hom
  have hp : P ≫ neighborhoodPointComplementPairMap e'.target (e' x) = T := by ext z : 2 <;> rfl
  have hc : P ≫ chartTargetInverseAtSourcePairMap d e' x = eP.inv := by
    apply MorphismProperty.Arrow.Hom.ext
    · ext z
      apply Subtype.ext
      change e.symm (z.1 + e x) = e.symm z.1
      rw [he, add_zero]
    · ext z
      change e.symm ((show Fin d → ℂ from z) + e x) = e.symm z
      rw [he, add_zero]
  have h := chartTargetPointPairMap_localClass d e' x (by trivial) P (by rw [hp]; rfl)
  rw [hc] at h
  exact h

/-- Identifying the image point of an actual homeomorphism gives the literal point-pair homology isomorphism, including its dependent basepoint transport.
Source: Hatcher, Algebraic Topology, section 2.1, functorial point-complement pairs.
HC no distance; AV milestone no distance. -/
lemma properCycle_local_homeomorph_point_identification
    {X Y : TopCat.{0}} (e : X ≃ₜ Y) (x : X) (y : Y) (he : e x = y) (n : ℕ) :
    Eq.mp (congrArg (fun z : Y => orientationGroup X n x ≅ orientationGroup Y n z) he)
        (properCycle_local_homology_homeomorph_iso e x n) =
      (HomologicalComplex.homologyFunctor (ModuleCat.{0} ℚ) (ComplexShape.down ℕ) n).mapIso
        ((relativeChainFunctor ℚ).mapIso
          (TopPair.isoOfSubset (X := X) (Y := Y) (A := ({x} : Set X)ᶜ) (B := ({y} : Set Y)ᶜ) e (by
            intro z
            change (e z ≠ y) ↔ z ≠ x
            apply not_congr
            rw [← he]
            exact e.injective.eq_iff))) := by
  subst y
  rfl

/-- The actual complex product orientation used by the original normal cap is exactly the original compressed chart class in its specified complex linear coordinates.
Source: Hatcher, Algebraic Topology, section 3.3; chartTargetPointPairMap_localClass, original chart normalization.
HC no distance; AV milestone no distance. -/
lemma properCycle_complex_product_orientation_chart_class (r d : ℕ) :
    let L : ((Fin r → ℂ) × (Fin d → ℂ)) ≃L[ℂ] (Fin (r + d) → ℂ) :=
      ContinuousLinearEquiv.ofFinrankEq
        (by simp only [Module.finrank_prod, Module.finrank_pi, Fintype.card_fin])
    properCycle_complex_product_standard_orientation r d =
      localClassOfChart (r + d) L.toHomeomorph.toOpenPartialHomeomorph (0, 0) (by trivial) := by
  dsimp only
  let L : ((Fin r → ℂ) × (Fin d → ℂ)) ≃L[ℂ] (Fin (r + d) → ℂ) :=
    ContinuousLinearEquiv.ofFinrankEq
      (by simp only [Module.finrank_prod, Module.finrank_pi, Fintype.card_fin])
  have h0 : L.toHomeomorph (0, 0) = 0 := map_zero L
  unfold properCycle_complex_product_standard_orientation properCycle_complex_product_standard_orientation_iso
  rw [properCycle_local_homeomorph_point_identification
    (X := TopCat.of ((Fin r → ℂ) × (Fin d → ℂ))) (Y := TopCat.of (Fin (r + d) → ℂ))
    L.toHomeomorph (0, 0) 0 h0]
  exact properCycle_homeomorph_zero_chart_local_class (r + d)
    (M := TopCat.of ((Fin r → ℂ) × (Fin d → ℂ))) L.toHomeomorph (0, 0) h0

/-- The original compressed complex chart orientation has the checked local cap multiplicity formula with the actual nonzero model scalar.
Source: Fulton, Intersection Theory, section 19.1; Hatcher, Algebraic Topology, section 3.3, local cap normalization.
HC no distance; AV milestone no distance. -/
lemma properCycle_complex_chart_cap_multiplicity (r d : ℕ) (m : ℚ) :
    let L : ((Fin r → ℂ) × (Fin d → ℂ)) ≃L[ℂ] (Fin (r + d) → ℂ) :=
      ContinuousLinearEquiv.ofFinrankEq
        (by simp only [Module.finrank_prod, Module.finrank_pi, Fintype.card_fin])
    properCycle_complex_product_local_cap r d
      (m • relativeCohomologyMap ℚ (2 * d)
        (properCycle_product_support_projection (Fin r → ℂ) (TopCat.of (Fin d → ℂ)) {0})
        (normalizedRelativeCoclass (standardComplexLocalClass ℚ d)
          (standardComplexLocalClass_ne_zero_for_chart d)))
      (localClassOfChart (r + d) L.toHomeomorph.toOpenPartialHomeomorph (0, 0) (by trivial)) =
        (m * properCycle_standard_complex_cap_scalar r d) • standardComplexLocalClass ℚ r := by
  dsimp only
  rw [← properCycle_complex_product_orientation_chart_class r d]
  exact properCycle_complex_product_local_cap_multiplicity r d m

end HodgeLean.Foundations.QuotientDuality
