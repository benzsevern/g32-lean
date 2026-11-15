import HodgeLean.Foundations.QuotientDuality.ProperCycleSingletonOrientation

/-! # Actual global complex classes on singleton spaces -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicTopology.Singular
namespace HodgeLean.Foundations.QuotientDuality

/-- On an actual singleton space the global-to-local homology projection is bijective in every degree.
Source: Hatcher, Algebraic Topology, section 2.1, relative homology with empty subspace.
HC no distance; AV milestone no distance. -/
lemma properCycle_subsingleton_local_orientation_bijective
    (X : TopCat.{0}) [Subsingleton X] (x : X) (n : ℕ) :
    Function.Bijective (fun c : Homology ℚ X n => localOrientation X n c x) := by
  have hempty : ({x} : Set X)ᶜ = ∅ := by
    ext y
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff, Set.mem_empty_iff_false, iff_false]
    exact not_not.mpr (Subsingleton.elim y x)
  change Function.Bijective (relativeHomologyProjection ℚ (pointComplementPair x) n).hom
  have hp : pointComplementPair x = emptySubspacePair X := by
    change TopPair.ofSubset (X := X) ({x} : Set X)ᶜ = TopPair.ofSubset (X := X) ∅
    rw [hempty]
  rw [hp]
  exact (homologyEmptySubspaceIso ℚ X n).toLinearEquiv.bijective

/-- A singleton has a unique global degree-zero class with the original complex normalization in every chart, and that class spans its homology.
Source: Hatcher, Algebraic Topology, sections 2.1 and 3.3, point homology and chart normalization.
HC no distance; AV milestone no distance. -/
lemma properCycle_singleton_complex_class
    (X : TopCat.{0}) [Unique X] :
    ∃! c : Homology ℚ X 0,
      (∀ (e : OpenPartialHomeomorph X (Fin 0 → ℂ)) (x : X) (hx : x ∈ e.source),
        localOrientation X 0 c x = localClassOfChart 0 e x hx) ∧
      Function.Bijective (LinearMap.toSpanSingleton ℚ (Homology ℚ X 0) c) := by
  letI : Unique (Fin 0 → ℂ) := { default := 0, uniq := fun _ => Subsingleton.elim _ _ }
  let e : OpenPartialHomeomorph X (Fin 0 → ℂ) :=
    (Homeomorph.homeomorphOfUnique _ _).toOpenPartialHomeomorph
  let x : X := default
  have hx : x ∈ e.source := Set.mem_univ _
  let P := (relativeHomologyProjection ℚ (pointComplementPair x) 0).hom
  have hP : Function.Bijective P := properCycle_subsingleton_local_orientation_bijective X x 0
  obtain ⟨c, hc⟩ := hP.surjective (localClassOfChart 0 e x hx)
  have hc0 : c ≠ 0 := by
    intro hz
    have h := hc
    rw [hz, map_zero] at h
    exact localClassOfChart_ne_zero 0 e x hx h.symm
  have hnorm : ∀ (f : OpenPartialHomeomorph X (Fin 0 → ℂ)) (y : X) (hy : y ∈ f.source),
      localOrientation X 0 c y = localClassOfChart 0 f y hy := by
    intro f y hy
    have hyx : y = x := Subsingleton.elim _ _
    subst y
    have hm : chartModelEmbeddingPair 0 e x hx = chartModelEmbeddingPair 0 f x hy := by
      apply MorphismProperty.Arrow.Hom.ext
      · ext z : 1
        apply Subtype.ext
        exact (inferInstance : Subsingleton X).elim _ _
      · ext z : 1
        exact (inferInstance : Subsingleton X).elim _ _
    exact hc.trans (congrArg (fun g => relativeHomologyMap ℚ 0 g
      (standardComplexLocalClass ℚ 0)) hm)
  refine ⟨c, ⟨hnorm, ?_⟩, ?_⟩
  · constructor
    · intro q r h
      exact smul_left_injective ℚ hc0 h
    · intro b
      have hs := span_localClassOfChart_eq_top 0 e x hx
      obtain ⟨q, hq⟩ := Submodule.mem_span_singleton.mp
        (show P b ∈ Submodule.span ℚ {localClassOfChart 0 e x hx} by
          rw [hs]
          exact Submodule.mem_top)
      refine ⟨q, hP.injective ?_⟩
      change P (q • c) = P b
      rw [map_smul, hc]
      exact hq
  · intro b hb
    exact hP.injective ((hb.1 e x hx).trans hc.symm)

end HodgeLean.Foundations.QuotientDuality
