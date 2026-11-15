import HodgeLean.Foundations.QuotientDuality.ProperCycleIntrinsicImage
import HodgeLean.RealDefs.Port.AlgebraicTopology.LocalHomology.ChartFundamentalClassGenerator
import HodgeLean.Foundations.QuotientDuality.ProperCycleSupportCoordinates
import HodgeLean.Foundations.QuotientDuality.ProperCycleComponentEvaluation
import HodgeLean.Foundations.QuotientDuality.ProperCyclePartialChartCapChecks
import HodgeLean.Foundations.QuotientDuality.ProperCycleSingletonOrientation

/-! # Independent normalization and coefficient checks for the proper-cycle split

The affine degree calculation tests the coefficient comparison. The point model
checks intrinsic top-class normalization in dimension zero. The partial-chart
model has one complex tangential and one complex normal dimension.
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry AlgebraicTopology.Singular
open HodgeLean.Adapters HodgeLean.Foundations.Program
namespace HodgeLean.Foundations.QuotientDuality.ProperCycleSplitChecks

private abbrev point : Over (Spec ↧ℂ) := Over.mk (𝟙 (Spec ↧ℂ))
private instance splitPointUnique : Unique (ComplexPoint point) where
  default := 𝟙 point
  uniq f := by
    apply Over.OverMorphism.ext
    simpa using f.w
private instance splitPointSchemeIntegral : AlgebraicGeometry.IsIntegral point.left :=
  inferInstanceAs (AlgebraicGeometry.IsIntegral (Spec ↧ℂ))
private instance splitPointAnSubsingleton : Subsingleton (a3b4_an point.hom) :=
  inferInstanceAs (Subsingleton (ComplexPoint point))
private instance splitZeroCoordinatesUnique : Unique (Fin 0 → ℂ) :=
  { default := 0, uniq := fun _ => Subsingleton.elim _ _ }
private def pointChart : OpenPartialHomeomorph (ComplexPoint point) (Fin 0 → ℂ) :=
  (Homeomorph.homeomorphOfUnique _ _).toOpenPartialHomeomorph
private def pointLocal := localClassOfChart 0 pointChart (𝟙 point) (by trivial)
private lemma point_pair_empty : pointComplementPair (𝟙 point) =
    emptySubspacePair (a3b4_an point.hom) := by
  change TopPair.ofSubset (X := a3b4_an point.hom) ({𝟙 point} : Set (ComplexPoint point))ᶜ =
    TopPair.ofSubset (X := a3b4_an point.hom) ∅
  congr 1
  ext z
  simp only [Set.mem_compl_iff, Set.mem_singleton_iff, Set.mem_empty_iff_false, iff_false]
  exact not_not.mpr (Subsingleton.elim z (𝟙 point))
private def pointProjection := (relativeHomologyProjection ℚ (pointComplementPair (𝟙 point)) 0).hom
private lemma pointProjection_bijective : Function.Bijective pointProjection := by
  unfold pointProjection
  rw [point_pair_empty]
  exact (homologyEmptySubspaceIso ℚ (a3b4_an point.hom) 0).toLinearEquiv.bijective
private def pointGlobal : Homology ℚ (a3b4_an point.hom) 0 :=
  (LinearEquiv.ofBijective pointProjection pointProjection_bijective).symm pointLocal

private lemma pointLocal_ne_zero : pointLocal ≠ 0 :=
  localClassOfChart_ne_zero 0 pointChart (𝟙 point) (by trivial)

private lemma pointGlobal_normalization :
    localOrientation (a3b4_an point.hom) 0 pointGlobal (𝟙 point) = pointLocal :=
  (LinearEquiv.ofBijective pointProjection pointProjection_bijective).apply_symm_apply _

/-- The actual global point class retains the specified intrinsic compressed-chart normalization.
Source: Hatcher, Algebraic Topology, sections 2.1 and 3.3.
HC no distance; AV milestone no distance. -/
theorem intrinsic_extension_point_example :
    localOrientation (a3b4_an point.hom) 0 pointGlobal (𝟙 point) = pointLocal :=
  pointGlobal_normalization

example : localOrientation (a3b4_an point.hom) 0 pointGlobal (𝟙 point) = pointLocal :=
  intrinsic_extension_point_example

/-- Orientation reversal fails the intrinsic extension normalization on an actual projective point.
Source: Hatcher, Algebraic Topology, section 3.3.
HC no distance; AV milestone no distance. -/
theorem intrinsic_extension_orientation_falsification :
    localOrientation (a3b4_an point.hom) 0 (-pointGlobal) (𝟙 point) ≠ pointLocal := by
  intro h
  change pointProjection (-pointGlobal) = pointLocal at h
  have hn : -(pointProjection pointGlobal) = pointLocal :=
    (map_neg pointProjection pointGlobal).symm.trans h
  have hc : pointProjection pointGlobal = pointLocal := pointGlobal_normalization
  rw [hc] at hn
  have hz : (2 : ℚ) • pointLocal = 0 := by
    rw [show (2 : ℚ) = 1 + 1 by norm_num, add_smul, one_smul]
    exact neg_eq_iff_add_eq_zero.mp hn
  exact (smul_ne_zero (by norm_num : (2 : ℚ) ≠ 0) pointLocal_ne_zero) hz

example : localOrientation (a3b4_an point.hom) 0 (-pointGlobal) (𝟙 point) ≠ pointLocal :=
  intrinsic_extension_orientation_falsification

/-- The actual integral projective point used by the independent intrinsic normalization model.
Source: Hilbert's Nullstellensatz; the identity complex scheme.
HC no distance; AV milestone no distance. -/
abbrev intrinsicPoint : Over (Spec ↧ℂ) := point

example : intrinsicPoint.hom = 𝟙 (Spec ↧ℂ) := rfl

/-- The independently constructed global intrinsic point class, using actual point excision rather than an open existence statement.
Source: Hatcher, Algebraic Topology, sections 2.1 and 3.3.
HC no distance; AV milestone no distance. -/
def intrinsicPointClass : Homology ℚ (a3b4_an intrinsicPoint.hom) 0 := pointGlobal

example : localOrientation (a3b4_an intrinsicPoint.hom) 0 intrinsicPointClass
    (𝟙 intrinsicPoint) = pointLocal := pointGlobal_normalization

/-- The independent intrinsic point class is nonzero.
Source: Hatcher, Algebraic Topology, section 3.3, its prescribed local normalization.
HC no distance; AV milestone no distance. -/
theorem intrinsicPointClass_ne_zero : intrinsicPointClass ≠ 0 := by
  intro h
  apply pointLocal_ne_zero
  have hh := pointGlobal_normalization
  change pointProjection intrinsicPointClass = pointLocal at hh
  rw [h, map_zero] at hh
  exact hh.symm

example : intrinsicPointClass ≠ 0 := intrinsicPointClass_ne_zero

/-- The point model has the actual scheme dimension zero.
Source: the field spectrum dimension formula.
HC no distance; AV milestone no distance. -/
theorem intrinsicPoint_dimension : topologicalKrullDim intrinsicPoint.left = (0 : ℕ) := by
  change topologicalKrullDim (PrimeSpectrum ℂ) = 0
  rw [PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim, ringKrullDim_eq_zero_of_field]

example : topologicalKrullDim intrinsicPoint.left = (0 : ℕ) := intrinsicPoint_dimension

/-- Every original zero-dimensional chart gives the same specified intrinsic normalization on the point model.
Source: Hatcher, Algebraic Topology, section 3.3, the unique point-complement map in dimension zero.
HC no distance; AV milestone no distance. -/
theorem intrinsicPointClass_complex
    (e : OpenPartialHomeomorph (ComplexPoint intrinsicPoint) (Fin 0 → ℂ))
    (x : ComplexPoint intrinsicPoint) (hx : x ∈ e.source) :
    localOrientation (a3b4_an intrinsicPoint.hom) 0 intrinsicPointClass x =
      localClassOfChart 0 e x hx := by
  have hxp : x = 𝟙 point := (inferInstance : Subsingleton (ComplexPoint point)).elim _ _
  subst x
  rw [show localOrientation (a3b4_an intrinsicPoint.hom) 0 intrinsicPointClass (𝟙 point) =
    pointLocal from pointGlobal_normalization]
  have hm : chartModelEmbeddingPair 0 pointChart (𝟙 point) (by trivial) =
      chartModelEmbeddingPair 0 e (𝟙 point) hx := by
    apply MorphismProperty.Arrow.Hom.ext
    · ext z : 1
      apply Subtype.ext
      exact (inferInstance : Subsingleton (ComplexPoint point)).elim _ _
    · ext z : 1
      exact (inferInstance : Subsingleton (ComplexPoint point)).elim _ _
  exact congrArg (fun f => relativeHomologyMap ℚ 0 f (standardComplexLocalClass ℚ 0)) hm

example : localOrientation (a3b4_an intrinsicPoint.hom) 0 intrinsicPointClass
    (𝟙 intrinsicPoint) = pointLocal := pointGlobal_normalization

/-- The independent intrinsic point class generates its actual global homology.
Source: Hatcher, Algebraic Topology, sections 2.1 and 3.3, point excision and the chart generator.
HC no distance; AV milestone no distance. -/
theorem intrinsicPointClass_generates : Function.Bijective
    (LinearMap.toSpanSingleton ℚ (Homology ℚ (a3b4_an intrinsicPoint.hom) 0) intrinsicPointClass) := by
  constructor
  · intro q r h
    exact smul_left_injective ℚ intrinsicPointClass_ne_zero h
  · intro b
    have hs := span_localClassOfChart_eq_top 0 pointChart (𝟙 point) (by trivial)
    obtain ⟨q, hq⟩ := Submodule.mem_span_singleton.mp
      (show pointProjection b ∈ Submodule.span ℚ {pointLocal} by
        rw [show Submodule.span ℚ {pointLocal} = ⊤ from hs]
        exact Submodule.mem_top)
    refine ⟨q, pointProjection_bijective.injective ?_⟩
    change pointProjection (q • intrinsicPointClass) = pointProjection b
    rw [map_smul, show pointProjection intrinsicPointClass = pointLocal from pointGlobal_normalization]
    exact hq

example : Function.Bijective (LinearMap.toSpanSingleton ℚ
    (Homology ℚ (a3b4_an intrinsicPoint.hom) 0) intrinsicPointClass) := intrinsicPointClass_generates

/-- The actual identity scheme morphism retains the nonzero intrinsic point class with its actual residue degree one.
Source: Fulton, Intersection Theory, section 1.4; functorial singular homology.
HC no distance; AV milestone no distance. -/
theorem intrinsic_component_degree_homology_example :
    properCycle_intrinsic_image (𝟙 intrinsicPoint) 0 intrinsicPointClass =
      (a1p_degree (𝟙 intrinsicPoint.left) (genericPoint intrinsicPoint.left) : ℚ) • intrinsicPointClass ∧
      properCycle_intrinsic_image (𝟙 intrinsicPoint) 0 intrinsicPointClass ≠ 0 := by
  rw [properCycle_intrinsic_image_id]
  have hd : a1p_degree (𝟙 intrinsicPoint.left) (genericPoint intrinsicPoint.left) = 1 :=
    Scheme.Hom.residueDegree_id _
  simp only [hd, Nat.cast_one, one_smul, true_and]
  exact intrinsicPointClass_ne_zero

example : properCycle_intrinsic_image (𝟙 intrinsicPoint) 0 intrinsicPointClass ≠ 0 :=
  intrinsic_component_degree_homology_example.2

/-- A factor two breaks the actual nonzero projective-point homology pushforward equation.
Source: Fulton, Intersection Theory, section 1.4.
HC no distance; AV milestone no distance. -/
theorem intrinsic_component_degree_homology_factor_falsification :
    properCycle_intrinsic_image (𝟙 intrinsicPoint) 0 intrinsicPointClass ≠ (2 : ℚ) • intrinsicPointClass := by
  rw [properCycle_intrinsic_image_id]
  intro h
  have hh : ((2 : ℚ) - 1) • intrinsicPointClass = 0 := by
    rw [sub_smul, one_smul, ← h, sub_self]
  exact (smul_ne_zero (by norm_num : (2 : ℚ) - 1 ≠ 0) intrinsicPointClass_ne_zero) hh

example : properCycle_intrinsic_image (𝟙 intrinsicPoint) 0 intrinsicPointClass ≠
    (2 : ℚ) • intrinsicPointClass := intrinsic_component_degree_homology_factor_falsification

/-- Extending the actual coefficient-two prime coordinate retains the nonzero multiplicity.
Source: Fulton, Intersection Theory, section 1.5.
HC no distance; AV milestone no distance. -/
theorem global_support_factorization_coordinate_example :
    properCycle_extend_coordinates point.left (properPrime (genericPoint point.left))
      (fun _ => (2 : ℚ)) (genericPoint point.left) = 2 := by
  classical
  change (if h : genericPoint point.left ∈ (properPrime (genericPoint point.left)).support
    then 2 else 0) = 2
  rw [dif_pos (show genericPoint point.left ∈ (properPrime (genericPoint point.left)).support by
    simp [properPrime])]

example : properCycle_extend_coordinates point.left (properPrime (genericPoint point.left))
    (fun _ => (2 : ℚ)) (genericPoint point.left) = 2 := global_support_factorization_coordinate_example

/-- Replacing the component coordinate by zero loses a literal nonzero prime coefficient.
Source: Fulton, Intersection Theory, section 1.5.
HC no distance; AV milestone no distance. -/
theorem global_support_factorization_zero_falsification :
    properCycle_extend_coordinates point.left (properPrime (genericPoint point.left))
      (fun _ => (2 : ℚ)) ≠ 0 := by
  intro h
  have hh := congrFun h (genericPoint point.left)
  rw [global_support_factorization_coordinate_example] at hh
  norm_num at hh

example : properCycle_extend_coordinates point.left (properPrime (genericPoint point.left))
    (fun _ => (2 : ℚ)) ≠ 0 := global_support_factorization_zero_falsification

/-- The actual squaring morphism's generic prime evaluates with residue degree two.
Source: Fulton, Intersection Theory, section 1.4; a1p_degree_square_eq_two.
HC no distance; AV milestone no distance. -/
theorem intrinsic_component_degree_square_example :
    properCycle_component_evaluation (fun _ : a1p_affineLine.left => (1 : ℚ))
      (a1p_pushforward a1p_squareMap.left (properPrime a1p_affineLineGeneric)) = 2 := by
  classical
  rw [properPrime, a1p_pushforward_single, properCycle_component_evaluation_single,
    a1p_degree_square_eq_two]
  norm_num

example : properCycle_component_evaluation (fun _ : a1p_affineLine.left => (1 : ℚ))
    (a1p_pushforward a1p_squareMap.left (properPrime a1p_affineLineGeneric)) = 2 :=
  intrinsic_component_degree_square_example

/-- Omitting the residue-degree factor fails for the actual squaring morphism.
Source: Fulton, Intersection Theory, section 1.4.
HC no distance; AV milestone no distance. -/
theorem intrinsic_component_degree_factor_falsification :
    properCycle_component_evaluation (fun _ : a1p_affineLine.left => (1 : ℚ))
      (a1p_pushforward a1p_squareMap.left (properPrime a1p_affineLineGeneric)) ≠ 1 := by
  rw [intrinsic_component_degree_square_example]
  norm_num

example : properCycle_component_evaluation (fun _ : a1p_affineLine.left => (1 : ℚ))
    (a1p_pushforward a1p_squareMap.left (properPrime a1p_affineLineGeneric)) ≠ 1 :=
  intrinsic_component_degree_factor_falsification

end HodgeLean.Foundations.QuotientDuality.ProperCycleSplitChecks
