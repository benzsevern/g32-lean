import HodgeLean.Foundations.QuotientDuality.RetainedCycleDefs
import HodgeLean.Foundations.QuotientDuality.RetainedCycleSingularChecks
import HodgeLean.Foundations.Program.SchoenCycleC2IsoPointHelpers
import HodgeConjecture.Lemmas.AlgebraicGeometry.ComplexPoint.AffineSpace
import HodgeLean.Adapters.NormalConeB4aClassExistsPure
import HodgeLean.Adapters.NormalConeB4aClassUniqueBoundary
import HodgeLean.Foundations.Analytic.Analytification
import HodgeLean.Foundations.Program.SchoenSelectedGeometryProjectiveDimension
import HodgeLean.RealDefs.DegreeZero
import HodgeConjecture.Lemmas.AlgebraicTopology.Singular.RelativeHomotopyInvariance

/-! # Independent retained cycle checks

Actual component inclusions, orbit coefficients and support enlargement detect
altered chart domains, trace scales, multiplicities and cancellation.
HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry AlgebraicTopology.Singular
open HodgeLean.Adapters HodgeLean.Foundations.Program
open HodgeLean.Foundations.Analytic HodgeLean.RealDefs
open scoped BigOperators
namespace HodgeLean.Foundations.QuotientDuality.RetainedCycleChecks

private abbrev point : Over (Spec ↧ℂ) := Over.mk (𝟙 (Spec ↧ℂ))
private instance retainedCyclePointNonempty : Nonempty (ComplexPoint point) := ⟨𝟙 point⟩
private instance retainedCyclePointIntegral : IsIntegral point.left :=
  inferInstanceAs (IsIntegral (Spec (CommRingCat.of ℂ)))
private instance retainedCyclePointDecidable : DecidableEq point.left := Classical.decEq _

private instance retainedCyclePointUnique : Unique (ComplexPoint point) where
  default := 𝟙 point
  uniq f := by
    apply Over.OverMorphism.ext
    simpa using f.w

private def pointChart : OpenPartialHomeomorph (ComplexPoint point)
    ((Fin (0 : ℕ) → ℂ) × (Fin (0 : ℕ) → ℂ)) := by
  letI : Unique ((Fin (0 : ℕ) → ℂ) × (Fin (0 : ℕ) → ℂ)) :=
    { default := 0, uniq := fun _ => Subsingleton.elim _ _ }
  exact (Homeomorph.homeomorphOfUnique _ _).toOpenPartialHomeomorph


private def weightedPrime : AlgebraicCycle point.left ℚ :=
  (properPrime (genericPoint point.left)).mapRange ((1 : ℚ) * ·) (mul_zero _)
private theorem orbit_eq : weightedPrime = Function.locallyFinsuppWithin.single
    (genericPoint point.left) (1 : ℚ) := by
  classical
  ext x
  by_cases h : x = genericPoint point.left <;> simp [weightedPrime, properPrime, h]
private theorem zero_pair_orbit_coefficient :
    weightedPrime (genericPoint point.left) = (1 : ℚ) := by
  classical
  rw [orbit_eq]; simp
private theorem zero_pair_normalized_class :
    ∃ α : s2e_supportedClass point weightedPrime (0 : ℕ),
      a3b4_IsCycleClass point.hom weightedPrime (0 : ℕ) α := by
  apply a3b4a_cycleClass_exists_of_codimension
  intro x hx
  exact bot_le

private theorem zero_pair_full_support :
    a3b4_cycleSupport point.hom weightedPrime = Set.univ := by
  ext x
  constructor
  · intro _; trivial
  · intro _
    change Point.underlying x ∈ ⋃ ξ ∈ weightedPrime.support, closure {ξ}
    apply Set.mem_iUnion.mpr
    refine ⟨genericPoint point.left, Set.mem_iUnion.mpr ⟨?_, ?_⟩⟩
    · change weightedPrime (genericPoint point.left) ≠ 0
      rw [zero_pair_orbit_coefficient]; norm_num
    · rw [genericPoint_closure]; trivial

private def fixedSupported : s2e_supportedClass point weightedPrime (0 : ℕ) :=
  zero_pair_normalized_class.choose

private theorem fixedSupported_normalized :
    a3b4_IsCycleClass point.hom weightedPrime (0 : ℕ) fixedSupported :=
  zero_pair_normalized_class.choose_spec

private theorem fixedSupported_ne_zero : fixedSupported ≠ 0 := by
  intro hz
  have hS : ∀ y ∈ pointChart.source,
      y ∈ a3b4_cycleSupport point.hom weightedPrime ↔ (pointChart y).2 = 0 := by
    intro y hy
    rw [zero_pair_full_support]
    simp only [Set.mem_univ, true_iff]
    exact Subsingleton.elim _ _
  have hhol : a3b4_IsHolChart point.hom pointChart :=
    ⟨fun j => Fin.elim0 j, fun j => Fin.elim0 j⟩
  let x : ComplexPoint point := 𝟙 point
  obtain ⟨W, hW, hWo, hxW, hnorm⟩ := fixedSupported_normalized (0 : ℕ)
    pointChart hS x (by change x ∈ Set.univ; trivial) (by rw [zero_pair_full_support]; trivial) hhol
  have hm : a3b4_multiplicity point.hom weightedPrime x = (1 : ℚ) := by
    classical
    have hc : weightedPrime = Function.locallyFinsuppWithin.single
        (genericPoint point.left) (1 : ℚ) := by
      exact orbit_eq
    have hcoeff : weightedPrime (genericPoint point.left) = (1 : ℚ) := by
      rw [hc]; simp
    rw [a3b4a_classMultiplicity_eq_component point.hom weightedPrime
      (genericPoint point.left) (by change weightedPrime _ ≠ 0; rw [hcoeff]; norm_num)
      x (by rw [genericPoint_closure]; trivial) (by
        intro η hη hne
        have heq : η = genericPoint point.left := by simpa [hc] using hη
        exact (hne heq).elim), hcoeff]

  rw [hz, map_zero, hm] at hnorm
  have hn := chartNormalProjectionCoclass_ne_zero (Fin (0 : ℕ) → ℂ) (0 : ℕ)
    pointChart (a3b4_cycleSupport point.hom weightedPrime) hS hWo hW hxW
      (Subsingleton.elim _ _)
  exact (smul_ne_zero (by norm_num : (1 : ℚ) ≠ 0) hn) hnorm.symm

private abbrev pointH0 := AlgebraicTopology.Singular.Cohomology ℚ
  (TopCat.of (ComplexPoint point)) (0 : ℕ)
private def fixedAbsolute : pointH0 := s2e_classToAbsolute point weightedPrime (0 : ℕ) fixedSupported

private theorem fixedAbsolute_ne_zero : fixedAbsolute ≠ 0 := by
  have hi : Function.Injective (s2e_classToAbsolute point weightedPrime (0 : ℕ)) := by
    unfold s2e_classToAbsolute s2e_supportedClass
    rw [zero_pair_full_support]
    let X := TopCat.of (ComplexPoint point)
    let P := TopPair.ofSubset ((Set.univ : Set X)ᶜ)
    have hmap : ((AlgebraicTopology.Singular.chainPairFunctor ℚ).obj P).hom = 0 := by
      apply HomologicalComplex.hom_ext
      intro n
      change (SSet.chainComplexMap (TopCat.toSSet.map P.map)
        (ModuleCat.of ℚ ℚ)).f n = 0
      apply SSet.chainComplex_hom_ext
      intro σ
      let f := P.snd.toSSetObjEquiv (Opposite.op (SimplexCategory.mk n)) σ
      exact ((f Convexity.StdSimplex.barycenter).2 trivial).elim
    letI : IsIso (AlgebraicTopology.Singular.relativeChainProjection ℚ P) :=
      CategoryTheory.Limits.cokernel.π_of_zero hmap
    let e := HomologicalComplex.homologyMapIso
      (HomologicalComplex.linearDualIso
        (asIso (AlgebraicTopology.Singular.relativeChainProjection ℚ P))) (0 : ℕ)
    exact ((ConcreteCategory.isIso_iff_bijective e.hom).mp e.isIso_hom).1
  intro hz
  exact fixedSupported_ne_zero (hi (hz.trans (map_zero _).symm))


set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

private abbrev P := TopCat.of (ComplexPoint point)
private abbrev u : Cohomology ℚ P 0 := HodgeLean.Foundations.Singular.unit P
private def c₀ : Homology ℚ P 0 :=
  (asIso (P.singularHomology₀ε (ModuleCat.of ℚ ℚ))).inv.hom (1 : ℚ)
private theorem eval₀ : orientationIntegral P 0 c₀ (cohomologyUnitZero ℚ P) = 1 := by
  change cohomologyEquivDualHomology ℚ P 0 (cohomologyUnitZero ℚ P) _ = _
  rw [cohomologyEquivDualHomology_cohomologyUnitZero]
  exact LinearMap.congr_fun
    (congrArg ModuleCat.Hom.hom (Iso.inv_hom_id
      (asIso (P.singularHomology₀ε (ModuleCat.of ℚ ℚ))))) 1
private def scalar : ℚ := Classical.choose (exists_smul_cohomologyUnitZero ℚ P u)
private theorem scalar_spec : scalar • cohomologyUnitZero ℚ P = u :=
  Classical.choose_spec (exists_smul_cohomologyUnitZero ℚ P u)
private theorem scalar_ne : scalar ≠ 0 := by
  intro h
  have hs := scalar_spec
  rw [h, zero_smul] at hs
  exact HodgeLean.Foundations.Singular.unit_ne_zero P hs.symm
private def c : Homology ℚ P 0 := scalar⁻¹ • c₀
private theorem eval_unit : orientationIntegral P 0 c u = 1 := by
  change cohomologyEquivDualHomology ℚ P 0 u (scalar⁻¹ • c₀) = 1
  rw [map_smul, ← scalar_spec, map_smul]
  change scalar⁻¹ * (scalar * orientationIntegral P 0 c₀ (cohomologyUnitZero ℚ P)) = 1
  rw [eval₀, mul_one, inv_mul_cancel₀ scalar_ne]
private def E : Cohomology ℚ P 0 →ₗ[ℚ] ℚ := orientationIntegral P 0 c
private theorem E_unit : E u = (1 : ℚ) := eval_unit
private theorem E_coordinates (a : Cohomology ℚ P 0) : E a • u = a := by
  obtain ⟨q, hq⟩ := exists_smul_cohomologyUnitZero ℚ P a
  have ha : a = (q * scalar⁻¹) • u := by
    rw [← scalar_spec, smul_smul, mul_assoc, inv_mul_cancel₀ scalar_ne, mul_one]
    exact hq.symm
  conv_lhs => rw [ha, map_smul, E_unit]
  simpa only [smul_eq_mul, mul_one] using ha.symm
private theorem E_injective : Function.Injective E := by
  intro a b h
  rw [← E_coordinates a, ← E_coordinates b, h]
private theorem eval_E (a : Cohomology ℚ P 0) : orientationIntegral P 0 c a = E a := rfl
private theorem pair_formula (X : TopCat.{0}) (cX : Homology ℚ X 0)
    (a b : Cohomology ℚ X 0) :
    properCyclePairing X 0 cX a b =
      orientationIntegral X 0 cX (HodgeLean.Foundations.Singular.cup X (p := 0) (q := 0) (k := 0) rfl a b) := rfl
private theorem pair_value (a b : Cohomology ℚ P 0) :
    properCyclePairing P 0 c a b = E a * E b := by
  rw [pair_formula, eval_E]
  conv_lhs => rw [← E_coordinates a, ← E_coordinates b,
    HodgeLean.Foundations.Singular.cup_constants, map_smul, E_unit]
  simp only [smul_eq_mul, mul_one]
private theorem perfect : Function.Bijective (properCyclePairing P 0 c) := by
  constructor
  · intro a b h
    apply E_injective
    have hh := LinearMap.congr_fun h u
    simpa only [pair_value, E_unit, mul_one] using hh
  · intro l
    refine ⟨l u • u, ?_⟩
    ext a
    rw [pair_value, map_smul, E_unit]
    have ha : (E a) • u = a := E_coordinates a
    conv_rhs => rw [← ha, map_smul]
    simp only [smul_eq_mul, one_mul, mul_comm]

private theorem enlargement_refl (X : TopCat.{0}) (S : Set X) (n : ℕ)
    (a : CohomologyWithSupport ℚ X S n) :
    enlargeSupport ℚ X (Set.Subset.rfl : S ⊆ S) n a = a := by
  change enlargeSupport ℚ X (Set.Subset.rfl : S ⊆ S) n a = a
  rw [enlargeSupport_rfl, LinearMap.id_apply]

private def enlarged : s2e_supportedClass point weightedPrime 0 :=
  enlargeSupport ℚ P (Set.Subset.rfl :
    a3b4_cycleSupport point.hom weightedPrime ⊆ a3b4_cycleSupport point.hom weightedPrime) 0 fixedSupported
private theorem enlarged_eq : enlarged = fixedSupported := enlargement_refl _ _ _ _
private theorem doubled_ne {M : Type} [AddCommGroup M] [Module ℚ M]
    (v : M) (hv : v ≠ 0) : v ≠ (2 : ℚ) • v := by
  intro h
  have hh : v + v = 0 + v := by simpa only [two_smul, zero_add] using h.symm
  exact hv (add_right_cancel hh)

private instance retainedComponentSurjective :
    Surjective (cycleComponentι point.left (genericPoint point.left)) := by
  constructor
  rw [← Set.range_eq_univ, range_cycleComponentι, genericPoint_closure]
private instance retainedComponentIsIso :
    IsIso (cycleComponentι point.left (genericPoint point.left)) :=
  isIso_of_isClosedImmersion_of_surjective _
private instance retainedComponentOverIsIso :
    IsIso (intrinsicComponentInclusion point (genericPoint point.left)) := by
  letI : IsIso ((Over.forget (Spec ↧ℂ)).map
      (intrinsicComponentInclusion point (genericPoint point.left))) := by
    change IsIso (cycleComponentι point.left (genericPoint point.left))
    infer_instance
  exact isIso_of_reflects_iso _ (Over.forget (Spec ↧ℂ))
private abbrev component := intrinsicComponent point (genericPoint point.left)
private def componentIso : component ≅ point :=
  asIso (intrinsicComponentInclusion point (genericPoint point.left))
private instance retainedComponentUnique : Unique (ComplexPoint component) :=
  (s2e_pointHomeomorphOfIso componentIso).toEquiv.unique
private def componentChart : OpenPartialHomeomorph (ComplexPoint component) (Fin 0 → ℂ) :=
  (Homeomorph.homeomorphOfUnique _ _).toOpenPartialHomeomorph

/-- The actual reduced component has a nonempty chart; an empty domain loses its point.
Source: Hartshorne, II.8, smooth coordinates.
HC no distance; AV milestone no distance. -/
private theorem check_component_point_chart :
    (default : ComplexPoint component) ∈ componentChart.source ∧
    (∀ j : Fin 0, (HodgeLean.Foundations.Analytic.f4_analytification component).IsHolFun
      (fun u : componentChart.source => componentChart u j)) ∧
    ¬ (default : ComplexPoint component) ∈ (∅ : Set (ComplexPoint component)) := by
  exact ⟨Set.mem_univ _, fun j => Fin.elim0 j, Set.notMem_empty _⟩
example := check_component_point_chart


private abbrev affineOne : Over (Spec ↧ℂ) :=
  Over.mk (AlgebraicGeometry.ComplexPoint.complexAffineSpace (Fin 1) ↘ Spec ↧ℂ)
private instance retainedAffineOneIntegral : IsIntegral affineOne.left := by
  change IsIntegral (AffineSpace (Fin 1) (Spec ↧ℂ))
  infer_instance
private instance retainedAffineComponentSurjective :
    Surjective (cycleComponentι affineOne.left (genericPoint affineOne.left)) := by
  constructor
  rw [← Set.range_eq_univ, range_cycleComponentι, genericPoint_closure]
private instance retainedAffineComponentIsIso :
    IsIso (cycleComponentι affineOne.left (genericPoint affineOne.left)) :=
  isIso_of_isClosedImmersion_of_surjective _
private instance retainedAffineComponentOverIsIso :
    IsIso (intrinsicComponentInclusion affineOne (genericPoint affineOne.left)) := by
  letI : IsIso ((Over.forget (Spec ↧ℂ)).map
      (intrinsicComponentInclusion affineOne (genericPoint affineOne.left))) := by
    change IsIso (cycleComponentι affineOne.left (genericPoint affineOne.left))
    infer_instance
  exact isIso_of_reflects_iso _ (Over.forget (Spec ↧ℂ))
private def affineComponentHomeomorph :
    ComplexPoint (intrinsicComponent affineOne (genericPoint affineOne.left)) ≃ₜ (Fin 1 → ℂ) :=
  (s2e_pointHomeomorphOfIso
    (asIso (intrinsicComponentInclusion affineOne (genericPoint affineOne.left)))).trans
      (AlgebraicGeometry.ComplexPoint.affineSpaceHomeomorph (Fin 1))
private def affineComponentChart := affineComponentHomeomorph.toOpenPartialHomeomorph
private def affineComponentZero := affineComponentHomeomorph.symm (0 : Fin 1 → ℂ)
private def affineComponentOne := affineComponentHomeomorph.symm (1 : Fin 1 → ℂ)

/-- The reduced affine component has a positive dimensional chart, rejecting a constant chart.
Source: Hartshorne, II.8; the standard affine coordinate construction.
HC no distance; AV milestone no distance. -/
private theorem check_affine_component_values :
    (default : ComplexPoint component) ∈ componentChart.source ∧
    affineComponentChart affineComponentZero (0 : Fin 1) = (0 : ℂ) ∧
    affineComponentChart affineComponentOne (0 : Fin 1) = (1 : ℂ) ∧
    ¬ ∀ z ∈ affineComponentChart.source, affineComponentChart z = (0 : Fin 1 → ℂ) := by
  have hz : affineComponentChart affineComponentZero = (0 : Fin 1 → ℂ) :=
    affineComponentHomeomorph.apply_symm_apply _
  have ho : affineComponentChart affineComponentOne = (1 : Fin 1 → ℂ) :=
    affineComponentHomeomorph.apply_symm_apply _
  refine ⟨check_component_point_chart.1, congrFun hz 0, congrFun ho 0, ?_⟩
  intro h
  have he := congrFun (h affineComponentOne (Set.mem_univ _)) (0 : Fin 1)
  rw [ho] at he
  norm_num at he
example := check_affine_component_values

private abbrev lineScheme := intrinsicComponent affineOne (genericPoint affineOne.left)
private instance retainedLineFiniteType : LocallyOfFiniteType lineScheme.hom := by
  change LocallyOfFiniteType (cycleComponentι affineOne.left (genericPoint affineOne.left) ≫ affineOne.hom)
  infer_instance
private instance retainedLineQuasiCompact : QuasiCompact lineScheme.hom := by
  change QuasiCompact (cycleComponentι affineOne.left (genericPoint affineOne.left) ≫ affineOne.hom)
  infer_instance
private instance retainedLineSeparated : IsSeparated lineScheme.hom := by
  change IsSeparated (cycleComponentι affineOne.left (genericPoint affineOne.left) ≫ affineOne.hom)
  infer_instance
private def lineChart := affineComponentChart
private theorem lineChart_hol (j : Fin 1) :
    (f4_analytification lineScheme).IsHolFun (fun z : lineChart.source => lineChart z j) := by
  have hcoord : (an_euclidSpace 1).IsHolFun
      (fun z : (Set.univ : Set (Fin 1 → ℂ)) => z.val j) := by
    intro z i hi
    exact ⟨Set.univ, isOpen_univ, Set.mem_univ _, (fun w : Fin 1 → ℂ => w j),
      ((ContinuousLinearMap.proj j : (Fin 1 → ℂ) →L[ℂ] ℂ).analyticAt _), fun _ _ => rfl⟩
  have hl := (f4_affineSpace_isHom 1).1.2 Set.univ isOpen_univ _ hcoord
  exact (f4_map_isHom (intrinsicComponentInclusion affineOne (genericPoint affineOne.left))).2
    Set.univ isOpen_univ _ hl

/-- Positive-dimensional holomorphic charts commute with the retained identity map;
rescaling one chart breaks the square at the unit point.
Source: Hartshorne, II.8; Serre, GAGA, section 2.
HC no distance; AV milestone no distance. -/
theorem check_retained_orbit_component_charts :
    (∀ j : Fin 1, (f4_analytification lineScheme).IsHolFun
      (fun z : lineChart.source => lineChart z j)) ∧
    (∀ z ∈ lineChart.source, lineChart z = lineChart (Point.map (𝟙 lineScheme) z)) ∧
    ¬ (∀ z ∈ lineChart.source,
      lineChart z = (2 : ℂ) • lineChart (Point.map (𝟙 lineScheme) z)) := by
  refine ⟨lineChart_hol, ?_, ?_⟩
  · intro z hz
    rfl
  · intro h
    let z := affineComponentOne
    have he := congrFun (h z (Set.mem_univ _)) (0 : Fin 1)
    change affineComponentHomeomorph z (0 : Fin 1) =
      (2 : ℂ) * affineComponentHomeomorph z (0 : Fin 1) at he
    have hz : affineComponentHomeomorph z = (1 : Fin 1 → ℂ) :=
      affineComponentHomeomorph.apply_symm_apply _
    rw [hz] at he
    norm_num at he
example := check_retained_orbit_component_charts

/-- Trace evaluation of the enlarged nonzero class detects a factor two.
Source: Hatcher, section 3.3.
HC no distance; AV milestone no distance. -/
theorem check_retained_trace_identification :
    orientationIntegral P 0 c (s2e_classToAbsolute point weightedPrime 0 enlarged) = E fixedAbsolute ∧
    orientationIntegral P 0 c (s2e_classToAbsolute point weightedPrime 0 enlarged) ≠
      ((2 : ℚ) • orientationIntegral P 0 c) (s2e_classToAbsolute point weightedPrime 0 enlarged) := by
  have hn : E fixedAbsolute ≠ 0 := by
    intro h
    exact fixedAbsolute_ne_zero (E_injective (h.trans (map_zero E).symm))
  rw [enlarged_eq]
  refine ⟨rfl, ?_⟩
  change E fixedAbsolute ≠ (2 : ℚ) • E fixedAbsolute
  exact doubled_ne _ hn
example := check_retained_trace_identification

private instance retainedLineIntegral : IsIntegral a1p_affineLine.left := by
  change IsIntegral (Spec (CommRingCat.of (Polynomial ℂ)))
  infer_instance
private theorem single_orbit (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [DecidableEq X.left] :
    s2e_rationalOrbitCycle (𝟙 X) (𝟙 X) 1 (fun _ => (2 : ℚ)) =
      Function.locallyFinsuppWithin.single (genericPoint X.left) (2 : ℚ) := by
  classical
  ext x
  simp [s2e_rationalOrbitCycle, s2e_componentCycle, Fin.sum_univ_one,
    Function.locallyFinsuppWithin.mapRange_apply]

/-- A nonidentity ramified map retains both the orbit coefficient and the residue degree.
Source: Fulton, Intersection Theory, section 1.4.
HC no distance; AV milestone no distance. -/
theorem check_retained_orbit_coefficients :
    retainedOrbitCoefficient a1p_squareMap (𝟙 a1p_affineLine) (𝟙 a1p_affineLine)
      1 (fun _ => (2 : ℚ)) (a1p_squareMap.left a1p_affineLineGeneric) = 4 ∧
    retainedOrbitCoefficient a1p_squareMap (𝟙 a1p_affineLine) (𝟙 a1p_affineLine)
      1 (fun _ => (2 : ℚ)) (a1p_squareMap.left a1p_affineLineGeneric) ≠ 2 := by
  classical
  unfold retainedOrbitCoefficient
  have hd : a1p_degree a1p_squareMap.left (genericPoint a1p_affineLine.left) = 2 :=
    a1p_degree_square_eq_two
  rw [single_orbit, a1p_pushforward_single, hd]
  norm_num [a1p_affineLineGeneric]
example := check_retained_orbit_coefficients

/-- Intrinsic integration rejects reversing the nonzero supported class.
Source: Bredon, Sheaf Theory, V.9.
HC no distance; AV milestone no distance. -/
private theorem check_point_duality :
    a3b4_IsCycleClass point.hom weightedPrime 0 enlarged ∧
    properCyclePairing P 0 c (s2e_classToAbsolute point weightedPrime 0 enlarged) u ≠
      properCyclePairing P 0 c (-s2e_classToAbsolute point weightedPrime 0 enlarged) u := by
  rw [enlarged_eq]
  refine ⟨fixedSupported_normalized, ?_⟩
  have hn : E fixedAbsolute ≠ 0 := by
    intro h
    exact fixedAbsolute_ne_zero (E_injective (h.trans (map_zero E).symm))
  rw [pair_value, pair_value, E_unit, mul_one, mul_one, map_neg]
  intro h
  change E fixedAbsolute = -E fixedAbsolute at h
  exact hn (by linarith)
example := check_point_duality

private def unitOnSupport (S : Set P) (hS : S = Set.univ) :
    CohomologyWithSupport ℚ P S 0 := by
  subst S
  exact (wholeSupportCohomologyLinearEquiv ℚ P 0).symm u
private theorem unitOnSupport_absolute (S : Set P) (hS : S = Set.univ) :
    forgetSupport ℚ P S 0 (unitOnSupport S hS) = u := by
  subst S
  exact (wholeSupportCohomologyLinearEquiv ℚ P 0).apply_symm_apply u
private def unitSupported : s2e_supportedClass point weightedPrime 0 :=
  unitOnSupport (a3b4_cycleSupport point.hom weightedPrime) zero_pair_full_support
private theorem unitSupported_absolute :
    s2e_classToAbsolute point weightedPrime 0 unitSupported = u :=
  unitOnSupport_absolute _ _
private def componentFundamental : Homology ℚ (a3b4_an component.hom) 0 :=
  homologyMap ℚ 0 (TopCat.ofHom (Point.continuousMap componentIso.inv)) c
private theorem component_integral (v : Cohomology ℚ P 0) :
    orientationIntegral (a3b4_an component.hom) 0 componentFundamental
      (s2e_pullback ℚ (intrinsicComponentInclusion point (genericPoint point.left)) 0 v) = E v := by
  change cohomologyEquivDualHomology ℚ (a3b4_an component.hom) 0
    (cohomologyMap ℚ 0 (TopCat.ofHom (Point.continuousMap componentIso.hom)) v)
      (homologyMap ℚ 0 (TopCat.ofHom (Point.continuousMap componentIso.inv)) c) = E v
  rw [cohomologyEquivDualHomology_cohomologyMap,
    ← LinearMap.comp_apply (homologyMap ℚ 0 (TopCat.ofHom (Point.continuousMap componentIso.hom)))
      (homologyMap ℚ 0 (TopCat.ofHom (Point.continuousMap componentIso.inv))),
    ← homologyMap_comp]
  have hid : TopCat.ofHom (Point.continuousMap componentIso.inv) ≫
      TopCat.ofHom (Point.continuousMap componentIso.hom) = 𝟙 P := by
    apply TopCat.hom_ext
    apply ContinuousMap.ext
    intro z
    change Point.map (componentIso.inv ≫ componentIso.hom) z = z
    rw [Iso.inv_hom_id]
    rfl
  rw [hid, homologyMap_id, LinearMap.id_apply]
  rfl

/-- The intrinsic component has the global supported integration equation for every test class.
The supported unit is nonzero, and reversing the intrinsic orientation breaks the equation.
Source: Hatcher, section 3.3, integration against the fundamental class of a point.
HC no distance; AV milestone no distance. -/
theorem check_intrinsic_supported_integration_equation :
    unitSupported ≠ 0 ∧
    (∀ v : Cohomology ℚ P 0,
      properCyclePairing P 0 c (s2e_classToAbsolute point weightedPrime 0 unitSupported) v =
        orientationIntegral (a3b4_an component.hom) 0 componentFundamental
          (s2e_pullback ℚ (intrinsicComponentInclusion point (genericPoint point.left)) 0 v)) ∧
    properCyclePairing P 0 c (s2e_classToAbsolute point weightedPrime 0 unitSupported) u ≠
      orientationIntegral (a3b4_an component.hom) 0 (-componentFundamental)
        (s2e_pullback ℚ (intrinsicComponentInclusion point (genericPoint point.left)) 0 u) := by
  refine ⟨?_, ?_, ?_⟩
  · intro h
    have he := unitSupported_absolute
    rw [h, map_zero] at he
    exact HodgeLean.Foundations.Singular.unit_ne_zero P he.symm
  · intro v
    rw [unitSupported_absolute, pair_value, E_unit, one_mul, component_integral]
  · rw [unitSupported_absolute, pair_value, E_unit, one_mul]
    change (1 : ℚ) ≠ cohomologyEquivDualHomology ℚ (a3b4_an component.hom) 0 _ (-componentFundamental)
    rw [map_neg]
    change (1 : ℚ) ≠ -(orientationIntegral (a3b4_an component.hom) 0 componentFundamental _)
    rw [component_integral, E_unit]
    norm_num
example := check_intrinsic_supported_integration_equation

/-- Intrinsic normalization remains nonzero on the reduced axis inside a singular ambient cylinder.
Source: Hartshorne, Algebraic Geometry, I.5 and II.3; Bredon, Sheaf Theory, V.9.
HC no distance; AV milestone no distance. -/
theorem check_intrinsic_prime_supported_duality :
    type_of% RetainedCycleSingularChecks.check_singular_axis :=
  RetainedCycleSingularChecks.check_singular_axis
example := check_intrinsic_prime_supported_duality

/-- Opposite occurrences cancel in the common supported carrier; dropping one does not.
Source: Fulton, Intersection Theory, sections 1.3 and 19.1.
HC no distance; AV milestone no distance. -/
theorem check_intrinsic_supported_additivity :
    enlarged + (-enlarged) = 0 ∧ enlarged + (-enlarged) ≠ enlarged ∧
    (∑ i : Fin 2, (properPrime (genericPoint point.left)).mapRange
      ((if i = (0 : Fin 2) then (1 : ℚ) else (-1 : ℚ)) * ·) (mul_zero _)) =
      (0 : AlgebraicCycle point.left ℚ) := by
  classical
  refine ⟨add_neg_cancel _, ?_, ?_⟩
  · rw [add_neg_cancel, enlarged_eq]
    exact Ne.symm fixedSupported_ne_zero
  · ext x
    simp [Fin.sum_univ_two, Function.locallyFinsuppWithin.mapRange_apply]
example := check_intrinsic_supported_additivity

private def zeroTowerMap : point ⟶ point :=
  retainedCycleModification (fun _ : Fin 1 => point) (Iso.refl point) (Iso.refl point)
    (fun i : Fin 0 => Fin.elim0 i)
private theorem zeroTowerMap_eq : zeroTowerMap = 𝟙 point := by
  simp [zeroTowerMap, retainedCycleModification, s2e_towerTotalMap]

/-- The retained total map and identity-open square preserve a nonzero supported class.
Source: Fulton, Intersection Theory, section 19.2; Hatcher, section 3.1.
HC no distance; AV milestone no distance. -/
private theorem check_total_map :
    zeroTowerMap = 𝟙 point ∧
    enlargeSupport ℚ P (Set.Subset.rfl :
      a3b4_cycleSupport point.hom weightedPrime ⊆ a3b4_cycleSupport point.hom weightedPrime)
        0 enlarged = enlarged ∧
    enlarged ≠ (0 : s2e_supportedClass point weightedPrime 0) := by
  refine ⟨zeroTowerMap_eq, enlargement_refl _ _ _ _, ?_⟩
  rw [enlarged_eq]
  exact fixedSupported_ne_zero
example := check_total_map


private instance retainedZeroTowerProper : IsProper zeroTowerMap.left := by
  rw [zeroTowerMap_eq]
  infer_instance

/-- The actual retained point pushforward preserves a normalized nonzero class;
reversing that supported class fails the transport comparison.
Source: Fulton, Intersection Theory, sections 1.4 and 19.2.
HC no distance; AV milestone no distance. -/
theorem check_retained_proper_cycle_class_comparison :
    a1p_pushforward zeroTowerMap.left weightedPrime = weightedPrime ∧
    a3b4_IsCycleClass point.hom weightedPrime 0 enlarged ∧
    enlargeSupport ℚ P (Set.Subset.rfl :
      a3b4_cycleSupport point.hom weightedPrime ⊆ a3b4_cycleSupport point.hom weightedPrime)
        0 enlarged = enlarged ∧ -enlarged ≠ enlarged := by
  refine ⟨?_, ?_, enlargement_refl _ _ _ _, ?_⟩
  · simpa only [zeroTowerMap_eq, Over.id_left] using (a1p_pushforward_id weightedPrime)
  · rw [enlarged_eq]
    exact fixedSupported_normalized
  · intro h
    have hn : enlarged ≠ 0 := enlarged_eq ▸ fixedSupported_ne_zero
    have hh : (2 : ℚ) • enlarged = 0 := by
      rw [two_smul]
      nth_rw 1 [← h]
      exact neg_add_cancel _
    exact (smul_ne_zero (by norm_num : (2 : ℚ) ≠ 0) hn) hh
example := check_retained_proper_cycle_class_comparison

private def pointPush : s2e_supportedClass point weightedPrime 0 →ₗ[ℚ]
    s2e_supportedClass point weightedPrime 0 := LinearMap.id

/-- The supported class of the actual pushed cycle equals F of the source class;
changing F to its negative breaks that equality.
Source: Fulton, Intersection Theory, section 19.2.
HC no distance; AV milestone no distance. -/
theorem check_retained_supported_pushforward_equality :
    ∃ b : s2e_supportedClass point (a1p_pushforward zeroTowerMap.left weightedPrime) 0,
      a3b4_IsCycleClass point.hom (a1p_pushforward zeroTowerMap.left weightedPrime) 0 b ∧
      ∃ hpush : a3b4_cycleSupport point.hom
          (a1p_pushforward zeroTowerMap.left weightedPrime) ⊆
            a3b4_cycleSupport point.hom weightedPrime,
        enlargeSupport ℚ P hpush 0 b = pointPush enlarged ∧
        enlargeSupport ℚ P hpush 0 b ≠ (-pointPush) enlarged := by
  have hp : a1p_pushforward zeroTowerMap.left weightedPrime = weightedPrime := by
    simpa only [zeroTowerMap_eq, Over.id_left] using (a1p_pushforward_id weightedPrime)
  rw [hp]
  refine ⟨enlarged, ?_, Set.Subset.rfl, ?_, ?_⟩
  · rw [enlarged_eq]
    exact fixedSupported_normalized
  · exact enlargement_refl _ _ _ _
  · rw [enlargement_refl]
    change enlarged ≠ -enlarged
    exact Ne.symm check_retained_proper_cycle_class_comparison.2.2.2
example := check_retained_supported_pushforward_equality

set_option backward.isDefEq.respectTransparency false

private instance retainedTwoTopology : TopologicalSpace (Fin 2) := ⊥
private instance retainedTwoDiscrete : DiscreteTopology (Fin 2) := ⟨rfl⟩
private abbrev twoVertices : TopCat.{0} := TopCat.of (Fin 2)
private def exchange : twoVertices ⟶ twoVertices :=
  TopCat.ofHom ⟨Equiv.swap (0 : Fin 2) 1, continuous_of_discreteTopology⟩
private theorem twoVertices_boundary :
    (SingularChainComplex ℚ twoVertices).d 1 0 = 0 := by
  apply SSet.chainComplex_hom_ext
  intro σ
  have hf : (TopCat.toSSet.obj twoVertices).δ (0 : Fin 2) σ =
      (TopCat.toSSet.obj twoVertices).δ (1 : Fin 2) σ := by
    apply TopCat.toSSetObj₀Equiv.injective
    exact PreconnectedSpace.constant inferInstance
      ((twoVertices.toSSetObjEquiv _ σ).continuous)
  change (TopCat.toSSet.obj twoVertices).ιChainComplex σ ≫
    ((TopCat.toSSet.obj twoVertices).chainComplex (ModuleCat.of ℚ ℚ)).d 1 0 = _
  rw [SSet.ιChainComplex_d, Fin.sum_univ_two]
  simp only [Fin.val_zero, Fin.val_one, pow_zero, pow_one, one_smul,
    neg_smul, hf, add_neg_cancel, Limits.comp_zero, CategoryTheory.Limits.comp_zero]

private theorem twoVertices_coboundary :
    (SingularCochainComplex ℚ twoVertices).d 0 1 = 0 := by
  change ModuleCat.ofHom ((SingularChainComplex ℚ twoVertices).d 1 0).hom.dualMap = 0
  rw [twoVertices_boundary]
  ext φ c
  exact map_zero φ

private def zeroIso : Cohomology ℚ twoVertices 0 ≅
    (SingularCochainComplex ℚ twoVertices).X 0 :=
  (SingularCochainComplex ℚ twoVertices).isoHomologyπ₀.symm ≪≫
    (SingularCochainComplex ℚ twoVertices).iCyclesIso 0 1 (by simp) twoVertices_coboundary

private def vertex (x : twoVertices) := TopCat.toSSetObj₀Equiv.symm x

private def vertexChain (x : twoVertices) : (SingularChainComplex ℚ twoVertices).X 0 :=
  ((TopCat.toSSet.obj twoVertices).ιChainComplex (vertex x)
    (R := ModuleCat.of ℚ ℚ)).hom 1

private def indicator : Module.Dual ℚ ((SingularChainComplex ℚ twoVertices).X 0) :=
  (CategoryTheory.Limits.Sigma.desc (fun σ => ModuleCat.ofHom
    ((LinearMap.ringLmapEquivSelf ℚ ℚ ℚ).symm
      (if TopCat.toSSetObj₀Equiv σ = (0 : Fin 2) then 1 else 0)))).hom

private theorem indicator_vertex (x : twoVertices) :
    indicator (vertexChain x) = if x = 0 then 1 else 0 := by
  change ModuleCat.Hom.hom
    ((TopCat.toSSet.obj twoVertices).ιChainComplex (vertex x)
      (R := ModuleCat.of ℚ ℚ) ≫
      (ModuleCat.ofHom indicator : (SingularChainComplex ℚ twoVertices).X 0 ⟶ ModuleCat.of ℚ ℚ)) 1 = _
  change ModuleCat.Hom.hom (Limits.Sigma.ι (fun _ => ModuleCat.of ℚ ℚ) (vertex x) ≫
    Limits.Sigma.desc (fun σ => ModuleCat.ofHom
      ((LinearMap.ringLmapEquivSelf ℚ ℚ ℚ).symm
        (if TopCat.toSSetObj₀Equiv σ = (0 : Fin 2) then 1 else 0)))) 1 = _
  rw [CategoryTheory.Limits.Sigma.ι_comp_desc]
  simp [vertex]

private def vertexClass : Cohomology ℚ twoVertices 0 := zeroIso.inv indicator

private theorem vertexClass_nonzero : vertexClass ≠ 0 := by
  intro h
  have he := congrArg (fun v => (show Module.Dual ℚ _ from zeroIso.hom v) (vertexChain 0)) h
  simp only [vertexClass, ← ModuleCat.comp_apply, Iso.inv_hom_id,
    ModuleCat.id_apply, map_zero] at he
  rw [indicator_vertex] at he
  norm_num at he



private theorem zeroIso_naturality :
    HomologicalComplex.homologyMap (singularCochainComplexMap ℚ exchange) 0 ≫
      zeroIso.hom = zeroIso.hom ≫ (singularCochainComplexMap ℚ exchange).f 0 := by
  dsimp only [zeroIso, Iso.trans_hom, Iso.symm_hom,
    HomologicalComplex.iCyclesIso_hom]
  rw [CochainComplex.isoHomologyπ₀_inv_naturality_assoc]
  change (SingularCochainComplex ℚ twoVertices).isoHomologyπ₀.inv ≫
    HomologicalComplex.cyclesMap (singularCochainComplexMap ℚ exchange) 0 ≫
      (SingularCochainComplex ℚ twoVertices).iCycles 0 = _
  rw [HomologicalComplex.cyclesMap_i]
  rfl

private theorem exchange_vertexChain (x : twoVertices) :
    ((singularChainComplexMap ℚ exchange).f 0).hom (vertexChain x) =
      vertexChain (exchange x) := by
  have he := SSet.ι_chainComplexMap_f _ _
    (TopCat.toSSet.map exchange) (ModuleCat.of ℚ ℚ) (vertex x)
  have hv : (TopCat.toSSet.map exchange).app _ (vertex x) = vertex (exchange x) := by
    apply TopCat.toSSetObj₀Equiv.injective
    change exchange (TopCat.toSSetObj₀Equiv (vertex x)) =
      TopCat.toSSetObj₀Equiv (vertex (exchange x))
    simp only [vertex, Equiv.apply_symm_apply]
  rw [hv] at he
  exact congrArg (fun f => f.hom 1) he

/-- The exchange changes an actual rational cohomology class in degree zero.
Source: Hatcher, Algebraic Topology, §3.1, degree-zero cohomology.
HC no distance; AV milestone no distance. -/
private theorem exchange_cohomology_nontrivial :
    cohomologyMap ℚ 0 exchange vertexClass ≠ vertexClass := by
  intro h
  have he := congrArg (fun v => (show Module.Dual ℚ _ from zeroIso.hom v)
    (vertexChain 0)) h
  have hn := congrArg (fun f => f.hom vertexClass) zeroIso_naturality
  change zeroIso.hom (cohomologyMap ℚ 0 exchange vertexClass) =
    (singularCochainComplexMap ℚ exchange).f 0 (zeroIso.hom vertexClass) at hn
  rw [hn] at he
  have hi : zeroIso.hom vertexClass = indicator := by
    change (zeroIso.inv ≫ zeroIso.hom).hom indicator = indicator
    rw [Iso.inv_hom_id]; rfl
  rw [hi] at he
  change indicator (((singularChainComplexMap ℚ exchange).f 0).hom (vertexChain 0)) =
    indicator (vertexChain 0) at he
  rw [exchange_vertexChain, indicator_vertex, indicator_vertex] at he
  norm_num [exchange, Equiv.swap_apply_left] at he


private def swapHomeomorph : twoVertices ≃ₜ twoVertices where
  toEquiv := Equiv.swap (0 : Fin 2) 1
  continuous_toFun := continuous_of_discreteTopology
  continuous_invFun := continuous_of_discreteTopology
private def supportedIndicator : CohomologyWithSupport ℚ twoVertices Set.univ 0 :=
  enlargeSupport ℚ twoVertices (Set.Subset.rfl :
    (Set.univ : Set twoVertices) ⊆ Set.univ) 0
      ((wholeSupportCohomologyLinearEquiv ℚ twoVertices 0).symm vertexClass)
private theorem forget_indicator :
    forgetSupport ℚ twoVertices Set.univ 0 supportedIndicator = vertexClass := by
  rw [supportedIndicator, enlargement_refl]
  exact (wholeSupportCohomologyLinearEquiv ℚ twoVertices 0).apply_symm_apply _
private theorem forget_naturality {X Y : TopCat.{0}} (n : ℕ)
    (f : X ⟶ Y) (Z : Set Y) (α : CohomologyWithSupport ℚ Y Z n) :
    cohomologyMap ℚ n f (forgetSupport ℚ Y Z n α) =
      forgetSupport ℚ X (f ⁻¹' Z) n (cohomologyWithSupportMap ℚ n f Z α) := by
  let a := preimageSupportPairMap f Z
  have hdual := congrArg HomologicalComplex.linearDualMap
    (TopPair.Homotopy.relativeChainProjection_naturality (R := ℚ) a)
  rw [HomologicalComplex.linearDualMap_comp, HomologicalComplex.linearDualMap_comp] at hdual
  have hhom := congrArg (fun u => HomologicalComplex.homologyMap u n) hdual
  rw [HomologicalComplex.homologyMap_comp, HomologicalComplex.homologyMap_comp] at hhom
  exact (ConcreteCategory.congr_hom hhom α).symm

private theorem forget_swap :
    forgetSupport ℚ twoVertices Set.univ 0
      (supportHomeomorphTransfer swapHomeomorph Set.univ 0 supportedIndicator) =
      cohomologyMap ℚ 0 exchange vertexClass := by
  rw [← forget_indicator]
  exact (forget_naturality 0 exchange Set.univ supportedIndicator).symm

/-- A nonidentity supported transport moves the indicator and rejects a stationary square.
Source: Hatcher, Algebraic Topology, section 3.1, naturality for maps of pairs.
HC no distance; AV milestone no distance. -/
private theorem check_exchange_transport :
    forgetSupport ℚ twoVertices Set.univ 0
      (supportHomeomorphTransfer swapHomeomorph Set.univ 0 supportedIndicator) =
      cohomologyMap ℚ 0 exchange
        (forgetSupport ℚ twoVertices Set.univ 0 supportedIndicator) ∧
    forgetSupport ℚ twoVertices Set.univ 0
      (supportHomeomorphTransfer swapHomeomorph Set.univ 0 supportedIndicator) ≠
      forgetSupport ℚ twoVertices Set.univ 0 supportedIndicator := by
  rw [forget_swap, forget_indicator]
  exact ⟨rfl, exchange_cohomology_nontrivial⟩
example := check_exchange_transport

private abbrev projectiveLine := f4_projectiveSpace 1
private instance retainedProjectiveLineIntegral : IsIntegral projectiveLine.left :=
  s0_complex_projective_integral 1
private instance retainedProjectiveLineProjective : IsProjective projectiveLine.hom :=
  s0_projective_space_projective 1 _
private def projectiveTowerMap : projectiveLine ⟶ projectiveLine :=
  retainedCycleModification (fun _ : Fin 2 => projectiveLine)
    (Iso.refl projectiveLine) (Iso.refl projectiveLine) (fun _ : Fin 1 => 𝟙 projectiveLine)
private theorem projectiveTowerMap_eq : projectiveTowerMap = 𝟙 projectiveLine := by
  simp only [projectiveTowerMap, retainedCycleModification, s2e_towerTotalMap,
    Iso.refl_inv, Category.id_comp]
  rfl

/-- A retained integral projective line tower has a restriction square on every nonempty
comparison open. The specified local transport preserves the nonzero unit; zero transport fails.
Source: Hatcher, Algebraic Topology, section 3.1; Hartshorne, II.7.
HC no distance; AV milestone no distance. -/
theorem check_retained_supported_transport
    (V : TopologicalSpace.Opens (ComplexPoint projectiveLine)) (x : V) :
    TopologicalSpace.dim projectiveLine.left = 1 ∧
    projectiveTowerMap = 𝟙 projectiveLine ∧
    ∃ hV : IsHomeomorph (retainedOpenMap projectiveTowerMap V),
      let XU := TopCat.of (Point.map projectiveTowerMap ⁻¹' (V : Set (ComplexPoint projectiveLine)))
      let jX : XU ⟶ a3b4_an projectiveLine.hom :=
        TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩
      let jY : TopCat.of V ⟶ a3b4_an projectiveLine.hom :=
        TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩
      (cohomologyWithSupportMap ℚ 0 jY Set.univ).comp
          (LinearMap.id : CohomologyWithSupport ℚ (a3b4_an projectiveLine.hom) Set.univ 0 →ₗ[ℚ]
            CohomologyWithSupport ℚ (a3b4_an projectiveLine.hom) Set.univ 0) =
        (retainedLocalTransport (X := projectiveLine) (Y := projectiveLine)
          projectiveTowerMap Set.univ Set.univ
          (by intro _ _; trivial) V hV 0).comp
            (cohomologyWithSupportMap ℚ 0 jX Set.univ) ∧
      (cohomologyWithSupportMap ℚ 0 jY Set.univ) ≠
        (0 : CohomologyWithSupport ℚ (a3b4_an projectiveLine.hom) Set.univ 0 →ₗ[ℚ]
          CohomologyWithSupport ℚ (TopCat.of V) Set.univ 0) := by
  refine ⟨s0_complex_projective_dimension 1, projectiveTowerMap_eq, ?_⟩
  rw [projectiveTowerMap_eq]
  let hV : IsHomeomorph (retainedOpenMap (𝟙 projectiveLine) V) := IsHomeomorph.id
  refine ⟨hV, ?_, ?_⟩
  · dsimp only
    rw [LinearMap.comp_id]
    unfold retainedLocalTransport supportHomeomorphTransfer enlargeSupport cohomologyWithSupportMap
    dsimp only
    rw [LinearMap.comp_assoc, ← relativeCohomologyMap_comp, ← relativeCohomologyMap_comp]
    congr 1
    ext y
    · exact (y.2 trivial).elim
    · exact congrArg Subtype.val ((hV.homeomorph (retainedOpenMap (𝟙 projectiveLine) V)).apply_symm_apply y).symm
  · letI : Nonempty V := ⟨x⟩
    let j : TopCat.of V ⟶ a3b4_an projectiveLine.hom :=
      TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩
    let a := (wholeSupportCohomologyLinearEquiv ℚ (a3b4_an projectiveLine.hom) 0).symm
      (HodgeLean.Foundations.Singular.unit (R := ℚ) (a3b4_an projectiveLine.hom))
    have hf : forgetSupport ℚ (a3b4_an projectiveLine.hom) Set.univ 0 a =
        HodgeLean.Foundations.Singular.unit (R := ℚ) (a3b4_an projectiveLine.hom) :=
      (wholeSupportCohomologyLinearEquiv ℚ (a3b4_an projectiveLine.hom) 0).apply_symm_apply _
    intro hzero
    have hh := forget_naturality 0 j Set.univ a
    rw [hzero] at hh
    change cohomologyMap ℚ 0 j (forgetSupport ℚ _ Set.univ 0 a) =
      forgetSupport ℚ _ (j ⁻¹' Set.univ) 0 (0 : CohomologyWithSupport ℚ (TopCat.of V) (j ⁻¹' Set.univ) 0) at hh
    rw [map_zero, hf,
      HodgeLean.Foundations.Singular.cohomologyMap_unit] at hh
    exact HodgeLean.Foundations.Singular.unit_ne_zero (R := ℚ) (TopCat.of V) hh
example := check_retained_supported_transport


#print axioms unitOnSupport_absolute
#print axioms unitSupported_absolute
#print axioms component_integral
#print axioms check_intrinsic_supported_integration_equation
#print axioms check_retained_supported_pushforward_equality

end HodgeLean.Foundations.QuotientDuality.RetainedCycleChecks
