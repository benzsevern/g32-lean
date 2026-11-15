import Mathlib.Topology.Compactification.OnePoint.Sphere
import HodgeLean.Foundations.QuotientDuality.SphereOrientationGeometry
import HodgeLean.Foundations.QuotientDuality.SphereChartInclusion
import HodgeLean.Foundations.QuotientDuality.LocalOrientationNaturality
import HodgeLean.Foundations.QuotientDuality.LocalTraceDefs
import HodgeLean.RealDefs.Port.AlgebraicTopology.LocalHomology.ChartFundamentalClassGenerator
import HodgeLean.Foundations.Singular.Cup
import HodgeLean.Foundations.Topology.RationalSheafComparison
import HodgeLean.Foundations.Program.SchoenCycleTowerHelpers
import HodgeLean.Foundations.AlgebraicTopology.Singular.PuncturedPlaneChecks

/-! # Connected orientation reversal under a deck involution

Complex conjugation gives the connected local countermodel on the folded plane.
HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Complex
open CategoryTheory AlgebraicTopology AlgebraicTopology.Singular HodgeLean.Adapters
open HodgeLean.Foundations.Program
open scoped Manifold ContDiff ComplexConjugate OnePoint
namespace HodgeLean.Foundations.QuotientDuality.RetainedTraceChecks
open AlgebraicTopology.Singular.PuncturedPlane

private theorem degree_transport {M N : Type} [TopologicalSpace M] [TopologicalSpace N]
    [T1Space N] [ChartedSpace ℂ M] [ChartedSpace ℂ N] (e : M ≃ₜ N) (x : M) :
    relativeHomologyMap ℤ 2
      (imagePointPairMap (TopCat.ofHom ⟨e, e.continuous⟩) e.injective x) (localClass x) =
        localDegree e x • localClass (e x) := by
  rw [← int_smul_eq_zsmul (ModuleCat.isModule _) (localDegree e x)]
  exact ((Equiv.ofBijective _ (b6m_surfaceLocalClass_smul_bijective ℤ (e x))).apply_symm_apply _).symm

private def imagePairAt {M N : Type} [TopologicalSpace M] [TopologicalSpace N]
    (e : M ≃ₜ N) (x : M) (y : N) (h : e x = y) :
    pointComplementPair x ⟶ pointComplementPair y :=
  imagePointPairMap (TopCat.ofHom ⟨e, e.continuous⟩) e.injective x ≫
    eqToHom (congrArg pointComplementPair h)

private theorem imagePairAt_left {M N : Type} [TopologicalSpace M] [TopologicalSpace N]
    (e : M ≃ₜ N) (x : M) (y : N) (h : e x = y) (z : (pointComplementPair x).snd) :
    ((imagePairAt e x y h).left z).val = e z.val := by
  cases h
  rfl

private theorem imagePairAt_right {M N : Type} [TopologicalSpace M] [TopologicalSpace N]
    (e : M ≃ₜ N) (x : M) (y : N) (h : e x = y) (z : M) :
    (imagePairAt e x y h).hom.right z = e z := by
  cases h
  rfl

private theorem degree_transport_at {M N : Type} [TopologicalSpace M] [TopologicalSpace N]
    [T1Space N] [ChartedSpace ℂ M] [ChartedSpace ℂ N]
    (e : M ≃ₜ N) (x : M) (y : N) (h : e x = y) :
    relativeHomologyMap ℤ 2 (imagePairAt e x y h) (localClass x) =
      localDegree e x • localClass y := by
  cases h
  unfold imagePairAt
  rw [eqToHom_refl, Category.comp_id]
  exact degree_transport e x

private theorem conjugation_degree : localDegree Complex.conjCLE.toHomeomorph 0 = -1 := by
  let e := Complex.conjCLE.toHomeomorph
  have he0 : e 0 = 0 := map_zero Complex.conjCLE
  let F := imagePairAt e 0 0 he0
  have ht := degree_transport_at e 0 0 he0
  have h : (-1 : ℤ) = localDegree e 0 := s2v_l1b_action_deck_local_sign
    F (fun z : ℂ => conj z) Complex.continuous_conj ?_ (-1) ?_
    (localDegree e 0) ht
  · exact h.symm
  · intro z
    rw [show (F.left ⟨Complex.exp z, Complex.exp_ne_zero z⟩).val = e (Complex.exp z) from
      imagePairAt_left e 0 0 he0 _]
    exact Complex.exp_conj z
  · intro z
    simp only [map_add, map_mul, map_ofNat, Complex.conj_ofReal, Complex.conj_I,
      Int.cast_neg, Int.cast_one, neg_one_mul, mul_neg]


/-- Connected local countermodel: connectedness does not force preservation of local orientations.
Source: Hatcher, Algebraic Topology, section 2.2, degree of a reflection;
docs/notes/native-inputs/s2e-chain-contract.md:659–668. -/
theorem connected_deck_orientation_falsification :
    ConnectedSpace ℂ ∧
    Function.Involutive Complex.conjCLE.toHomeomorph ∧
    Continuous (fun z : ℂ => (z.re : ℂ) + ((|z.im| : ℝ) : ℂ) * Complex.I) ∧
    (∀ z : ℂ, ((conj z).re : ℂ) + ((|(conj z).im| : ℝ) : ℂ) * Complex.I =
      (z.re : ℂ) + ((|z.im| : ℝ) : ℂ) * Complex.I) ∧
    localDegree Complex.conjCLE.toHomeomorph (0 : ℂ) = (-1 : ℤ) ∧
    relativeHomologyMap ℤ 2
      (imagePointPairMap (TopCat.ofHom
        ⟨Complex.conjCLE.toHomeomorph, Complex.conjCLE.continuous⟩)
        Complex.conjCLE.toHomeomorph.injective (0 : ℂ))
      (localClass (0 : ℂ)) ≠
        localClass (Complex.conjCLE.toHomeomorph (0 : ℂ)) := by
  refine ⟨inferInstance, ?_, ?_, ?_, conjugation_degree, ?_⟩
  · intro z
    exact Complex.conj_conj z
  · exact (Complex.continuous_ofReal.comp Complex.continuous_re).add
      ((Complex.continuous_ofReal.comp (continuous_abs.comp Complex.continuous_im)).mul
        continuous_const)
  · intro z
    simp only [Complex.conj_re, Complex.conj_im, abs_neg]
  · intro he
    have hd : localDegree Complex.conjCLE.toHomeomorph (0 : ℂ) = (1 : ℤ) := by
      unfold localDegree
      rw [he]
      have hcoeff (x : ℂ) (n : ℤ) : localCoefficient x (n • localClass x) = n := by
        rw [← int_smul_eq_zsmul (ModuleCat.isModule _) n]
        exact (Equiv.ofBijective _ (b6m_surfaceLocalClass_smul_bijective ℤ x)).symm_apply_apply n
      simpa only [one_smul] using hcoeff (Complex.conjCLE.toHomeomorph (0 : ℂ)) (1 : ℤ)

    rw [conjugation_degree] at hd
    norm_num at hd

example := connected_deck_orientation_falsification

#print axioms connected_deck_orientation_falsification

private abbrev P := TopCat.of Unit
private def c : Homology ℚ P 0 :=
  (asIso (P.singularHomology₀ε (ModuleCat.of ℚ ℚ))).inv.hom (1 : ℚ)
private def u : Cohomology ℚ P 0 := cohomologyUnitZero ℚ P
private theorem eval_one : orientationIntegral P 0 c u = 1 := by
  change cohomologyEquivDualHomology ℚ P 0 (cohomologyUnitZero ℚ P) _ = _
  rw [cohomologyEquivDualHomology_cohomologyUnitZero]
  exact LinearMap.congr_fun
    (congrArg ModuleCat.Hom.hom (Iso.inv_hom_id
      (asIso (P.singularHomology₀ε (ModuleCat.of ℚ ℚ))))) 1
private theorem c_ne : c ≠ 0 := by
  intro h
  have he := eval_one
  rw [h] at he
  simp [orientationIntegral] at he


/-- The point model detects a change in the trace normalization.
Source: Hatcher, Algebraic Topology, section 3.3, evaluation on a fundamental class. -/
theorem retained_normalized_trace_model :
    orientationIntegral P 0 c u = (1 : ℚ) ∧
    orientationIntegral P 0 ((2 : ℚ) • c) u ≠ (1 : ℚ) := by
  refine ⟨eval_one, ?_⟩
  change cohomologyEquivDualHomology ℚ P 0 u ((2 : ℚ) • c) ≠ (1 : ℚ)
  rw [map_smul]
  change (2 : ℚ) * orientationIntegral P 0 c u ≠ (1 : ℚ)
  rw [eval_one]
  norm_num

example := retained_normalized_trace_model

private def totalPointMap : P ⟶ P :=
  s2e_towerTotalMap (fun _ : Fin ((0 : ℕ) + 1) => P) (𝟙 P)
    (fun i : Fin (0 : ℕ) => Fin.elim0 i) 0

/-- The zero-step retained tower uses the actual total-map construction and preserves a nonzero class.
Source: Hatcher, Algebraic Topology, section 2.2, degree of the identity;
Program/SchoenCycleTowerHelpers.lean:12. -/
theorem retained_modification_model :
    c ≠ 0 ∧ homologyMap ℚ 0 totalPointMap c = c ∧
    orientationIntegral P 0 c (cohomologyMap ℚ 0 totalPointMap u) = (1 : ℚ) := by
  refine ⟨c_ne, ?_, ?_⟩
  · change homologyMap ℚ 0 (𝟙 P) c = c
    rw [homologyMap_id]
    rfl
  · change orientationIntegral P 0 c (cohomologyMap ℚ 0 (𝟙 P) u) = (1 : ℚ)
    rw [cohomologyMap_id]
    exact eval_one

example := retained_modification_model

/-- The actual singular cup detects a misplaced scalar factor on nonzero degree-zero classes.
Source: Hatcher, Algebraic Topology, section 3.2, constant cup classes. -/
theorem retained_cup_comparison_falsification :
    HodgeLean.Foundations.Singular.cup (R := ℚ) P (p := 0) (q := 0) (k := 0) rfl
      ((2 : ℚ) • HodgeLean.Foundations.Singular.unit (R := ℚ) P)
      ((3 : ℚ) • HodgeLean.Foundations.Singular.unit (R := ℚ) P) ≠
      (3 : ℚ) • HodgeLean.Foundations.Singular.unit (R := ℚ) P := by
  rw [HodgeLean.Foundations.Singular.cup_constants]
  intro he
  have hz : (3 : ℚ) • HodgeLean.Foundations.Singular.unit (R := ℚ) P = 0 := by
    calc
      (3 : ℚ) • HodgeLean.Foundations.Singular.unit (R := ℚ) P =
          ((2 : ℚ) * 3 - 3) • HodgeLean.Foundations.Singular.unit (R := ℚ) P := by norm_num
      _ = 0 := by rw [sub_smul, he, sub_self]
  exact HodgeLean.Foundations.Singular.unit_ne_zero (R := ℚ) P
    ((smul_eq_zero.mp hz).resolve_left (by norm_num))

example := retained_cup_comparison_falsification

private theorem point_basis (x : P) (U : TopologicalSpace.Opens P) (hx : x ∈ U) :
    ∃ V : TopologicalSpace.Opens P, x ∈ V ∧ ContractibleSpace V ∧ V ≤ U := by
  haveI : Nonempty U := ⟨⟨x, hx⟩⟩
  exact ⟨U, hx, inferInstance, le_rfl⟩

/-- The canonical M1 comparison on a constructed M2 basis retains a nonzero unit and its identity square.
Source: Bredon, Sheaf Theory, II.4, II.6, III.1. -/
theorem retained_rational_comparison_model :
    HodgeLean.Topology.RationalSheafComparison.comparison P point_basis 0
      (HodgeLean.Foundations.Singular.unit (R := ℚ) P) ≠ 0 ∧
    HodgeLean.Topology.RationalSheafComparison.comparison P point_basis 0
      (cohomologyMap ℚ 0 totalPointMap (HodgeLean.Foundations.Singular.unit (R := ℚ) P)) =
    HodgeLean.Topology.RationalSheafComparison.sheafPullback totalPointMap 0
      (HodgeLean.Topology.RationalSheafComparison.comparison P point_basis 0
        (HodgeLean.Foundations.Singular.unit (R := ℚ) P)) := by
  refine ⟨?_, ?_⟩
  · intro he
    exact HodgeLean.Foundations.Singular.unit_ne_zero (R := ℚ) P
      ((HodgeLean.Topology.RationalSheafComparison.comparison_linearEquiv P point_basis 0).1.1
        (he.trans (map_zero (HodgeLean.Topology.RationalSheafComparison.comparison P point_basis 0)).symm))
  · exact HodgeLean.Topology.RationalSheafComparison.comparison_naturality
      P point_basis P point_basis totalPointMap 0 _

example := retained_rational_comparison_model

#print axioms retained_normalized_trace_model
#print axioms retained_modification_model
#print axioms retained_cup_comparison_falsification
#print axioms retained_rational_comparison_model


private abbrev chartClass :=
  localClassOfChart 1 (OpenPartialHomeomorph.refl (Fin (1 : ℕ) → ℂ))
    (0 : Fin (1 : ℕ) → ℂ) (by trivial)

/-- The smooth complex line has a nonzero actual rational chart class whose normalization detects doubling.
Source: Hatcher, Algebraic Topology, section 3.3, complex chart orientations. -/
theorem retained_smooth_chart_model :
    chartClass ≠ 0 ∧ (2 : ℚ) • chartClass ≠ chartClass := by
  have hn : chartClass ≠ 0 := localClassOfChart_ne_zero 1
    (OpenPartialHomeomorph.refl (Fin (1 : ℕ) → ℂ)) (0 : Fin (1 : ℕ) → ℂ) (by trivial)
  refine ⟨hn, ?_⟩
  intro he
  have hz : chartClass + chartClass = chartClass + 0 := by
    simpa only [two_smul, add_zero] using he
  exact hn (add_left_cancel hz)

example := retained_smooth_chart_model
#print axioms retained_smooth_chart_model

private abbrev SphereModel := TopCat.of (OnePoint ℂ)
private abbrev SphereDeck := OnePoint ℂ ≃ₜ OnePoint ℂ
private def sphereReflection : SphereDeck := Complex.conjCLE.toHomeomorph.onePointCongr

private theorem sphereReflection_involutive : Function.Involutive sphereReflection := by
  intro x
  cases x using OnePoint.rec with
  | infty => rfl
  | coe z => change (↑(conj (conj z)) : OnePoint ℂ) = ↑z; rw [Complex.conj_conj]

private def sphereHomeomorph : OnePoint ℂ ≃ₜ
    Metric.sphere (0 : EuclideanSpace ℝ (Fin (3 : ℕ))) (1 : ℝ) :=
  onePointEquivSphereOfFinrankEq (by simp)

example : sphereReflection (OnePoint.infty : OnePoint ℂ) =
    (OnePoint.infty : OnePoint ℂ) := rfl

example : sphereReflection (↑Complex.I : OnePoint ℂ) ≠ (↑Complex.I : OnePoint ℂ) := by
  change (↑(conj Complex.I) : OnePoint ℂ) ≠ ↑Complex.I
  intro he
  have hi : -Complex.I = Complex.I := by
    simpa only [Complex.conj_I] using OnePoint.coe_injective he
  have him := congrArg Complex.im hi
  norm_num at him

example : Function.Bijective sphereHomeomorph := sphereHomeomorph.bijective

private theorem sphere_model_topology :
    CompactSpace SphereModel ∧ T2Space SphereModel ∧ ConnectedSpace SphereModel :=
  ⟨inferInstance, inferInstance, inferInstance⟩

attribute [local instance] b4cov_sphChartedSpace

private theorem sphere_reflection_local :
    ∃ F : pointComplementPair ((0 : ℂ) : OnePoint ℂ) ⟶
        pointComplementPair ((0 : ℂ) : OnePoint ℂ),
      F.hom.right = TopCat.ofHom ⟨sphereReflection, sphereReflection.continuous⟩ ∧
      relativeHomologyMap ℚ 2 F (sphereLocalOrientation.generator ((0 : ℂ) : OnePoint ℂ)) =
        -sphereLocalOrientation.generator ((0 : ℂ) : OnePoint ℂ) := by
  let e := Complex.conjCLE.toHomeomorph
  have he0 : e 0 = 0 := map_zero Complex.conjCLE
  have hH0 : sphereReflection ((0 : ℂ) : OnePoint ℂ) = ((0 : ℂ) : OnePoint ℂ) := by
    change ((conj (0 : ℂ) : ℂ) : OnePoint ℂ) = ((0 : ℂ) : OnePoint ℂ)
    rw [map_zero]
  let P := imagePairAt e 0 0 he0
  let F := imagePairAt sphereReflection ((0 : ℂ) : OnePoint ℂ) ((0 : ℂ) : OnePoint ℂ) hH0
  have hP : relativeHomologyMap ℤ 2 P (b6m_surfaceLocalClass ℤ (0 : ℂ)) =
      -b6m_surfaceLocalClass ℤ (0 : ℂ) := by
    have ht := degree_transport_at e 0 0 he0
    rw [conjugation_degree] at ht
    simpa only [neg_one_zsmul] using ht
  have hPQ := surface_local_neg_of_integral (0 : ℂ) (0 : ℂ) P hP
  have hcomm : P ≫ spherePlanePair = spherePlanePair ≫ F := by
    apply MorphismProperty.Arrow.Hom.ext
    · ext z
      apply Subtype.ext
      change ((P.left z).val : OnePoint ℂ) = (F.left (spherePlanePair.left z)).val
      rw [imagePairAt_left, imagePairAt_left]
      rfl
    · ext z
      change spherePlaneInclusion (P.hom.right z) = F.hom.right (spherePlaneInclusion z)
      rw [imagePairAt_right, imagePairAt_right]
      rfl
  refine ⟨F, ?_, ?_⟩
  · ext z
    exact imagePairAt_right sphereReflection _ _ hH0 z
  · rw [sphereLocalOrientation_generator,
      ← sphere_plane_localClass ℚ]
    rw [← LinearMap.comp_apply, ← relativeHomologyMap_comp, ← hcomm,
      relativeHomologyMap_comp, LinearMap.comp_apply, hPQ, map_neg]

/-- Rational sphere construction target for the compact reflection test.
Source: Hatcher, Algebraic Topology, Theorems 2.26 and 3.26 and section 2.2,
degree of a reflection. -/
private theorem sphere_reflection_geometry :
    ∃ (a : ℕ) (K : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin a)))
      (hK : K.faces.Finite) (eK : K.space ≃ₜ SphereModel)
      (o : LocalRationalOrientation SphereModel 2) (c : Homology ℚ SphereModel 2),
      (∀ x, localOrientation SphereModel 2 c x = o.generator x) ∧
      homologyMap ℚ 2 (deckMap SphereDeck SphereModel sphereReflection) c = -c := by
  obtain ⟨K, hK, ⟨eK⟩⟩ := sphere_finite_triangulation
  obtain ⟨c, hc, hgen⟩ := sphere_surface_fundamental
  refine ⟨3, K, hK, eK, sphereLocalOrientation, c, hc, ?_⟩
  obtain ⟨F, hF, hneg⟩ := sphere_reflection_local
  have hdeck : deckMap SphereDeck SphereModel sphereReflection =
      TopCat.ofHom ⟨sphereReflection, sphereReflection.continuous⟩ := by
    ext z
    change sphereReflection.symm z = sphereReflection z
    apply sphereReflection.injective
    rw [sphereReflection.apply_symm_apply, sphereReflection_involutive]
  obtain ⟨q, hq⟩ := hgen.2 (homologyMap ℚ 2 (deckMap SphereDeck SphereModel sphereReflection) c)
  change q • c = _ at hq
  let x : SphereModel := ((0 : ℂ) : OnePoint ℂ)
  have hloc : localOrientation SphereModel 2 (q • c) x =
      -sphereLocalOrientation.generator x := by
    erw [hq]
    have hn := localOrientation_map 2 x x F c
    rw [hF, ← hdeck] at hn
    exact hn.symm.trans ((congrArg (relativeHomologyMap ℚ 2 F) (hc x)).trans hneg)
  have he : q • sphereLocalOrientation.generator x =
      (-1 : ℚ) • sphereLocalOrientation.generator x := by
    change q • sphereLocalOrientation.generator x = _
    have hs : localOrientation SphereModel 2 (q • c) x =
        q • sphereLocalOrientation.generator x := by
      change (relativeHomologyProjection ℚ (pointComplementPair x) 2).hom (q • c) = _
      rw [map_smul]
      exact congrArg (q • ·) (hc x)
    rw [← hs, hloc, neg_one_smul]
  have hqneg : q = -1 := (sphereLocalOrientation.generates x).1 he
  rw [← hq, hqneg]
  exact neg_one_smul ℚ c

#print axioms sphere_reflection_geometry

/-- Reflection reverses rational trace on the compact connected two-sphere.
The construction target retains every other input of `local_deck_trace_pairing`,
with p = 0 and q = 2. The sphere geometry body is listed separately.
Source: Hatcher, Algebraic Topology, sections 2.2 and 3.3. -/
theorem local_deck_trace_pairing_sphere_falsification :
    CompactSpace SphereModel ∧ T2Space SphereModel ∧ ConnectedSpace SphereModel ∧
    Function.Involutive sphereReflection ∧
    ∃ (a : ℕ) (K : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin a)))
      (hK : K.faces.Finite) (eK : K.space ≃ₜ SphereModel)
      (o : LocalRationalOrientation SphereModel (0 + 2))
      (c : Homology ℚ SphereModel (0 + 2)) (u : Cohomology ℚ SphereModel (0 + 2)),
      (∀ x, localOrientation SphereModel (0 + 2) c x = o.generator x) ∧
      orientationIntegral SphereModel (0 + 2) c u = (1 : ℚ) ∧
      orientationIntegral SphereModel (0 + 2) c
        (deckRepresentation SphereDeck SphereModel (0 + 2) sphereReflection u) = (-1 : ℚ) ∧
      orientationIntegral SphereModel (0 + 2) c
        (deckRepresentation SphereDeck SphereModel (0 + 2) sphereReflection u) ≠
        orientationIntegral SphereModel (0 + 2) c u := by
  obtain ⟨a, K, hK, eK, o, c, hc, hr⟩ := sphere_reflection_geometry
  have hcne : c ≠ 0 := by
    intro hz
    have hg : o.generator (OnePoint.infty : OnePoint ℂ) = 0 := by
      rw [← hc, hz]
      exact map_zero _
    have he := (o.generates (OnePoint.infty : OnePoint ℂ)).1
      (show LinearMap.toSpanSingleton ℚ _ (o.generator (OnePoint.infty : OnePoint ℂ))
          (0 : ℚ) = LinearMap.toSpanSingleton ℚ _
          (o.generator (OnePoint.infty : OnePoint ℂ)) (1 : ℚ) by simp [hg])
    exact zero_ne_one he
  obtain ⟨φ, hφ⟩ := Module.Projective.exists_dual_eq_one ℚ hcne
  let u := (cohomologyEquivDualHomology ℚ SphereModel 2).symm φ
  have hu : orientationIntegral SphereModel 2 c u = (1 : ℚ) := by
    change cohomologyEquivDualHomology ℚ SphereModel 2
      ((cohomologyEquivDualHomology ℚ SphereModel 2).symm φ) c = (1 : ℚ)
    rw [LinearEquiv.apply_symm_apply, hφ]
  obtain ⟨hcompact, ht2, hconnected⟩ := sphere_model_topology
  refine ⟨hcompact, ht2, hconnected, sphereReflection_involutive,
    a, K, hK, eK, o, c, u, hc, hu, ?_, ?_⟩
  · change cohomologyEquivDualHomology ℚ SphereModel 2
      (cohomologyMap ℚ 2 (deckMap SphereDeck SphereModel sphereReflection) u) c = _
    rw [cohomologyEquivDualHomology_cohomologyMap, hr, map_neg]
    change -orientationIntegral SphereModel 2 c u = (-1 : ℚ)
    rw [hu]
  · change cohomologyEquivDualHomology ℚ SphereModel 2
      (cohomologyMap ℚ 2 (deckMap SphereDeck SphereModel sphereReflection) u) c ≠ _
    rw [cohomologyEquivDualHomology_cohomologyMap, hr, map_neg]
    change -orientationIntegral SphereModel 2 c u ≠ orientationIntegral SphereModel 2 c u
    rw [hu]
    norm_num

example : Function.Involutive sphereReflection := sphereReflection_involutive

#print axioms local_deck_trace_pairing_sphere_falsification

end HodgeLean.Foundations.QuotientDuality.RetainedTraceChecks
