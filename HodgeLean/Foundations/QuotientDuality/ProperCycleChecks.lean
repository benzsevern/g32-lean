import HodgeLean.Foundations.QuotientDuality.ProperCycleDefs
import Other.AlgebraicTopology.Singular.SupportNaturality
import HodgeLean.Adapters.NormalConeB4aClassExistsPure
import HodgeLean.Adapters.NormalConeB4aClassUniqueBoundary
import HodgeLean.RealDefs.DegreeZero

/-! # Independent multiplicity and proper transfer checks

Nonzero supported classes and actual singular cup products detect altered
multiplicities, orientations, test spaces and coefficient sums.
HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry AlgebraicTopology.Singular
open HodgeLean.Adapters HodgeLean.Foundations.Program
open HodgeLean.Foundations.Analytic HodgeLean.RealDefs
open scoped BigOperators
namespace HodgeLean.Foundations.QuotientDuality.ProperCycleChecks

private abbrev point : Over (Spec ↧ℂ) := Over.mk (𝟙 (Spec ↧ℂ))
private instance properCyclePointNonempty : Nonempty (ComplexPoint point) := ⟨𝟙 point⟩
private instance properCyclePointIntegral : IsIntegral point.left :=
  inferInstanceAs (IsIntegral (Spec (CommRingCat.of ℂ)))
private instance properCyclePointDecidable : DecidableEq point.left := Classical.decEq _

private instance properCyclePointUnique : Unique (ComplexPoint point) where
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
  (properPrime (genericPoint point.left)).mapRange ((2 : ℚ) * ·) (mul_zero _)
private theorem orbit_eq : weightedPrime = Function.locallyFinsuppWithin.single
    (genericPoint point.left) (2 : ℚ) := by
  classical
  ext x
  by_cases h : x = genericPoint point.left <;> simp [weightedPrime, properPrime, h]
private theorem zero_pair_orbit_coefficient :
    weightedPrime (genericPoint point.left) = (2 : ℚ) := by
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
  have hm : a3b4_multiplicity point.hom weightedPrime x = (2 : ℚ) := by
    classical
    have hc : weightedPrime = Function.locallyFinsuppWithin.single
        (genericPoint point.left) (2 : ℚ) := by
      exact orbit_eq
    have hcoeff : weightedPrime (genericPoint point.left) = (2 : ℚ) := by
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
  exact (smul_ne_zero (by norm_num : (2 : ℚ) ≠ 0) hn) hnorm.symm

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
private abbrev line := a1p_affineLine
private instance properCycleLineIntegral : IsIntegral line.left := by
  change IsIntegral (Spec (CommRingCat.of (Polynomial ℂ)))
  infer_instance
private def origin : line.left :=
  PrimeSpectrum.comap (Polynomial.evalRingHom (0 : ℂ)) ⟨⊥, inferInstance⟩
private theorem origin_coheight : (1 : ℕ∞) ≤ Order.coheight origin := by
  have hne : origin ≠ genericPoint line.left := by
    intro h
    have hx : Polynomial.X ∈ origin.asIdeal := by
      change Polynomial.eval (0 : ℂ) Polynomial.X ∈ (⊥ : Ideal ℂ)
      simp only [Polynomial.eval_X, Ideal.mem_bot]
    rw [h, show (genericPoint line.left).asIdeal = ⊥ from
      a1p_affineLineGeneric_asIdeal, Ideal.mem_bot] at hx
    exact Polynomial.X_ne_zero hx
  have hlt : origin < (⊤ : line.left) := lt_of_le_not_ge le_top (fun h =>
    hne ((genericPoint_specializes origin).antisymm h).eq.symm)
  simpa using Order.coheight_add_one_le hlt
private abbrev squareFibreIdeal : Ideal (Polynomial ℂ) := Ideal.span {Polynomial.X ^ 2}
private def ramifiedParameter : (Polynomial ℂ) ⧸ squareFibreIdeal :=
  Ideal.Quotient.mk squareFibreIdeal Polynomial.X
private theorem square_fibre_parameter :
    ramifiedParameter ≠ 0 ∧ ramifiedParameter ^ 2 = 0 := by
  constructor
  · intro h
    have hm := (Ideal.Quotient.eq_zero_iff_mem).mp h
    have hd : (Polynomial.X ^ 2 : (Polynomial ℂ)) ∣ Polynomial.X :=
      Ideal.mem_span_singleton.mp hm
    have hn := Polynomial.natDegree_le_of_dvd hd Polynomial.X_ne_zero
    norm_num only [Polynomial.natDegree_X, Polynomial.natDegree_pow] at hn
  · change (Ideal.Quotient.mk squareFibreIdeal Polynomial.X) ^ 2 = 0
    rw [← map_pow]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton _))

/-- The ramified square fibre has a nonzero nilpotent at a positive-coheight point.
Source: Fulton, Intersection Theory, sections 1.4 and 2.3.
HC no distance; AV milestone no distance. -/
theorem check_proper_prime_pushforward_ramification :
    Polynomial.aeval (Polynomial.X ^ 2 : Polynomial ℂ) (Polynomial.X : Polynomial ℂ) =
      (Polynomial.X ^ 2 : Polynomial ℂ) ∧
    ramifiedParameter ≠ 0 ∧ ramifiedParameter ^ 2 = 0 ∧
    (1 : ℕ∞) ≤ Order.coheight origin ∧
    Order.coheight (a1p_squareMap.left a1p_affineLineGeneric) =
      Order.coheight a1p_affineLineGeneric := by
  exact ⟨Polynomial.aeval_X _, square_fibre_parameter.1, square_fibre_parameter.2,
    origin_coheight, congrArg Order.coheight a1p_squareMap_generic⟩
example := check_proper_prime_pushforward_ramification

/-- A genuine quadratic residue extension doubles the coefficient of the prime.
Source: Fulton, Intersection Theory, section 1.4.
HC no distance; AV milestone no distance. -/
theorem check_proper_prime_pushforward :
    a1p_pushforward a1p_squareMap.left (properPrime a1p_affineLineGeneric)
      (a1p_squareMap.left a1p_affineLineGeneric) = (2 : ℚ) ∧
    a1p_pushforward a1p_squareMap.left (properPrime a1p_affineLineGeneric)
      (a1p_squareMap.left a1p_affineLineGeneric) ≠ (1 : ℚ) := by
  classical
  rw [properPrime, a1p_pushforward_single, a1p_degree_square_eq_two]
  norm_num
example := check_proper_prime_pushforward

private instance properCycleLineSmooth : Smooth line.hom := by
  apply (HasRingHomProperty.Spec_iff (P := @Smooth)).mpr
  change (algebraMap ℂ (Polynomial ℂ)).Smooth
  exact RingHom.smooth_algebraMap.mpr ⟨inferInstance, inferInstance⟩
private instance properCycleLineQuasiCompact : QuasiCompact line.hom := by
  change QuasiCompact (Spec.map (CommRingCat.ofHom (algebraMap ℂ (Polynomial ℂ))))
  infer_instance
private instance properCycleLineSeparated : IsSeparated line.hom := by
  change IsSeparated (Spec.map (CommRingCat.ofHom (algebraMap ℂ (Polynomial ℂ))))
  infer_instance

/-- The quadratic residue-degree model carries normalized source and image classes.
Source: Fulton, Intersection Theory, sections 1.4 and 19.1.
HC no distance; AV milestone no distance. -/
theorem check_proper_prime_pushforward_supported :
    ∃ (a : s2e_supportedClass line (properPrime a1p_affineLineGeneric) 0)
      (b : s2e_supportedClass line
        (a1p_pushforward a1p_squareMap.left (properPrime a1p_affineLineGeneric)) 0),
      a3b4_IsCycleClass line.hom (properPrime a1p_affineLineGeneric) 0 a ∧
      a3b4_IsCycleClass line.hom
        (a1p_pushforward a1p_squareMap.left (properPrime a1p_affineLineGeneric)) 0 b ∧
      a1p_pushforward a1p_squareMap.left (properPrime a1p_affineLineGeneric)
        (a1p_squareMap.left a1p_affineLineGeneric) = (2 : ℚ) ∧
      a1p_pushforward a1p_squareMap.left (properPrime a1p_affineLineGeneric)
        (a1p_squareMap.left a1p_affineLineGeneric) ≠ (1 : ℚ) := by
  obtain ⟨a, ha⟩ := a3b4a_cycleClass_exists_of_codimension line.hom
    (properPrime a1p_affineLineGeneric) 0 (fun _ _ => bot_le)
  obtain ⟨b, hb⟩ := a3b4a_cycleClass_exists_of_codimension line.hom
    (a1p_pushforward a1p_squareMap.left (properPrime a1p_affineLineGeneric))
    0 (fun _ _ => bot_le)
  exact ⟨a, b, ha, hb, check_proper_prime_pushforward⟩
example := check_proper_prime_pushforward_supported

private theorem fixed_coordinates_ne : E fixedAbsolute ≠ 0 := by
  intro h
  exact fixedAbsolute_ne_zero (E_injective (h.trans (map_zero E).symm))

private theorem normalized_unique (a b : s2e_supportedClass point weightedPrime 0)
    (ha : a3b4_IsCycleClass point.hom weightedPrime 0 a)
    (hb : a3b4_IsCycleClass point.hom weightedPrime 0 b) : a = b := by
  apply a3b4a_cycleClass_unique_of_regularBoundary point.hom weightedPrime 0
    (fun _ _ => bot_le) (⊥ : TopologicalSpace.Closeds point.left)
    bot_le (by intro z hz; exact hz.elim) ?_ a b ha hb
  intro x hx _
  refine ⟨0, pointChart, ?_, ?_, ?_⟩
  · change x ∈ Set.univ; trivial
  · exact ⟨fun j => Fin.elim0 j, fun j => Fin.elim0 j⟩
  · intro y hy
    rw [zero_pair_full_support]
    exact iff_of_true (Set.mem_univ _) (Subsingleton.elim _ _)

private theorem doubled_ne {M : Type} [AddCommGroup M] [Module ℚ M]
    (v : M) (hv : v ≠ 0) : v ≠ (2 : ℚ) • v := by
  intro h
  have hh : v + v = 0 + v := by simpa only [two_smul, zero_add] using h.symm
  exact hv (add_right_cancel hh)

/-- The actual algebraic prime class has a fixed local Thom normalization.
Source: Fulton, Intersection Theory, section 19.1; Bott–Tu, sections 5–6.
HC no distance; AV milestone no distance. -/
theorem check_proper_prime_thom :
    a3b4_IsCycleClass point.hom weightedPrime 0 fixedSupported ∧
    fixedSupported ≠ 0 ∧
    ¬ a3b4_IsCycleClass point.hom weightedPrime 0 ((2 : ℚ) • fixedSupported) := by
  refine ⟨fixedSupported_normalized, fixedSupported_ne_zero, ?_⟩
  intro h
  exact doubled_ne fixedSupported fixedSupported_ne_zero
    (normalized_unique _ _ fixedSupported_normalized h)
example := check_proper_prime_thom

/-- Projection tests the absolute image of an actual normalized supported cycle.
Source: Fulton, Intersection Theory, section 19.2.
HC no distance; AV milestone no distance. -/
theorem check_proper_cycle_projection :
    a1p_pushforward (𝟙 point.left) weightedPrime = weightedPrime ∧
    (∀ a : Cohomology ℚ P 0, properCyclePairing P 0 c fixedAbsolute a =
      properCyclePairing P 0 c fixedAbsolute
        (cohomologyMap ℚ 0 (TopCat.ofHom (Point.continuousMap (𝟙 point))) a)) ∧
    properCyclePairing P 0 c fixedAbsolute u ≠
      properCyclePairing P 0 c ((2 : ℚ) • fixedAbsolute) u := by
  refine ⟨a1p_pushforward_id _, ?_, ?_⟩
  · intro a
    change _ = properCyclePairing P 0 c fixedAbsolute (cohomologyMap ℚ 0 (𝟙 P) a)
    rw [cohomologyMap_id, LinearMap.id_apply]
  · rw [pair_value, pair_value, map_smul, E_unit, mul_one, mul_one]
    exact doubled_ne (E fixedAbsolute) fixed_coordinates_ne
example := check_proper_cycle_projection

/-- The cup adjoint retains the normalized algebraic class and rejects doubling.
Source: Fulton, Intersection Theory, section 19.2; linear duality.
HC no distance; AV milestone no distance. -/
theorem check_proper_cycle_adjoint :
    s2e_pairingAdjoint (properCyclePairing P 0 c) perfect
      (properCyclePairing P 0 c)
      (cohomologyMap ℚ 0 (TopCat.ofHom (Point.continuousMap (𝟙 point))))
      fixedAbsolute = fixedAbsolute ∧
    s2e_pairingAdjoint (properCyclePairing P 0 c) perfect
      (properCyclePairing P 0 c)
      (cohomologyMap ℚ 0 (TopCat.ofHom (Point.continuousMap (𝟙 point))))
      fixedAbsolute ≠ (2 : ℚ) • fixedAbsolute ∧
    Order.coheight (genericPoint point.left) = 0 := by
  have hi : s2e_pairingAdjoint (properCyclePairing P 0 c) perfect
      (properCyclePairing P 0 c) (cohomologyMap ℚ 0 (𝟙 P)) fixedAbsolute =
      fixedAbsolute := by
    simpa only [cohomologyMap_id, LinearMap.id_apply] using
      s2e_pairingAdjoint_retraction (properCyclePairing P 0 c) perfect
        (properCyclePairing P 0 c) (LinearMap.id : _ →ₗ[ℚ] _) (by intros; rfl) fixedAbsolute
  refine ⟨hi, ?_, HodgeLean.RealDefs.coheight_genericPoint point.left⟩
  change s2e_pairingAdjoint (properCyclePairing P 0 c) perfect
    (properCyclePairing P 0 c) (cohomologyMap ℚ 0 (𝟙 P)) fixedAbsolute ≠ _
  rw [hi]
  exact doubled_ne fixedAbsolute fixedAbsolute_ne_zero
example := check_proper_cycle_adjoint

private def cancelledCycle : AlgebraicCycle point.left ℚ :=
  ∑ i : Fin 2, weightedPrime.mapRange
    ((if i = 0 then (1 : ℚ) else (-1 : ℚ)) * ·) (mul_zero _)
private theorem cancelledCycle_eq : cancelledCycle = weightedPrime - weightedPrime := by
  classical
  ext x
  simp [cancelledCycle, Fin.sum_univ_two, Function.locallyFinsuppWithin.mapRange_apply]

private def wholeClass : CohomologyWithSupport ℚ P Set.univ 0 :=
  (wholeSupportCohomologyLinearEquiv ℚ P 0).symm fixedAbsolute

private theorem homeomorph_transfer_id (X : TopCat.{0}) (Z : Set X) (n : ℕ)
    (a : CohomologyWithSupport ℚ X Z n) :
    supportHomeomorphTransfer (Homeomorph.refl X) Z n a = a :=
  LinearMap.congr_fun (cohomologyWithSupportMap_id ℚ X Z n) a

/-- The library's inverse-homeomorphism map retains a nonzero algebraic class image.
Source: Hatcher, Algebraic Topology, sections 2.1 and 3.1.
HC no distance; AV milestone no distance. -/
theorem check_support_homeomorph_transfer :
    forgetSupport ℚ P Set.univ 0
      (supportHomeomorphTransfer (Homeomorph.refl P) Set.univ 0 wholeClass) = fixedAbsolute ∧
    supportHomeomorphTransfer (Homeomorph.refl P) Set.univ 0 wholeClass ≠ 0 := by
  have ht : supportHomeomorphTransfer (Homeomorph.refl P) Set.univ 0 wholeClass =
      wholeClass := homeomorph_transfer_id P Set.univ 0 wholeClass
  have hf : forgetSupport ℚ P Set.univ 0 wholeClass = fixedAbsolute :=
    (wholeSupportCohomologyLinearEquiv ℚ P 0).apply_symm_apply fixedAbsolute
  refine ⟨(congrArg (forgetSupport ℚ P Set.univ 0) ht).trans hf, ?_⟩
  intro hz
  exact fixedAbsolute_ne_zero (hf.symm.trans
    ((congrArg (forgetSupport ℚ P Set.univ 0) (ht.symm.trans hz)).trans
      (map_zero _)))
example := check_support_homeomorph_transfer

/-- Opposite coefficients cancel before choosing the supported carrier.
Source: Fulton, Intersection Theory, sections 1.4 and 19.1.
HC no distance; AV milestone no distance. -/
theorem check_proper_cycle_rational_assembly :
    a3b4_cycleSupport point.hom cancelledCycle = ∅ ∧
    a3b4_cycleSupport point.hom weightedPrime ≠ ∅ ∧
    ∃ t : s2e_supportedClass point cancelledCycle 0,
      a3b4_IsCycleClass point.hom cancelledCycle 0 t ∧
      s2e_classToAbsolute point cancelledCycle 0 t = fixedAbsolute - fixedAbsolute ∧
      s2e_classToAbsolute point cancelledCycle 0 t ≠ fixedAbsolute := by
  refine ⟨?_, ?_, ?_⟩
  · rw [cancelledCycle_eq]
    simp [a3b4_cycleSupport]
  · rw [zero_pair_full_support]
    change (Set.univ : Set (ComplexPoint point)) ≠ ∅
    exact Set.univ_nonempty.ne_empty
  · have hΓ : cancelledCycle = 0 := cancelledCycle_eq.trans (sub_self _)
    rw [hΓ]
    refine ⟨0, ?_, ?_, ?_⟩
    · intro r e hS x _ hx
      simp [a3b4_cycleSupport] at hx
    · rw [map_zero, sub_self]
    · rw [map_zero]
      exact Ne.symm fixedAbsolute_ne_zero
example := check_proper_cycle_rational_assembly

end HodgeLean.Foundations.QuotientDuality.ProperCycleChecks
