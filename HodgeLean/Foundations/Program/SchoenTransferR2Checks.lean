import HodgeLean.RealDefs.DegreeZero
import HodgeLean.Foundations.Curves.CubicS13
import HodgeLean.Foundations.WitnessSelection.Defs
import HodgeLean.Foundations.Program.SchoenCyclePushDefs
import HodgeLean.Foundations.Program.SchoenCycleTowerHelpers
import HodgeLean.Foundations.Program.SchoenCycleC2AbsoluteTransportHelpers
import HodgeLean.Adapters.NormalConeB4aClassExistsPure

/-! # Primitive and zero-pair retention checks

The actual cyclotomic operator, normalized cycle carrier and tower map are used.
HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxRecDepth 4000
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
open HodgeLean.WitnessSelection HodgeLean.Adapters HodgeLean.Foundations.Program
open HodgeLean.RealDefs HodgeLean.Foundations HodgeLean.Foundations.Curves
namespace HodgeLean.Foundations.Program.R2Checks

private abbrev point : Over (Spec ↧ℂ) := Over.mk (𝟙 (Spec ↧ℂ))
private instance : Nonempty (ComplexPoint point) := ⟨𝟙 point⟩
private instance : IsIntegral point.left :=
  inferInstanceAs (IsIntegral (Spec (CommRingCat.of ℂ)))
private instance : DecidableEq point.left := Classical.decEq _

private instance : Unique (ComplexPoint point) where
  default := 𝟙 point
  uniq f := by
    apply Over.OverMorphism.ext
    simpa using f.w

private def pointChart : OpenPartialHomeomorph (ComplexPoint point)
    ((Fin (0 : ℕ) → ℂ) × (Fin (0 : ℕ) → ℂ)) := by
  letI : Unique ((Fin (0 : ℕ) → ℂ) × (Fin (0 : ℕ) → ℂ)) :=
    { default := 0, uniq := fun _ => Subsingleton.elim _ _ }
  exact (Homeomorph.homeomorphOfUnique _ _).toOpenPartialHomeomorph

private abbrev cubicH2 := AlgebraicTopology.Singular.Cohomology ℚ
  (TopCat.of (ComplexPoint E)) (2 : ℕ)
private abbrev primitiveOperator := Polynomial.aeval (s2e_pullback ℚ (𝟙 E) (2 : ℕ))
  (Polynomial.cyclotomic (1 : ℕ) ℚ)
private def intoPrimitive : cubicH2 ≃ₗ[ℚ] LinearMap.ker primitiveOperator where
  toFun x := ⟨x, by simp [primitiveOperator, s2e_pullback_id, Polynomial.cyclotomic_one]⟩
  invFun x := x.val
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
private instance : Module.Finite ℚ (HQ E (2 : ℕ)) :=
  s13_inputs_cubic.2.1.finite (2 : ℕ)
private def cubicPrimitiveBasis : Module.Basis (Fin (1 : ℕ)) ℚ
    (LinearMap.ker primitiveOperator) :=
  (Module.finBasisOfFinrankEq ℚ (HQ E (2 : ℕ)) (by
    simpa using finrank_HQ_cubic (2 : ℕ))).map
      (((HQ.linearEquiv E (2 : ℕ)).trans
        (rationalCohomologyLinearEquivSingular E (2 : ℕ))).trans intoPrimitive)

private theorem cubic_basis_nonzero : cubicPrimitiveBasis (0 : Fin (1 : ℕ)) ≠ 0 :=
  cubicPrimitiveBasis.ne_zero _

private theorem slice_basis_reselection_check :
    TopologicalSpace.dim E.left = (1 : ℕ) ∧
    (1 : ℕ) + 1 = 2 * (1 : ℕ) ∧
    (2 : ℚ) • ((1 / 2 : ℚ) • cubicPrimitiveBasis (0 : Fin (1 : ℕ))) =
      cubicPrimitiveBasis (0 : Fin (1 : ℕ)) ∧
    s2e_pullback ℚ (𝟙 E) (2 : ℕ)
      (cubicPrimitiveBasis (0 : Fin (1 : ℕ)) : cubicH2) =
      (cubicPrimitiveBasis (0 : Fin (1 : ℕ)) : cubicH2) := by
  refine ⟨E_dim, rfl, ?_, ?_⟩
  · rw [smul_smul]; norm_num
  · rw [s2e_pullback_id, LinearMap.id_apply]

private theorem slice_basis_reselection_falsification :
    ¬ ∃ anew : ℚ, anew • (0 : LinearMap.ker primitiveOperator) =
      cubicPrimitiveBasis (0 : Fin (1 : ℕ)) := by
  rintro ⟨anew, heq⟩
  exact cubic_basis_nonzero (by simpa using heq.symm)

example : (2 : ℚ) • ((1 / 2 : ℚ) • cubicPrimitiveBasis (0 : Fin (1 : ℕ))) =
    cubicPrimitiveBasis (0 : Fin (1 : ℕ)) ∧
    cubicPrimitiveBasis (0 : Fin (1 : ℕ)) ≠ 0 :=
  ⟨slice_basis_reselection_check.2.2.1, cubic_basis_nonzero⟩

private abbrev line := a1p_affineLine
private instance : IsIntegral line.left := by
  change IsIntegral (Spec (CommRingCat.of (Polynomial ℂ)))
  infer_instance
private instance : Smooth line.hom := by
  apply (HasRingHomProperty.Spec_iff (P := @Smooth)).mpr
  change (algebraMap ℂ (Polynomial ℂ)).Smooth
  exact RingHom.smooth_algebraMap.mpr ⟨inferInstance, inferInstance⟩
private instance : QuasiCompact line.hom := by
  change QuasiCompact (Spec.map (CommRingCat.ofHom (algebraMap ℂ (Polynomial ℂ))))
  infer_instance
private instance : IsSeparated line.hom := by
  change IsSeparated (Spec.map (CommRingCat.ofHom (algebraMap ℂ (Polynomial ℂ))))
  infer_instance
private instance : DecidableEq line.left := Classical.decEq _
private def origin : line.left :=
  PrimeSpectrum.comap (Polynomial.evalRingHom (0 : ℂ)) ⟨⊥, inferInstance⟩
private def divisor : AlgebraicCycle line.left ℚ :=
  Function.locallyFinsuppWithin.single origin (2 : ℚ)

private theorem origin_ne_generic : origin ≠ genericPoint line.left := by
  intro h
  have hx : Polynomial.X ∈ origin.asIdeal := by
    change Polynomial.eval (0 : ℂ) Polynomial.X ∈ (⊥ : Ideal ℂ)
    simp
  rw [h, show (genericPoint line.left).asIdeal = ⊥ from
    a1p_affineLineGeneric_asIdeal, Ideal.mem_bot] at hx
  exact Polynomial.X_ne_zero hx

private theorem divisor_codimension :
    ∀ x ∈ divisor.support, (1 : ℕ∞) ≤ Order.coheight x := by
  intro x hx
  have hx' : x = origin := by
    by_contra h
    have : divisor x = 0 := by simp [divisor, Function.locallyFinsuppWithin.single_apply, h]
    exact hx this
  subst x
  have hlt : origin < (⊤ : line.left) := lt_of_le_not_ge le_top (fun h =>
    origin_ne_generic ((genericPoint_specializes origin).antisymm h).eq.symm)
  simpa using Order.coheight_add_one_le hlt

private theorem normalized_divisor_reselection_check :
    ∃ αold αnew : s2e_supportedClass line divisor (1 : ℕ),
      a3b4_IsCycleClass line.hom divisor (1 : ℕ) αold ∧
      a3b4_IsCycleClass line.hom divisor (1 : ℕ) αnew ∧
      s2e_classToAbsolute line divisor (1 : ℕ) αnew =
        s2e_classToAbsolute line divisor (1 : ℕ) αold ∧
      divisor origin = (2 : ℚ) ∧ (1 : ℕ) + 1 = 2 * (1 : ℕ) := by
  obtain ⟨α, hα⟩ := a3b4a_cycleClass_exists_of_codimension line.hom divisor
    (1 : ℕ) divisor_codimension
  exact ⟨α, α, hα, hα, rfl, by simp [divisor], rfl⟩

-- Smooth support of a new representative does not retain a fixed nonzero coordinate.
private theorem cycle_coordinate_loss_falsification :
    ¬ ∃ anew : ℚ, Function.locallyFinsuppWithin.single origin anew = divisor ∧
      Function.locallyFinsuppWithin.single origin anew = (0 : AlgebraicCycle line.left ℚ) := by
  rintro ⟨anew, hfixed, hzero⟩
  have h := hfixed.symm.trans hzero
  have heval := congrArg (fun c : AlgebraicCycle line.left ℚ => c origin) h
  norm_num [divisor] at heval

example : ∃ αold αnew : s2e_supportedClass line divisor (1 : ℕ),
    a3b4_IsCycleClass line.hom divisor (1 : ℕ) αold ∧
    a3b4_IsCycleClass line.hom divisor (1 : ℕ) αnew ∧
    s2e_classToAbsolute line divisor (1 : ℕ) αnew =
      s2e_classToAbsolute line divisor (1 : ℕ) αold ∧
    divisor origin = (2 : ℚ) ∧ (1 : ℕ) + 1 = 2 * (1 : ℕ) :=
  normalized_divisor_reselection_check

private def zeroPairOrbit : AlgebraicCycle point.left ℚ :=
  s2e_rationalOrbitCycle (𝟙 point) (𝟙 point) (1 : ℕ) (fun _ => (2 : ℚ))

private theorem zero_pair_orbit_coefficient :
    pushedCycle (s2e_towerTotalMap (fun _ : Fin (1 : ℕ) => point)
      (𝟙 point) (fun i : Fin (0 : ℕ) => Fin.elim0 i) (Fin.last (0 : ℕ))).left
      zeroPairOrbit (genericPoint point.left) = (2 : ℚ) := by
  classical
  change pushedCycle (𝟙 point.left) zeroPairOrbit (genericPoint point.left) = (2 : ℚ)
  rw [pushedCycle, a1p_pushforward_id]
  simp only [zeroPairOrbit, s2e_rationalOrbitCycle, Fin.sum_univ_one,
    s2e_componentCycle]
  change (2 : ℚ) * (if genericPoint point.left = genericPoint point.left then 1 else 0) = 2
  norm_num

private theorem zero_pair_normalized_class :
    ∃ α : s2e_supportedClass point zeroPairOrbit (0 : ℕ),
      a3b4_IsCycleClass point.hom zeroPairOrbit (0 : ℕ) α := by
  apply a3b4a_cycleClass_exists_of_codimension
  intro x hx
  exact bot_le

example : (∃ α : s2e_supportedClass point zeroPairOrbit (0 : ℕ),
    a3b4_IsCycleClass point.hom zeroPairOrbit (0 : ℕ) α) ∧
    pushedCycle (𝟙 point.left) zeroPairOrbit (genericPoint point.left) = (2 : ℚ) :=
  ⟨zero_pair_normalized_class, zero_pair_orbit_coefficient⟩

#print axioms slice_basis_reselection_check
#print axioms slice_basis_reselection_falsification
#print axioms normalized_divisor_reselection_check


private theorem zero_pair_full_support :
    a3b4_cycleSupport point.hom zeroPairOrbit = Set.univ := by
  ext x
  constructor
  · intro _; trivial
  · intro _
    change Point.underlying x ∈ ⋃ ξ ∈ zeroPairOrbit.support, closure {ξ}
    apply Set.mem_iUnion.mpr
    refine ⟨genericPoint point.left, Set.mem_iUnion.mpr ⟨?_, ?_⟩⟩
    · change zeroPairOrbit (genericPoint point.left) ≠ 0
      have h := zero_pair_orbit_coefficient
      change pushedCycle (𝟙 point.left) zeroPairOrbit (genericPoint point.left) = (2 : ℚ) at h
      rw [pushedCycle, a1p_pushforward_id] at h
      rw [h]; norm_num
    · rw [genericPoint_closure]; trivial

private def fixedSupported : s2e_supportedClass point zeroPairOrbit (0 : ℕ) :=
  zero_pair_normalized_class.choose

private theorem fixedSupported_normalized :
    a3b4_IsCycleClass point.hom zeroPairOrbit (0 : ℕ) fixedSupported :=
  zero_pair_normalized_class.choose_spec

private theorem fixedSupported_ne_zero : fixedSupported ≠ 0 := by
  intro hz
  have hS : ∀ y ∈ pointChart.source,
      y ∈ a3b4_cycleSupport point.hom zeroPairOrbit ↔ (pointChart y).2 = 0 := by
    intro y hy
    rw [zero_pair_full_support]
    simp only [Set.mem_univ, true_iff]
    exact Subsingleton.elim _ _
  have hhol : a3b4_IsHolChart point.hom pointChart :=
    ⟨fun j => Fin.elim0 j, fun j => Fin.elim0 j⟩
  let x : ComplexPoint point := 𝟙 point
  obtain ⟨W, hW, hWo, hxW, hnorm⟩ := fixedSupported_normalized (0 : ℕ)
    pointChart hS x (by change x ∈ Set.univ; trivial) (by rw [zero_pair_full_support]; trivial) hhol
  have hm : a3b4_multiplicity point.hom zeroPairOrbit x = (2 : ℚ) := by
    classical
    have hc : zeroPairOrbit = Function.locallyFinsuppWithin.single
        (genericPoint point.left) (2 : ℚ) := by
      ext y
      simp [zeroPairOrbit, s2e_rationalOrbitCycle, s2e_componentCycle, Fin.sum_univ_one]
    have hcoeff : zeroPairOrbit (genericPoint point.left) = (2 : ℚ) := by
      rw [hc]; simp
    rw [a3b4a_classMultiplicity_eq_component point.hom zeroPairOrbit
      (genericPoint point.left) (by change zeroPairOrbit _ ≠ 0; rw [hcoeff]; norm_num)
      x (by rw [genericPoint_closure]; trivial) (by
        intro η hη hne
        have heq : η = genericPoint point.left := by simpa [hc] using hη
        exact (hne heq).elim), hcoeff]

  rw [hz, map_zero, hm] at hnorm
  have hn := chartNormalProjectionCoclass_ne_zero (Fin (0 : ℕ) → ℂ) (0 : ℕ)
    pointChart (a3b4_cycleSupport point.hom zeroPairOrbit) hS hWo hW hxW
      (Subsingleton.elim _ _)
  exact (smul_ne_zero (by norm_num : (2 : ℚ) ≠ 0) hn) hnorm.symm

private abbrev pointH0 := AlgebraicTopology.Singular.Cohomology ℚ
  (TopCat.of (ComplexPoint point)) (0 : ℕ)
private def fixedAbsolute : pointH0 := s2e_classToAbsolute point zeroPairOrbit (0 : ℕ) fixedSupported

private theorem fixedAbsolute_ne_zero : fixedAbsolute ≠ 0 := by
  have hi : Function.Injective (s2e_classToAbsolute point zeroPairOrbit (0 : ℕ)) := by
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

private abbrev pointOperator := Polynomial.aeval (s2e_pullback ℚ (𝟙 point) (0 : ℕ))
  (Polynomial.cyclotomic (1 : ℕ) ℚ)
private def pointPrimitiveEquiv : pointH0 ≃ₗ[ℚ] LinearMap.ker pointOperator where
  toFun x := ⟨x, by simp [pointOperator, s2e_pullback_id, Polynomial.cyclotomic_one]⟩
  invFun x := x.val
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private theorem pointH0_rank : Module.finrank ℚ pointH0 = (1 : ℕ) := by
  letI : Unique (UnitAddTorus (Fin (0 : ℕ))) :=
    { default := 0, uniq := fun _ => Subsingleton.elim _ _ }
  let e : ComplexPoint point ≃ₜ UnitAddTorus (Fin (0 : ℕ)) :=
    Homeomorph.homeomorphOfUnique _ _
  rw [(HodgeLean.Foundations.Singular.cohomologyHomeomorphEquiv e (0 : ℕ)).finrank_eq]
  exact HodgeLean.Foundations.Singular.finrank_cohomology_unitAddTorus (0 : ℕ) (0 : ℕ)

private def normalizedPrimitiveBasis : Module.Basis (Fin (1 : ℕ)) ℚ
    (LinearMap.ker pointOperator) :=
  (FiniteDimensional.basisSingleton (Fin (1 : ℕ)) pointH0_rank fixedAbsolute fixedAbsolute_ne_zero).map
    pointPrimitiveEquiv

private theorem normalized_geometric_model :
    IsClosedImmersion (𝟙 point : point ⟶ point).left ∧ IsFinite (𝟙 point : point ⟶ point).left ∧
    Function.Surjective (𝟙 point : point ⟶ point).left ∧
    a3b4_IsCycleClass point.hom
      (s2e_rationalOrbitCycle (𝟙 point) (𝟙 point) (1 : ℕ) (fun _ => (2 : ℚ)))
      (0 : ℕ) fixedSupported ∧
    s2e_classToAbsolute point zeroPairOrbit (0 : ℕ) fixedSupported =
      (normalizedPrimitiveBasis (0 : Fin (1 : ℕ)) : pointH0) ∧
    s2e_pullback ℚ (𝟙 point) (0 : ℕ)
      (s2e_classToAbsolute point zeroPairOrbit (0 : ℕ) fixedSupported) =
        (normalizedPrimitiveBasis (0 : Fin (1 : ℕ)) : pointH0) ∧
    (normalizedPrimitiveBasis (0 : Fin (1 : ℕ)) : pointH0) ≠ 0 := by
  have hb : (normalizedPrimitiveBasis (0 : Fin (1 : ℕ)) : pointH0) = fixedAbsolute := by
    simp [normalizedPrimitiveBasis, pointPrimitiveEquiv]
  refine ⟨inferInstance, inferInstance, Function.surjective_id,
    fixedSupported_normalized, hb.symm, ?_, ?_⟩
  · rw [s2e_pullback_id, LinearMap.id_apply]; exact hb.symm
  · rw [hb]; exact fixedAbsolute_ne_zero

example := normalized_geometric_model
#print axioms normalized_geometric_model

private theorem fixed_supported_loss : (2 : ℚ) • fixedSupported ≠ fixedSupported := by
  intro heq
  have hz : ((2 : ℚ) - 1) • fixedSupported = 0 := by
    rw [sub_smul, one_smul, heq, sub_self]
  norm_num at hz
  exact fixedSupported_ne_zero hz

private def pointTrace : pointH0 →ₗ[ℚ] ℚ :=
  (FiniteDimensional.basisSingleton (Fin (1 : ℕ)) pointH0_rank
    (Singular.unit (TopCat.of (ComplexPoint point)))
    (Singular.unit_ne_zero _)).coord (0 : Fin (1 : ℕ))

private theorem pointTrace_unit :
    pointTrace (Singular.unit (TopCat.of (ComplexPoint point))) = (1 : ℚ) := by
  simp [pointTrace, Singular.unit_ne_zero]

private theorem adjoint_compatibility_loss :
    (∀ u v : pointH0,
      s2e_middlePairing (TopCat.of (ComplexPoint point)) (0 : ℕ) pointTrace
        ((LinearMap.id : pointH0 →ₗ[ℚ] pointH0) u) v =
      s2e_middlePairing (TopCat.of (ComplexPoint point)) (0 : ℕ) pointTrace
        u (s2e_pullback ℚ (𝟙 point) (0 : ℕ) v)) ∧
    ¬ (∀ u v : pointH0,
      s2e_middlePairing (TopCat.of (ComplexPoint point)) (0 : ℕ) pointTrace
        (((2 : ℚ) • (LinearMap.id : pointH0 →ₗ[ℚ] pointH0)) u) v =
      s2e_middlePairing (TopCat.of (ComplexPoint point)) (0 : ℕ) pointTrace
        u (s2e_pullback ℚ (𝟙 point) (0 : ℕ) v)) := by
  constructor
  · intro u v
    rw [s2e_pullback_id, LinearMap.id_apply, LinearMap.id_apply]
  · intro h
    have heq := h (Singular.unit (TopCat.of (ComplexPoint point)))
      (Singular.unit (TopCat.of (ComplexPoint point)))
    simp only [s2e_pullback_id, LinearMap.id_apply, LinearMap.smul_apply,
      map_smul, LinearMap.smul_apply] at heq
    have hu : s2e_middlePairing (TopCat.of (ComplexPoint point)) (0 : ℕ) pointTrace
        (Singular.unit (TopCat.of (ComplexPoint point)))
        (Singular.unit (TopCat.of (ComplexPoint point))) = (1 : ℚ) := by
      change pointTrace (Singular.cup _ _ _ _) = 1
      rw [Singular.one_cup, pointTrace_unit]
    rw [hu] at heq
    norm_num at heq

example : fixedSupported ≠ 0 ∧ (2 : ℚ) • fixedSupported ≠ 0 ∧
    (2 : ℚ) • fixedSupported ≠ fixedSupported := by
  refine ⟨fixedSupported_ne_zero, ?_, fixed_supported_loss⟩
  exact smul_ne_zero (by norm_num) fixedSupported_ne_zero

#print axioms fixed_supported_loss
#print axioms adjoint_compatibility_loss

private theorem zero_pair_loss : zeroPairOrbit ≠ (0 : AlgebraicCycle point.left ℚ) := by
  intro heq
  have h := zero_pair_orbit_coefficient
  change pushedCycle (𝟙 point.left) zeroPairOrbit (genericPoint point.left) = (2 : ℚ) at h
  rw [pushedCycle, a1p_pushforward_id, heq] at h
  norm_num at h


/-- Independent construction model for ramified_slice_reselection.
Source: Schoen (1988), pp. 13–18; Fulton, Intersection Theory, §§1.4,19.1.
HC no distance; AV milestone no distance. -/
theorem s4_chain_ramified_slice_reselection_example :
    TopologicalSpace.dim E.left = (1 : ℕ) ∧
    (1 : ℕ) + 1 = 2 * (1 : ℕ) ∧
    (2 : ℚ) • ((1 / 2 : ℚ) • cubicPrimitiveBasis (0 : Fin (1 : ℕ))) =
      cubicPrimitiveBasis (0 : Fin (1 : ℕ)) ∧
    s2e_pullback ℚ (𝟙 E) (2 : ℕ)
      (cubicPrimitiveBasis (0 : Fin (1 : ℕ)) : cubicH2) =
      (cubicPrimitiveBasis (0 : Fin (1 : ℕ)) : cubicH2) :=
  slice_basis_reselection_check

example :
    TopologicalSpace.dim E.left = (1 : ℕ) ∧
    (1 : ℕ) + 1 = 2 * (1 : ℕ) ∧
    (2 : ℚ) • ((1 / 2 : ℚ) • cubicPrimitiveBasis (0 : Fin (1 : ℕ))) =
      cubicPrimitiveBasis (0 : Fin (1 : ℕ)) ∧
    s2e_pullback ℚ (𝟙 E) (2 : ℕ)
      (cubicPrimitiveBasis (0 : Fin (1 : ℕ)) : cubicH2) =
      (cubicPrimitiveBasis (0 : Fin (1 : ℕ)) : cubicH2) := s4_chain_ramified_slice_reselection_example

/-- Independent construction model for ramified_slice_reselection.
Source: Schoen (1988), pp. 13–18; Fulton, Intersection Theory, §§1.4,19.1.
HC no distance; AV milestone no distance. -/
theorem s4_chain_ramified_slice_reselection_falsification :
    ¬ ∃ anew : ℚ, anew • (0 : LinearMap.ker primitiveOperator) =
      cubicPrimitiveBasis (0 : Fin (1 : ℕ)) :=
  slice_basis_reselection_falsification

example :
    ¬ ∃ anew : ℚ, anew • (0 : LinearMap.ker primitiveOperator) =
      cubicPrimitiveBasis (0 : Fin (1 : ℕ)) := s4_chain_ramified_slice_reselection_falsification

/-- Independent construction model for ramified_basis_reselection.
Source: Schoen (1988), pp. 13–18; Fulton, Intersection Theory, §§1.4,19.1.
HC no distance; AV milestone no distance. -/
theorem s4_chain_ramified_basis_reselection_example :
    TopologicalSpace.dim E.left = (1 : ℕ) ∧
    (1 : ℕ) + 1 = 2 * (1 : ℕ) ∧
    (2 : ℚ) • ((1 / 2 : ℚ) • cubicPrimitiveBasis (0 : Fin (1 : ℕ))) =
      cubicPrimitiveBasis (0 : Fin (1 : ℕ)) ∧
    s2e_pullback ℚ (𝟙 E) (2 : ℕ)
      (cubicPrimitiveBasis (0 : Fin (1 : ℕ)) : cubicH2) =
      (cubicPrimitiveBasis (0 : Fin (1 : ℕ)) : cubicH2) :=
  slice_basis_reselection_check

example :
    TopologicalSpace.dim E.left = (1 : ℕ) ∧
    (1 : ℕ) + 1 = 2 * (1 : ℕ) ∧
    (2 : ℚ) • ((1 / 2 : ℚ) • cubicPrimitiveBasis (0 : Fin (1 : ℕ))) =
      cubicPrimitiveBasis (0 : Fin (1 : ℕ)) ∧
    s2e_pullback ℚ (𝟙 E) (2 : ℕ)
      (cubicPrimitiveBasis (0 : Fin (1 : ℕ)) : cubicH2) =
      (cubicPrimitiveBasis (0 : Fin (1 : ℕ)) : cubicH2) := s4_chain_ramified_basis_reselection_example

/-- Independent construction model for ramified_basis_reselection.
Source: Schoen (1988), pp. 13–18; Fulton, Intersection Theory, §§1.4,19.1.
HC no distance; AV milestone no distance. -/
theorem s4_chain_ramified_basis_reselection_falsification :
    ¬ ∃ anew : ℚ, anew • (0 : LinearMap.ker primitiveOperator) =
      cubicPrimitiveBasis (0 : Fin (1 : ℕ)) :=
  slice_basis_reselection_falsification

example :
    ¬ ∃ anew : ℚ, anew • (0 : LinearMap.ker primitiveOperator) =
      cubicPrimitiveBasis (0 : Fin (1 : ℕ)) := s4_chain_ramified_basis_reselection_falsification

/-- Independent construction model for ramified_normalized_support.
Source: Schoen (1988), pp. 13–18; Fulton, Intersection Theory, §§1.4,19.1.
HC no distance; AV milestone no distance. -/
theorem s4_chain_ramified_normalized_support_example :
    (∃ αold αnew : s2e_supportedClass line divisor (1 : ℕ),
      a3b4_IsCycleClass line.hom divisor (1 : ℕ) αold ∧
      a3b4_IsCycleClass line.hom divisor (1 : ℕ) αnew ∧
      s2e_classToAbsolute line divisor (1 : ℕ) αnew =
        s2e_classToAbsolute line divisor (1 : ℕ) αold ∧
      divisor origin = (2 : ℚ) ∧ (1 : ℕ) + 1 = 2 * (1 : ℕ)) ∧
    (∀ x ∈ divisor.support, ∃ U : line.left.Opens, x ∈ U ∧ Smooth (U.ι ≫ line.hom)) :=
  ⟨normalized_divisor_reselection_check, fun _x _ => ⟨⊤, trivial, inferInstance⟩⟩

example := s4_chain_ramified_normalized_support_example

/-- Independent construction model for ramified_normalized_support.
Source: Schoen (1988), pp. 13–18; Fulton, Intersection Theory, §§1.4,19.1.
HC no distance; AV milestone no distance. -/
theorem s4_chain_ramified_normalized_support_falsification :
    (2 : ℚ) • fixedSupported ≠ fixedSupported :=
  fixed_supported_loss

example := s4_chain_ramified_normalized_support_falsification

/-- Independent construction model for ramified_zero_pair_support.
Source: Schoen (1988), pp. 13–18; Fulton, Intersection Theory, §§1.4,19.1.
HC no distance; AV milestone no distance. -/
theorem s4_chain_ramified_zero_pair_support_example :
    Etale point.hom ∧ Smooth point.hom ∧
    (∃ α : s2e_supportedClass point zeroPairOrbit (0 : ℕ),
      a3b4_IsCycleClass point.hom zeroPairOrbit (0 : ℕ) α) ∧
    (pushedCycle (s2e_towerTotalMap (fun _ : Fin (1 : ℕ) => point)
      (𝟙 point) (fun i : Fin (0 : ℕ) => Fin.elim0 i) (Fin.last (0 : ℕ))).left
      zeroPairOrbit (genericPoint point.left) = (2 : ℚ)) :=
  ⟨(by change Etale (𝟙 (Spec ↧ℂ)); infer_instance),
    (by change Smooth (𝟙 (Spec ↧ℂ)); infer_instance),
    zero_pair_normalized_class, zero_pair_orbit_coefficient⟩

example := s4_chain_ramified_zero_pair_support_example

/-- Independent construction model for ramified_zero_pair_support.
Source: Schoen (1988), pp. 13–18; Fulton, Intersection Theory, §§1.4,19.1.
HC no distance; AV milestone no distance. -/
theorem s4_chain_ramified_zero_pair_support_falsification : zeroPairOrbit ≠ (0 : AlgebraicCycle point.left ℚ) :=
  zero_pair_loss

example : zeroPairOrbit ≠ (0 : AlgebraicCycle point.left ℚ) := s4_chain_ramified_zero_pair_support_falsification

/-- Independent construction model for ramified_support_assembly.
Source: Schoen (1988), pp. 13–18; Fulton, Intersection Theory, §§1.4,19.1.
HC no distance; AV milestone no distance. -/
theorem s4_chain_ramified_support_assembly_example :
    (∃ αold αnew : s2e_supportedClass line divisor (1 : ℕ),
      a3b4_IsCycleClass line.hom divisor (1 : ℕ) αold ∧
      a3b4_IsCycleClass line.hom divisor (1 : ℕ) αnew ∧
      s2e_classToAbsolute line divisor (1 : ℕ) αnew =
        s2e_classToAbsolute line divisor (1 : ℕ) αold ∧
      divisor origin = (2 : ℚ) ∧ (1 : ℕ) + 1 = 2 * (1 : ℕ)) ∧
    (∀ x ∈ divisor.support, ∃ U : line.left.Opens, x ∈ U ∧ Smooth (U.ι ≫ line.hom)) :=
  ⟨normalized_divisor_reselection_check, fun _x _ => ⟨⊤, trivial, inferInstance⟩⟩

example := s4_chain_ramified_support_assembly_example

/-- The specified unit-normalized traces satisfy the middle-pairing adjoint equation
for the identity projection; doubling the adjoint violates that equation.
Source: Schoen (1988), pp. 13–18; Fulton, Intersection Theory, §§1.4,19.1.
HC no distance; AV milestone no distance. -/
theorem s4_chain_ramified_support_assembly_falsification :
    (∀ u v : pointH0,
      s2e_middlePairing (TopCat.of (ComplexPoint point)) (0 : ℕ) pointTrace
        ((LinearMap.id : pointH0 →ₗ[ℚ] pointH0) u) v =
      s2e_middlePairing (TopCat.of (ComplexPoint point)) (0 : ℕ) pointTrace
        u (s2e_pullback ℚ (𝟙 point) (0 : ℕ) v)) ∧
    ¬ (∀ u v : pointH0,
      s2e_middlePairing (TopCat.of (ComplexPoint point)) (0 : ℕ) pointTrace
        (((2 : ℚ) • (LinearMap.id : pointH0 →ₗ[ℚ] pointH0)) u) v =
      s2e_middlePairing (TopCat.of (ComplexPoint point)) (0 : ℕ) pointTrace
        u (s2e_pullback ℚ (𝟙 point) (0 : ℕ) v)) :=
  adjoint_compatibility_loss

example := s4_chain_ramified_support_assembly_falsification

/-- A geometric slice/component/projection model with normalized orbit representatives
of a fixed nonzero cyclotomic-kernel basis, using the degree-zero point model.
Source: Schoen (1988), pp. 13–18; Fulton, Intersection Theory, §19.1.
HC no distance; AV milestone no distance. -/
theorem s4_chain_ramified_slice_basis_retention_example :
    IsClosedImmersion (𝟙 point : point ⟶ point).left ∧ IsFinite (𝟙 point : point ⟶ point).left ∧
    Function.Surjective (𝟙 point : point ⟶ point).left ∧
    a3b4_IsCycleClass point.hom
      (s2e_rationalOrbitCycle (𝟙 point) (𝟙 point) (1 : ℕ) (fun _ => (2 : ℚ)))
      (0 : ℕ) fixedSupported ∧
    s2e_classToAbsolute point zeroPairOrbit (0 : ℕ) fixedSupported =
      (normalizedPrimitiveBasis (0 : Fin (1 : ℕ)) : pointH0) ∧
    s2e_pullback ℚ (𝟙 point) (0 : ℕ)
      (s2e_classToAbsolute point zeroPairOrbit (0 : ℕ) fixedSupported) =
        (normalizedPrimitiveBasis (0 : Fin (1 : ℕ)) : pointH0) ∧
    (normalizedPrimitiveBasis (0 : Fin (1 : ℕ)) : pointH0) ≠ 0 := normalized_geometric_model

example := s4_chain_ramified_slice_basis_retention_example

end HodgeLean.Foundations.Program.R2Checks
