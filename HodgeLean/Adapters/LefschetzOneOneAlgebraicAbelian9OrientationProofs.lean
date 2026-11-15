import HodgeLean.Adapters.LefschetzOneOneAlgebraicAbelian9OrientationDefs

noncomputable section
open CategoryTheory AlgebraicTopology.Singular
namespace HodgeLean.Adapters

open HodgeLean.Foundations.Singular

/-- Every rational functional on the top cohomology of the coordinate torus is
represented by a unique homology class.
Source: the universal coefficient theorem over a field and finite-dimensional duality. -/
theorem bh9_torus_functional_representable
    (f : Cohomology ℚ (TopCat.of (UnitAddTorus (Fin 2))) 2 →ₗ[ℚ] ℚ) :
    ∃! z : Homology ℚ (TopCat.of (UnitAddTorus (Fin 2))) 2,
      ∀ a, cohomologyEquivDualHomology ℚ _ 2 a z = f a := by
  let e := cohomologyEquivDualHomology ℚ (TopCat.of (UnitAddTorus (Fin 2))) 2
  let := finite_cohomology_unitAddTorus 2 2
  let : Module.Finite ℚ (Module.Dual ℚ
      (Homology ℚ (TopCat.of (UnitAddTorus (Fin 2))) 2)) :=
    Module.Finite.equiv e
  let : Module.Finite ℚ (Homology ℚ (TopCat.of (UnitAddTorus (Fin 2))) 2) :=
    (Module.finite_dual_iff ℚ).mp inferInstance
  let z := (Module.evalEquiv ℚ _).symm (f.comp e.symm.toLinearMap)
  refine ⟨z, ?_, ?_⟩
  · intro a
    change e a ((Module.evalEquiv ℚ _).symm _) = f a
    rw [Module.apply_evalEquiv_symm_apply, LinearMap.comp_apply,
      LinearEquiv.coe_coe, e.symm_apply_apply]
  · intro w hw
    apply (Module.evalEquiv ℚ _).injective
    apply LinearMap.ext
    intro g
    obtain ⟨a, rfl⟩ := e.surjective g
    change e a w = e a z
    rw [hw]
    symm
    change e a ((Module.evalEquiv ℚ _).symm _) = f a
    rw [Module.apply_evalEquiv_symm_apply, LinearMap.comp_apply,
      LinearEquiv.coe_coe, e.symm_apply_apply]

/-- Restriction of the disk class to its center preserves its prescribed local generator.
Source: the inverse in `bh5_diskClass` and the convex-support restriction isomorphism. -/
theorem bh9_diskClass_restrict :
    relativeHomologyMap ℚ 2
      (supportInclusionPairMap (TopCat.of (Fin 1 → ℂ))
        (Set.singleton_subset_iff.mpr
          (Metric.mem_closedBall_self (by norm_num : (0 : ℝ) ≤ 2)))) bh5_diskClass =
      standardComplexLocalClass ℚ 1 := by
  exact (Equiv.ofBijective _ (HodgeLean.RealDefs.j5c_convex_restrict_bijective
    (convex_closedBall (0 : Fin 1 → ℂ) (2 : ℝ)) (isCompact_closedBall 0 2)
    (Metric.mem_closedBall_self (by norm_num : (0 : ℝ) ≤ 2)) 2)).apply_symm_apply _

/-- The prescribed disk class is nonzero.
Source: nonvanishing of the standard complex local class and restriction to the center. -/
theorem bh9_diskClass_ne_zero : bh5_diskClass ≠ 0 := by
  let f : RelativeHomology ℚ bh5_diskPair 2 →ₗ[ℚ]
      RelativeHomology ℚ (puncturedPair ℂ 1) 2 :=
    relativeHomologyMap ℚ 2
      (supportInclusionPairMap (TopCat.of (Fin 1 → ℂ))
        (Set.singleton_subset_iff.mpr
          (Metric.mem_closedBall_self (by norm_num : (0 : ℝ) ≤ 2))))
  intro h
  apply standardComplexLocalClass_ne_zero_for_chart 1
  calc
    standardComplexLocalClass ℚ 1 = f bh5_diskClass := bh9_diskClass_restrict.symm
    _ = f 0 := congrArg f h
    _ = 0 := f.map_zero

/-- Every degree-two disk-relative class is a multiple of the prescribed disk class.
Source: convex-support restriction and generation by the standard complex local class. -/
theorem bh9_diskClass_spans (z : RelativeHomology ℚ bh5_diskPair 2) :
    ∃ r : ℚ, r • bh5_diskClass = z := by
  let f : RelativeHomology ℚ bh5_diskPair 2 →ₗ[ℚ]
      RelativeHomology ℚ (puncturedPair ℂ 1) 2 := relativeHomologyMap ℚ 2
    (supportInclusionPairMap (TopCat.of (Fin 1 → ℂ))
      (Set.singleton_subset_iff.mpr
        (Metric.mem_closedBall_self (by norm_num : (0 : ℝ) ≤ 2))))
  have hf := HodgeLean.RealDefs.j5c_convex_restrict_bijective
    (convex_closedBall (0 : Fin 1 → ℂ) (2 : ℝ)) (isCompact_closedBall 0 2)
    (Metric.mem_closedBall_self (by norm_num : (0 : ℝ) ≤ 2)) 2
  have hz : f z ∈ Submodule.span ℚ {standardComplexLocalClass ℚ 1} := by
    rw [span_standardComplexLocalClass_eq_top_for_chart]
    exact Submodule.mem_top
  obtain ⟨r, hr⟩ := Submodule.mem_span_singleton.mp hz
  refine ⟨r, hf.1 ?_⟩
  change f (r • bh5_diskClass) = f z
  rw [map_smul, show f bh5_diskClass = standardComplexLocalClass ℚ 1 from
    bh9_diskClass_restrict, hr]

private def bh9_unitArcHomeomorph : Set.Ioo (0 : ℝ) 1 ≃ₜ circleArc 0 :=
  (Homeomorph.setCongr (by rw [zero_add] : Set.Ioo (0 : ℝ) 1 = Set.Ioo 0 (0 + 1))).trans
    (circleArcHomeomorph 0)

/-- The open square is the complement of the coordinate skeleton, in coordinate order.
Source: Hatcher, Algebraic Topology, section 2.2, the open torus two-cell;
`circleArcHomeomorph` identifies each open unit interval with the punctured circle. -/
def bh9_openCellHomeomorph :
    (Set.Ioo (0 : ℝ) 1 × Set.Ioo (0 : ℝ) 1) ≃ₜ
      (bh9_torusSkeletonᶜ : Set (UnitAddTorus (Fin 2))) where
  toFun p := ⟨![(bh9_unitArcHomeomorph p.1).val,
      (bh9_unitArcHomeomorph p.2).val], by
    rintro (h | h)
    · exact (bh9_unitArcHomeomorph p.1).property h
    · exact (bh9_unitArcHomeomorph p.2).property h⟩
  invFun t := (bh9_unitArcHomeomorph.symm ⟨t.val 0, fun h ↦ t.property (Or.inl h)⟩,
    bh9_unitArcHomeomorph.symm ⟨t.val 1, fun h ↦ t.property (Or.inr h)⟩)
  left_inv p := by
    apply Prod.ext
    · exact bh9_unitArcHomeomorph.symm_apply_apply p.1
    · exact bh9_unitArcHomeomorph.symm_apply_apply p.2
  right_inv t := by
    apply Subtype.ext
    funext i
    fin_cases i
    · exact congrArg Subtype.val (bh9_unitArcHomeomorph.apply_symm_apply
        ⟨t.val 0, fun h ↦ t.property (Or.inl h)⟩)
    · exact congrArg Subtype.val (bh9_unitArcHomeomorph.apply_symm_apply
        ⟨t.val 1, fun h ↦ t.property (Or.inr h)⟩)
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply continuous_pi
    intro i
    fin_cases i
    · exact continuous_subtype_val.comp
        (bh9_unitArcHomeomorph.continuous.comp continuous_fst)
    · exact continuous_subtype_val.comp
        (bh9_unitArcHomeomorph.continuous.comp continuous_snd)
  continuous_invFun := by
    apply Continuous.prodMk
    · exact bh9_unitArcHomeomorph.symm.continuous.comp
        (((continuous_apply 0).comp continuous_subtype_val).subtype_mk _)
    · exact bh9_unitArcHomeomorph.symm.continuous.comp
        (((continuous_apply 1).comp continuous_subtype_val).subtype_mk _)

example (p : Set.Ioo (0 : ℝ) 1 × Set.Ioo (0 : ℝ) 1) :
    (bh9_openCellHomeomorph p).val = ![(p.1.val : UnitAddCircle),
      (p.2.val : UnitAddCircle)] := rfl

/-- In the interior, the clamped map agrees with the ordered open-cell chart.
Source: the affine coordinate formula defining `bh9_squareTorus`. -/
theorem bh9_squareTorus_openCell (p : Set.Ioo (0 : ℝ) 1 × Set.Ioo (0 : ℝ) 1) :
    bh9_squareTorus (fun _ ↦ Complex.mk (2 * p.1.val - 1) (2 * p.2.val - 1)) =
      (bh9_openCellHomeomorph p).val := by
  have h1 : (2 * p.1.val - 1 + 1) / 2 = p.1.val := by ring
  have h2 : (2 * p.2.val - 1 + 1) / 2 = p.2.val := by ring
  change ![(bh5_clamp ((2 * p.1.val - 1 + 1) / 2) : UnitAddCircle),
    (bh5_clamp ((2 * p.2.val - 1 + 1) / 2) : UnitAddCircle)] =
      ![(p.1.val : UnitAddCircle), (p.2.val : UnitAddCircle)]
  rw [h1, h2]
  simp only [bh5_clamp, min_eq_right p.1.property.2.le, min_eq_right p.2.property.2.le,
    max_eq_right p.1.property.1.le, max_eq_right p.2.property.1.le]

/-- Duality isolates the remaining relative homology comparison exactly.
Source: naturality of universal coefficients for the projection and the square map. -/
theorem bh9_torus_cell_iff_homology
    (z : Homology ℚ (TopCat.of (UnitAddTorus (Fin 2))) 2)
    (hz : ∀ b, cohomologyEquivDualHomology ℚ _ 2 b z = bh8_torusCoefficient b) :
    (∀ a : RelativeCohomology ℚ bh9_torusPair 2,
      bh8_torusCoefficient (relativeCohomologyToAbsolute ℚ bh9_torusPair 2 a) =
        relativeCohomologyEquivDualHomology ℚ bh5_diskPair 2
          (relativeCohomologyMap ℚ 2 bh9_squareTorusMap a) bh5_diskClass) ↔
      (relativeHomologyProjection ℚ bh9_torusPair 2).hom z =
        relativeHomologyMap ℚ 2 bh9_squareTorusMap bh5_diskClass := by
  constructor
  · intro h
    apply Module.eval_apply_injective ℚ
    apply LinearMap.ext
    intro f
    obtain ⟨a, rfl⟩ := (relativeCohomologyEquivDualHomology ℚ bh9_torusPair 2).surjective f
    change relativeCohomologyEquivDualHomology ℚ bh9_torusPair 2 a
      ((relativeHomologyProjection ℚ bh9_torusPair 2).hom z) =
        relativeCohomologyEquivDualHomology ℚ bh9_torusPair 2 a
          (relativeHomologyMap ℚ 2 bh9_squareTorusMap bh5_diskClass)
    exact (cohomologyEquivDualHomology_relativeCohomologyToAbsolute ℚ
      bh9_torusPair 2 a z).symm.trans ((hz _).trans ((h a).trans
        (relativeCohomologyEquivDualHomology_relativeCohomologyMap ℚ 2
          bh9_squareTorusMap a bh5_diskClass)))
  · intro h a
    exact (hz _).symm.trans
      ((cohomologyEquivDualHomology_relativeCohomologyToAbsolute ℚ
        bh9_torusPair 2 a z).trans
        ((congrArg (relativeCohomologyEquivDualHomology ℚ bh9_torusPair 2 a) h).trans
          (relativeCohomologyEquivDualHomology_relativeCohomologyMap ℚ 2
            bh9_squareTorusMap a bh5_diskClass).symm))

/-- Vanishing of subspace homology makes projection to relative homology injective.
Source: Hatcher, Algebraic Topology, section 2.1, the long exact sequence of a pair. -/
theorem bh9_relativeProjection_injective (P : TopPair)
    [Subsingleton (Homology ℚ P.snd 2)] :
    Function.Injective (relativeHomologyProjection ℚ P 2).hom := by
  have hzero := ModuleCat.isZero_of_subsingleton (Homology ℚ P.snd 2)
  have hex := (relativeChainShortComplex_shortExact ℚ P).homology_exact₂ 2
  exact (ModuleCat.mono_iff_injective _).mp (hex.mono_g (hzero.eq_of_src _ 0))

/-- Injectivity on degree-one subspace homology makes degree-two relative projection surjective.
Source: Hatcher, Algebraic Topology, section 2.1, the long exact sequence of a pair. -/
theorem bh9_relativeProjection_surjective (P : TopPair)
    (hi : Function.Injective (homologyMap ℚ 1 P.map)) :
    Function.Surjective (relativeHomologyProjection ℚ P 2).hom := by
  have hm : Mono (HomologicalComplex.homologyMap
      (relativeChainShortComplex ℚ P).f 1) :=
    (ModuleCat.mono_iff_injective _).mpr hi
  have hz := ((relativeChainShortComplex_shortExact ℚ P).homology_exact₁ 2 1
    (ComplexShape.down_mk 2 1 (by omega))).mono_g_iff.mp hm
  exact (ModuleCat.epi_iff_surjective _).mp
    ((relativeSingular_homology_exact_relative P 1).epi_f hz)

/-- The top monomial uses the real coordinate first and the imaginary coordinate second.
Source: `torusMonomialBasis_apply` and the increasing enumeration of `Fin 2`. -/
theorem bh9_topMonomial_eq_cup :
    torusMonomialBasis 2 2 (Set.powersetCard.ofCard
      (by simp : (Finset.univ : Finset (Fin 2)).card = 2)) =
    cup (R := ℚ) (TopCat.of (UnitAddTorus (Fin 2))) (p := 1) (q := 1) (k := 2) rfl
      (torusCoordinateClass 0) (torusCoordinateClass 1) := by
  let I : Set.powersetCard (Fin 2) 2 := Set.powersetCard.ofCard
    (by simp : (Finset.univ : Finset (Fin 2)).card = 2)
  have hmono := (Set.powersetCard.ofFinEmbEquiv.symm I).strictMono
  have hI0 : Set.powersetCard.ofFinEmbEquiv.symm I 0 = 0 := by
    have h := hmono (by decide : (0 : Fin 2) < 1)
    omega
  have hI1 : Set.powersetCard.ofFinEmbEquiv.symm I 1 = 1 := by
    have h := hmono (by decide : (0 : Fin 2) < 1)
    omega
  change torusMonomialBasis 2 2 I = _
  rw [torusMonomialBasis_apply, cupMulti_succ _ 1 rfl, cupMulti_succ _ 0 rfl,
    cupMulti_zero, cup_one, hI0]
  simp only [Fin.tail]
  rw [show (Fin.succ 0 : Fin 2) = 1 by rfl, hI1]

/-- The increasing ordered product has coefficient one.
Source: the coordinate functional of `torusMonomialBasis`. -/
theorem bh9_coefficient_cup :
    bh8_torusCoefficient (cup (R := ℚ) (TopCat.of (UnitAddTorus (Fin 2))) (p := 1) (q := 1) (k := 2) rfl
      (torusCoordinateClass 0) (torusCoordinateClass 1)) = 1 := by
  rw [← bh9_topMonomial_eq_cup]
  simp only [bh8_torusCoefficient, Module.Basis.coord_apply,
    Module.Basis.repr_self, Finsupp.single_eq_same]

private theorem bh9_centeredArc_zero :
    (0 : UnitAddCircle) ∈ circleArc (-(1 / 2 : ℝ)) := by
  change (0 : UnitAddCircle) ≠ ((-(1 / 2 : ℝ)) : UnitAddCircle)
  intro h
  have hh := (AddCircle.coe_eq_coe_iff_of_mem_Ico (p := (1 : ℝ))
    (a := -(1 / 2 : ℝ)) (x := 0) (y := -(1 / 2 : ℝ))
    (by constructor <;> norm_num) (by constructor <;> norm_num)).mp h
  norm_num at hh

private def bh9_skeletonOpen (i : Fin 2) : Set bh9_torusSkeleton :=
  {t | t.val i ∈ circleArc (-(1 / 2 : ℝ))}

private theorem bh9_skeletonOpen_isOpen (i : Fin 2) : IsOpen (bh9_skeletonOpen i) :=
  (isOpen_circleArc _).preimage ((continuous_apply i).comp continuous_subtype_val)

/-- Cutting each coordinate circle away from the vertex gives an open cover of the skeleton.
Source: Hatcher, Algebraic Topology, section 2.2, the two-circle skeleton of the torus. -/
theorem bh9_skeleton_open_cover : bh9_skeletonOpen 0 ∪ bh9_skeletonOpen 1 = Set.univ := by
  apply Set.eq_univ_of_forall
  intro t
  rcases t.property with h | h
  · exact Or.inl (by change t.val 0 ∈ circleArc (-(1 / 2 : ℝ)); rw [h]; exact bh9_centeredArc_zero)
  · exact Or.inr (by change t.val 1 ∈ circleArc (-(1 / 2 : ℝ)); rw [h]; exact bh9_centeredArc_zero)

private def bh9_arcContract (s : unitInterval) (z : circleArc (-(1 / 2 : ℝ))) :
    circleArc (-(1 / 2 : ℝ)) :=
  circleArcHomeomorph _ ⟨(1 - (s : ℝ)) *
    ((circleArcHomeomorph _).symm z).val, by
      have h := ((circleArcHomeomorph (-(1 / 2 : ℝ))).symm z).property
      simpa only [smul_eq_mul, mul_zero, zero_add] using
        (convex_Ioo (-(1 / 2 : ℝ)) (-(1 / 2 : ℝ) + 1))
          (by constructor <;> norm_num : (0 : ℝ) ∈ Set.Ioo _ _) h
          s.property.1 (sub_nonneg.mpr s.property.2) (by ring)⟩

private theorem bh9_arcContract_continuous :
    Continuous (fun p : unitInterval × circleArc (-(1 / 2 : ℝ)) ↦
      bh9_arcContract p.1 p.2) := by
  unfold bh9_arcContract
  fun_prop

private theorem bh9_arcContract_start (z : circleArc (-(1 / 2 : ℝ))) :
    bh9_arcContract 0 z = z := by
  unfold bh9_arcContract
  convert (circleArcHomeomorph (-(1 / 2 : ℝ))).apply_symm_apply z using 1
  simp only [show (0 : unitInterval).val = 0 from rfl, sub_zero, one_mul]

private theorem bh9_arcContract_end (z : circleArc (-(1 / 2 : ℝ))) :
    (bh9_arcContract 1 z).val = 0 := by
  change (((1 - (1 : unitInterval).val) *
    ((circleArcHomeomorph _).symm z).val : ℝ) : UnitAddCircle) = 0
  simp only [show (1 : unitInterval).val = 1 from rfl, sub_self, zero_mul, AddCircle.coe_zero]

private theorem bh9_arcContract_zero (s : unitInterval) :
    (bh9_arcContract s ⟨0, bh9_centeredArc_zero⟩).val = 0 := by
  have h : (circleArcHomeomorph (-(1 / 2 : ℝ))).symm ⟨0, bh9_centeredArc_zero⟩ =
      ⟨0, by constructor <;> norm_num⟩ := by
    apply (circleArcHomeomorph _).injective
    rw [Homeomorph.apply_symm_apply]
    rfl
  change (((1 - (s : ℝ)) *
    ((circleArcHomeomorph _).symm ⟨0, bh9_centeredArc_zero⟩).val : ℝ) : UnitAddCircle) = 0
  rw [h]
  simp only [mul_zero, AddCircle.coe_zero]

private theorem bh9_arcContract_eq_zero (s : unitInterval)
    (z : circleArc (-(1 / 2 : ℝ))) (hz : z.val = 0) :
    (bh9_arcContract s z).val = 0 := by
  have h : z = ⟨0, bh9_centeredArc_zero⟩ := Subtype.ext hz
  rw [h]
  exact bh9_arcContract_zero s

private def bh9_skeletonContract (i : Fin 2) (s : unitInterval)
    (t : bh9_skeletonOpen i) : bh9_skeletonOpen i :=
  ⟨⟨fun k ↦ if k = i then (bh9_arcContract s ⟨t.val.val i, t.property⟩).val
        else t.val.val k, by
      have ht := t.val.property
      fin_cases i
      · rcases ht with h | h
        · exact Or.inl (by simpa using
            bh9_arcContract_eq_zero s ⟨t.val.val 0, t.property⟩ h)
        · exact Or.inr (by simpa using h)
      · rcases ht with h | h
        · exact Or.inl (by simpa using h)
        · exact Or.inr (by simpa using
            bh9_arcContract_eq_zero s ⟨t.val.val 1, t.property⟩ h)⟩, by
    change (if i = i then _ else _) ∈ circleArc (-(1 / 2 : ℝ))
    rw [ite_eq_left rfl]
    exact (bh9_arcContract s ⟨t.val.val i, t.property⟩).property⟩

private theorem bh9_skeletonContract_continuous (i : Fin 2) :
    Continuous (fun p : unitInterval × bh9_skeletonOpen i ↦
      bh9_skeletonContract i p.1 p.2) := by
  apply Continuous.subtype_mk
  apply Continuous.subtype_mk
  apply continuous_pi
  intro k
  by_cases h : k = i
  · simp only [ite_eq_left h]
    exact continuous_subtype_val.comp (bh9_arcContract_continuous.comp
      (continuous_fst.prodMk (((continuous_apply i).comp
        (continuous_subtype_val.comp (continuous_subtype_val.comp continuous_snd))).subtype_mk _)))
  · simp only [ite_eq_right h]
    exact (continuous_apply k).comp
      (continuous_subtype_val.comp (continuous_subtype_val.comp continuous_snd))

private def bh9_skeletonAxis (i j : Fin 2) (hij : i ≠ j) :
    C(UnitAddCircle, bh9_skeletonOpen i) :=
  ⟨fun z ↦ ⟨⟨fun k ↦ if k = j then z else 0, by
      fin_cases j
      · exact Or.inr (by simp)
      · exact Or.inl (by simp)⟩, by
      change (if i = j then z else 0) ∈ circleArc (-(1 / 2 : ℝ))
      rw [ite_eq_right hij]
      exact bh9_centeredArc_zero⟩, by
    apply Continuous.subtype_mk
    apply Continuous.subtype_mk
    apply continuous_pi
    intro k
    by_cases h : k = j <;> simp only [h, ite_true, ite_false] <;> fun_prop⟩

private def bh9_skeletonCircleEquiv (i j : Fin 2) (hij : i ≠ j) :
    ContinuousMap.HomotopyEquiv (bh9_skeletonOpen i) UnitAddCircle where
  toFun := ⟨fun t ↦ t.val.val j,
    (continuous_apply j).comp (continuous_subtype_val.comp continuous_subtype_val)⟩
  invFun := bh9_skeletonAxis i j hij
  left_inv := by
    apply ContinuousMap.Homotopic.symm
    refine ⟨⟨⟨fun p ↦ bh9_skeletonContract i p.1 p.2,
      bh9_skeletonContract_continuous i⟩, ?_, ?_⟩⟩
    · intro t
      apply Subtype.ext
      apply Subtype.ext
      funext k
      change (if k = i then _ else _) = _
      rw [bh9_arcContract_start]
      split_ifs with h
      · subst k; rfl
      · rfl
    · intro t
      apply Subtype.ext
      apply Subtype.ext
      funext k
      change (if k = i then _ else _) = (if k = j then _ else _)
      rw [bh9_arcContract_end]
      fin_cases i <;> fin_cases j <;> fin_cases k <;> simp_all
  right_inv := by
    convert ContinuousMap.Homotopic.refl (ContinuousMap.id UnitAddCircle) using 1
    ext z
    simp [bh9_skeletonAxis]

private def bh9_skeletonOverlapContract (s : unitInterval)
    (t : (bh9_skeletonOpen 0 ∩ bh9_skeletonOpen 1 : Set bh9_torusSkeleton)) :
    (bh9_skeletonOpen 0 ∩ bh9_skeletonOpen 1 : Set bh9_torusSkeleton) :=
  ⟨⟨![(bh9_arcContract s ⟨t.val.val 0, t.property.1⟩).val,
      (bh9_arcContract s ⟨t.val.val 1, t.property.2⟩).val], by
    rcases t.val.property with h | h
    · exact Or.inl (bh9_arcContract_eq_zero s ⟨t.val.val 0, t.property.1⟩ h)
    · exact Or.inr (bh9_arcContract_eq_zero s ⟨t.val.val 1, t.property.2⟩ h)⟩,
    (bh9_arcContract s ⟨t.val.val 0, t.property.1⟩).property,
    (bh9_arcContract s ⟨t.val.val 1, t.property.2⟩).property⟩

private theorem bh9_skeletonOverlapContract_continuous :
    Continuous (fun p : unitInterval ×
      (bh9_skeletonOpen 0 ∩ bh9_skeletonOpen 1 : Set bh9_torusSkeleton) ↦
      bh9_skeletonOverlapContract p.1 p.2) := by
  apply Continuous.subtype_mk
  apply Continuous.subtype_mk
  apply continuous_pi
  intro k
  fin_cases k
  · exact continuous_subtype_val.comp (bh9_arcContract_continuous.comp
      (continuous_fst.prodMk (((continuous_apply 0).comp
        (continuous_subtype_val.comp (continuous_subtype_val.comp continuous_snd))).subtype_mk
          (fun p : unitInterval × (bh9_skeletonOpen 0 ∩ bh9_skeletonOpen 1 : Set bh9_torusSkeleton) ↦ p.2.property.1))))
  · exact continuous_subtype_val.comp (bh9_arcContract_continuous.comp
      (continuous_fst.prodMk (((continuous_apply 1).comp
        (continuous_subtype_val.comp (continuous_subtype_val.comp continuous_snd))).subtype_mk
          (fun p : unitInterval × (bh9_skeletonOpen 0 ∩ bh9_skeletonOpen 1 : Set bh9_torusSkeleton) ↦ p.2.property.2))))

/-- The overlap of the two skeleton charts contracts to their common vertex.
Source: Hatcher, Algebraic Topology, section 2.2, the contractible cross in a two-circle wedge. -/
theorem bh9_skeleton_overlap_contractible :
    ContractibleSpace (bh9_skeletonOpen 0 ∩ bh9_skeletonOpen 1 : Set bh9_torusSkeleton) := by
  apply (contractible_iff_id_nullhomotopic _).mpr
  refine ⟨⟨⟨0, Or.inl rfl⟩, bh9_centeredArc_zero, bh9_centeredArc_zero⟩,
    ⟨⟨⟨fun p ↦ bh9_skeletonOverlapContract p.1 p.2,
      bh9_skeletonOverlapContract_continuous⟩, ?_, ?_⟩⟩⟩
  · intro t
    apply Subtype.ext
    apply Subtype.ext
    funext k
    fin_cases k <;> exact congrArg Subtype.val (bh9_arcContract_start _)
  · intro t
    apply Subtype.ext
    apply Subtype.ext
    funext k
    fin_cases k <;> exact bh9_arcContract_end _

private def bh9_skeletonOpenCohomologyEquiv (i j : Fin 2) (hij : i ≠ j) (n : ℕ) :
    Cohomology ℚ (TopCat.of (bh9_skeletonOpen i)) n ≃ₗ[ℚ]
      Cohomology ℚ (TopCat.of UnitAddCircle) n :=
  ((HomologicalComplex.linearDualHomotopyEquiv
    (AlgebraicTopology.singularChainHomotopyEquivOfHomotopyEquiv ℚ
      (bh9_skeletonCircleEquiv i j hij))).toHomologyIso n).symm.toLinearEquiv

/-- The skeleton has no rational cohomology in degree two.
Source: Hatcher, Algebraic Topology, section 3.1, Mayer–Vietoris for two circle charts
with contractible intersection. -/
theorem bh9_skeleton_cohomology_two_subsingleton :
    Subsingleton (Cohomology ℚ bh9_torusPair.snd 2) := by
  let Y := TopCat.of bh9_torusSkeleton
  let U := bh9_skeletonOpen 0
  let V := bh9_skeletonOpen 1
  let hU := bh9_skeletonOpen_isOpen 0
  let hV := bh9_skeletonOpen_isOpen 1
  let hUV := bh9_skeleton_open_cover
  let : Subsingleton (Cohomology ℚ (TopCat.of UnitAddCircle) 2) :=
    ModuleCat.subsingleton_of_isZero (isZero_cohomology_circle_add_two 0)
  let : Subsingleton (Cohomology ℚ (TopCat.of U) 2) :=
    (bh9_skeletonOpenCohomologyEquiv 0 1 (by decide) 2).injective.subsingleton
  let : Subsingleton (Cohomology ℚ (TopCat.of V) 2) :=
    (bh9_skeletonOpenCohomologyEquiv 1 0 (by decide) 2).injective.subsingleton
  let e := (mvCohomologySumIso Y U V 2 ≪≫ ModuleCat.biprodIsoProd _ _).toLinearEquiv
  let : Subsingleton ((mvCochainShortComplex Y U V).X₂.homology 2) := e.injective.subsingleton
  let : ContractibleSpace (U ∩ V : Set Y) := bh9_skeleton_overlap_contractible
  let : Subsingleton (Cohomology ℚ (TopCat.of (U ∩ V : Set Y)) 1) :=
    ModuleCat.subsingleton_of_isZero (isZero_cohomology_succ_of_contractible _ 0)
  have hz (a : Cohomology ℚ Y 2) : a = 0 := by
    obtain ⟨b, hb⟩ := (mv_exact₁ Y U V hU hV hUV 1 a).mp (Subsingleton.elim _ _)
    rw [Subsingleton.elim b 0, map_zero] at hb
    exact hb.symm
  exact ⟨fun a b ↦ (hz a).trans (hz b).symm⟩

/-- The two-circle skeleton has no rational homology in degree two.
Source: Hatcher, Algebraic Topology, sections 2.2 and 3.1; Mayer–Vietoris and
universal coefficients over the field of rational numbers. -/
theorem bh9_skeleton_homology_two_subsingleton :
    Subsingleton (Homology ℚ bh9_torusPair.snd 2) := by
  let := bh9_skeleton_cohomology_two_subsingleton
  let e := cohomologyEquivDualHomology ℚ bh9_torusPair.snd 2
  let : Subsingleton (Module.Dual ℚ (Homology ℚ bh9_torusPair.snd 2)) :=
    e.symm.injective.subsingleton
  refine ⟨fun x y ↦ Module.eval_apply_injective ℚ ?_⟩
  apply LinearMap.ext
  intro f
  rw [Subsingleton.elim f 0]
  rfl

/-- Passing from the torus to the torus relative to its skeleton loses no top homology.
Source: Hatcher, Algebraic Topology, section 2.1, the exact sequence of the pair
and vanishing of degree-two homology of the skeleton. -/
theorem bh9_torus_relativeProjection_injective :
    Function.Injective (relativeHomologyProjection ℚ bh9_torusPair 2).hom := by
  let := bh9_skeleton_homology_two_subsingleton
  exact bh9_relativeProjection_injective bh9_torusPair

private theorem bh9_skeleton_restriction_one_injective :
    Function.Injective (mvRestriction (TopCat.of bh9_torusSkeleton)
      (bh9_skeletonOpen 0) (bh9_skeletonOpen 1)
      (bh9_skeletonOpen_isOpen 0) (bh9_skeletonOpen_isOpen 1)
      bh9_skeleton_open_cover 1) := by
  let Y := TopCat.of bh9_torusSkeleton
  let U := bh9_skeletonOpen 0
  let V := bh9_skeletonOpen 1
  let hU := bh9_skeletonOpen_isOpen 0
  let hV := bh9_skeletonOpen_isOpen 1
  let hUV := bh9_skeleton_open_cover
  let : ContractibleSpace (U ∩ V : Set Y) := bh9_skeleton_overlap_contractible
  have hd (b : Cohomology ℚ (TopCat.of (U ∩ V : Set Y)) 0) :
      mvδ Y U V hU hV hUV 0 b = 0 := by
    obtain ⟨r, hr⟩ := exists_smul_unit (TopCat.of (U ∩ V : Set Y)) b
    apply (mv_exact₃ Y U V hU hV hUV 0 b).mpr
    refine ⟨((mvCohomologySumIso Y U V 0 ≪≫ ModuleCat.biprodIsoProd _ _).toLinearEquiv).symm
      (r • unit (TopCat.of U), 0), ?_⟩
    rw [mvDifference_sum_apply, map_smul, map_zero, sub_zero, cohomologyMap_unit]
    exact hr
  have hz (a : Cohomology ℚ Y 1) (ha : mvRestriction Y U V hU hV hUV 1 a = 0) :
      a = 0 := by
    obtain ⟨b, hb⟩ := (mv_exact₁ Y U V hU hV hUV 0 a).mp ha
    rw [hd] at hb
    exact hb.symm
  intro a b hab
  exact sub_eq_zero.mp (hz (a - b) (by rw [map_sub, hab, sub_self]))

private theorem bh9_skeletonOpenCohomologyEquiv_apply (i j : Fin 2) (hij : i ≠ j)
    (n : ℕ) (a : Cohomology ℚ (TopCat.of (bh9_skeletonOpen i)) n) :
    bh9_skeletonOpenCohomologyEquiv i j hij n a =
      cohomologyMap ℚ n (TopCat.ofHom (bh9_skeletonAxis i j hij)) a := by
  rfl

private def bh9_skeletonCircleAxis (j : Fin 2) : TopCat.of UnitAddCircle ⟶ bh9_torusPair.snd :=
  TopCat.ofHom ⟨fun z ↦ ⟨fun k ↦ if k = j then z else 0, by
    fin_cases j
    · exact Or.inr (by simp)
    · exact Or.inl (by simp)⟩, by
      apply Continuous.subtype_mk
      apply continuous_pi
      intro k
      by_cases h : k = j <;> simp only [h, ite_true, ite_false] <;> fun_prop⟩

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem bh9_skeleton_eq_of_axes (a b : Cohomology ℚ bh9_torusPair.snd 1)
    (h0 : cohomologyMap ℚ 1 (bh9_skeletonCircleAxis 0) a =
      cohomologyMap ℚ 1 (bh9_skeletonCircleAxis 0) b)
    (h1 : cohomologyMap ℚ 1 (bh9_skeletonCircleAxis 1) a =
      cohomologyMap ℚ 1 (bh9_skeletonCircleAxis 1) b) : a = b := by
  apply bh9_skeleton_restriction_one_injective
  apply ((mvCohomologySumIso (TopCat.of bh9_torusSkeleton)
    (bh9_skeletonOpen 0) (bh9_skeletonOpen 1) 1 ≪≫
      ModuleCat.biprodIsoProd _ _).toLinearEquiv).injective
  rw [mvRestriction_sum_apply, mvRestriction_sum_apply]
  apply Prod.ext
  · apply (bh9_skeletonOpenCohomologyEquiv 0 1 (by decide) 1).injective
    rw [bh9_skeletonOpenCohomologyEquiv_apply, bh9_skeletonOpenCohomologyEquiv_apply,
      ← LinearMap.comp_apply, ← cohomologyMap_comp,
      ← LinearMap.comp_apply, ← cohomologyMap_comp]
    exact h1
  · apply (bh9_skeletonOpenCohomologyEquiv 1 0 (by decide) 1).injective
    rw [bh9_skeletonOpenCohomologyEquiv_apply, bh9_skeletonOpenCohomologyEquiv_apply,
      ← LinearMap.comp_apply, ← cohomologyMap_comp,
      ← LinearMap.comp_apply, ← cohomologyMap_comp]
    exact h0

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem bh9_skeleton_axis_coordinate (i j : Fin 2) :
    cohomologyMap ℚ 1 (bh9_skeletonCircleAxis j)
      (cohomologyMap ℚ 1 bh9_torusPair.map (torusCoordinateClass i)) =
        if i = j then circleClass else 0 := by
  let axis : TopCat.of UnitAddCircle ⟶ TopCat.of (UnitAddTorus (Fin 2)) :=
    bh9_skeletonCircleAxis j ≫ bh9_torusPair.map
  unfold torusCoordinateClass
  rw [← LinearMap.comp_apply, ← cohomologyMap_comp]
  change cohomologyMap ℚ 1 axis
    (cohomologyMap ℚ 1 (TopCat.ofHom ⟨fun t : UnitAddTorus (Fin 2) ↦ t i,
      continuous_apply i⟩) circleClass) = _
  rw [← LinearMap.comp_apply, ← cohomologyMap_comp]
  by_cases h : i = j
  · subst i
    have he : axis ≫
        TopCat.ofHom ⟨fun t : UnitAddTorus (Fin 2) ↦ t j, continuous_apply j⟩ = 𝟙 _ := by
      ext z
      change (if j = j then z else 0) = z
      exact ite_eq_left rfl
    rw [he, cohomologyMap_id, ite_eq_left rfl]
    rfl
  · let f : TopCat.of UnitAddCircle ⟶ TopCat.of PUnit :=
      TopCat.ofHom ⟨fun _ ↦ PUnit.unit, continuous_const⟩
    let g : TopCat.of PUnit ⟶ TopCat.of UnitAddCircle :=
      TopCat.ofHom ⟨fun _ ↦ 0, continuous_const⟩
    have he : axis ≫
        TopCat.ofHom ⟨fun t : UnitAddTorus (Fin 2) ↦ t i, continuous_apply i⟩ = f ≫ g := by
      ext z
      change (if i = j then z else 0) = 0
      exact ite_eq_right h
    let := ModuleCat.subsingleton_of_isZero (isZero_cohomology_succ_of_contractible PUnit 0)
    rw [he, cohomologyMap_comp, LinearMap.comp_apply, Subsingleton.elim
      (cohomologyMap ℚ 1 g circleClass) 0, map_zero, ite_eq_right h]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Every degree-one class on the skeleton extends to the torus.
Source: Hatcher, Algebraic Topology, sections 2.2 and 3.1; the two coordinate
circle classes generate the first cohomology of the wedge. -/
theorem bh9_skeleton_cohomology_one_surjective :
    Function.Surjective (cohomologyMap ℚ 1 bh9_torusPair.map) := by
  intro a
  have h0 : cohomologyMap ℚ 1 (bh9_skeletonCircleAxis 0) a ∈
      Submodule.span ℚ {circleClass} := by
    rw [span_circleClass_eq_top]
    exact Submodule.mem_top
  have h1 : cohomologyMap ℚ 1 (bh9_skeletonCircleAxis 1) a ∈
      Submodule.span ℚ {circleClass} := by
    rw [span_circleClass_eq_top]
    exact Submodule.mem_top
  obtain ⟨r0, hr0⟩ := Submodule.mem_span_singleton.mp h0
  obtain ⟨r1, hr1⟩ := Submodule.mem_span_singleton.mp h1
  refine ⟨r0 • torusCoordinateClass 0 + r1 • torusCoordinateClass 1, ?_⟩
  apply bh9_skeleton_eq_of_axes
  · simp only [map_add, map_smul, bh9_skeleton_axis_coordinate, ite_true, ite_false,
      show (1 : Fin 2) ≠ 0 by decide, smul_zero, add_zero]
    exact hr0
  · simp only [map_add, map_smul, bh9_skeleton_axis_coordinate, ite_true, ite_false,
      show (0 : Fin 2) ≠ 1 by decide, smul_zero, zero_add]
    exact hr1

/-- Inclusion of the skeleton is injective on first rational homology.
Source: Hatcher, Algebraic Topology, section 3.1, naturality of universal coefficients
and extension of the two coordinate circle classes. -/
theorem bh9_skeleton_homology_one_injective :
    Function.Injective (homologyMap ℚ 1 bh9_torusPair.map) := by
  intro x y h
  apply Module.eval_apply_injective ℚ
  apply LinearMap.ext
  intro f
  obtain ⟨a, rfl⟩ := (cohomologyEquivDualHomology ℚ bh9_torusPair.snd 1).surjective f
  obtain ⟨b, rfl⟩ := bh9_skeleton_cohomology_one_surjective a
  change cohomologyEquivDualHomology ℚ _ 1 (cohomologyMap ℚ 1 _ b) x =
    cohomologyEquivDualHomology ℚ _ 1 (cohomologyMap ℚ 1 _ b) y
  rw [cohomologyEquivDualHomology_cohomologyMap,
    cohomologyEquivDualHomology_cohomologyMap, h]

/-- Absolute top homology maps bijectively to homology relative to the torus skeleton.
Source: Hatcher, Algebraic Topology, section 2.1, the exact sequence of the pair. -/
theorem bh9_torus_relativeProjection_bijective :
    Function.Bijective (relativeHomologyProjection ℚ bh9_torusPair 2).hom :=
  ⟨bh9_torus_relativeProjection_injective,
    bh9_relativeProjection_surjective bh9_torusPair bh9_skeleton_homology_one_injective⟩

/-- The relative top homology of the torus cell has rational dimension one.
Source: Hatcher, Algebraic Topology, section 2.2; the exact sequence of the torus
and its skeleton, together with the torus Betti-number computation. -/
theorem bh9_torus_relativeHomology_finrank :
    Module.finrank ℚ (RelativeHomology ℚ bh9_torusPair 2) = 1 := by
  let Y := TopCat.of (UnitAddTorus (Fin 2))
  let e := cohomologyEquivDualHomology ℚ Y 2
  let := finite_cohomology_unitAddTorus 2 2
  let : Module.Finite ℚ (Module.Dual ℚ (Homology ℚ Y 2)) := Module.Finite.equiv e
  let : Module.Finite ℚ (Homology ℚ Y 2) := (Module.finite_dual_iff ℚ).mp inferInstance
  let p := LinearEquiv.ofBijective (relativeHomologyProjection ℚ bh9_torusPair 2).hom
    bh9_torus_relativeProjection_bijective
  calc
    Module.finrank ℚ (RelativeHomology ℚ bh9_torusPair 2) =
        Module.finrank ℚ (Homology ℚ Y 2) := p.finrank_eq.symm
    _ = Module.finrank ℚ (Cohomology ℚ Y 2) := by
      rw [e.finrank_eq, Subspace.dual_finrank_eq]
    _ = 1 := by
      exact (finrank_cohomology_unitAddTorus 2 2).trans (by decide)

/-- Forgetting the skeleton gives an isomorphism on rational cohomology in degree two.
Source: Hatcher, Algebraic Topology, section 3.1, naturality of universal coefficients
and the top-homology isomorphism of the torus pair. -/
theorem bh9_torus_relativeCohomologyToAbsolute_bijective :
    Function.Bijective (relativeCohomologyToAbsolute ℚ bh9_torusPair 2) := by
  let p := LinearEquiv.ofBijective (relativeHomologyProjection ℚ bh9_torusPair 2).hom
    bh9_torus_relativeProjection_bijective
  let er := relativeCohomologyEquivDualHomology ℚ bh9_torusPair 2
  let ea := cohomologyEquivDualHomology ℚ bh9_torusPair.fst 2
  let e := er.trans (p.dualMap.trans ea.symm)
  have he : (e : RelativeCohomology ℚ bh9_torusPair 2 → Cohomology ℚ bh9_torusPair.fst 2) =
      relativeCohomologyToAbsolute ℚ bh9_torusPair 2 := by
    funext a
    apply ea.injective
    apply LinearMap.ext
    intro z
    change ea (ea.symm _) z = _
    rw [ea.apply_symm_apply]
    exact (cohomologyEquivDualHomology_relativeCohomologyToAbsolute ℚ bh9_torusPair 2 a z).symm
  rw [← he]
  exact e.bijective

/-- The increasing top cup product has a nonzero relative lift.
Source: Hatcher, Algebraic Topology, sections 2.2 and 3.2, the torus cell and its
increasing ordered cup basis. -/
theorem bh9_torus_topCup_relative_lift :
    ∃ a : RelativeCohomology ℚ bh9_torusPair 2,
      relativeCohomologyToAbsolute ℚ bh9_torusPair 2 a =
        cup (R := ℚ) (TopCat.of (UnitAddTorus (Fin 2))) (p := 1) (q := 1) (k := 2) rfl
          (torusCoordinateClass 0) (torusCoordinateClass 1) ∧ a ≠ 0 := by
  obtain ⟨a, ha⟩ := bh9_torus_relativeCohomologyToAbsolute_bijective.2
    (cup (R := ℚ) (TopCat.of (UnitAddTorus (Fin 2))) (p := 1) (q := 1) (k := 2) rfl
      (torusCoordinateClass 0) (torusCoordinateClass 1))
  refine ⟨a, ha, ?_⟩
  intro hz
  have hc := congrArg bh8_torusCoefficient ha
  rw [hz, map_zero] at hc
  change bh8_torusCoefficient (0 : Cohomology ℚ (TopCat.of (UnitAddTorus (Fin 2))) 2) = _ at hc
  rw [map_zero, bh9_coefficient_cup] at hc
  exact zero_ne_one hc

/-- A map that is a homeomorphism in neighborhoods of its unique point fiber
induces an isomorphism on local rational homology.
Source: Hatcher, Algebraic Topology, section 2.1, excision at a point. -/
theorem bh9_localHomology_bijective_of_chart
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] [T1Space X] [T1Space Y]
    (x : X) (y : Y) (f : pointComplementPair x ⟶ pointComplementPair y)
    (hf : ∀ z : X, TopPair.Hom.fst f z = y ↔ z = x)
    (U : Set X) (V : Set Y) (hU : IsOpen U) (hV : IsOpen V) (hx : x ∈ U) (hy : y ∈ V)
    (e : U ≃ₜ V) (he : ∀ u : U, TopPair.Hom.fst f u.val = (e u).val) (n : ℕ) :
    Function.Bijective (relativeHomologyMap ℚ n f) := by
  let ep : neighborhoodPointComplementPair U x ≅ neighborhoodPointComplementPair V y :=
    TopPair.isoOfSubset e (fun u ↦ by
      change (e u).val ≠ y ↔ u.val ≠ x
      rw [← he]
      exact not_congr (hf u.val))
  have hcomm : neighborhoodPointComplementPairMap U x ≫ f =
      ep.hom ≫ neighborhoodPointComplementPairMap V y := by
    apply MorphismProperty.Arrow.Hom.ext
    · ext u
      apply Subtype.ext
      have hw := ConcreteCategory.congr_hom (TopPair.Hom.w f) ⟨u.val.val, u.property⟩
      exact hw.trans (he u.val)
    · ext u
      exact he u
  have hleft := neighborhoodPointComplement_relativeHomologyMap_bijective U x hU hx n
  have hright := neighborhoodPointComplement_relativeHomologyMap_bijective V y hV hy n
  have heq : Function.Bijective (relativeHomologyMap ℚ n ep.hom) :=
    ((relativeHomologyFunctor ℚ n).mapIso ep).toLinearEquiv.bijective
  have hcomp : Function.Bijective ((relativeHomologyMap ℚ n f).comp
      (relativeHomologyMap ℚ n (neighborhoodPointComplementPairMap U x))) := by
    rw [← relativeHomologyMap_comp, hcomm, relativeHomologyMap_comp]
    exact hright.comp heq
  constructor
  · intro a b hab
    obtain ⟨a', rfl⟩ := hleft.2 a
    obtain ⟨b', rfl⟩ := hleft.2 b
    exact congrArg (relativeHomologyMap ℚ n (neighborhoodPointComplementPairMap U x))
      (hcomp.1 hab)
  · intro b
    obtain ⟨a, ha⟩ := hcomp.2 b
    exact ⟨relativeHomologyMap ℚ n (neighborhoodPointComplementPairMap U x) a, ha⟩

private def bh9_openSquare : Set (Fin 1 → ℂ) :=
  {q | (q 0).re ∈ Set.Ioo (-1 : ℝ) 1 ∧ (q 0).im ∈ Set.Ioo (-1 : ℝ) 1}

private theorem bh9_openSquare_isOpen : IsOpen bh9_openSquare :=
  (isOpen_Ioo.preimage (Complex.continuous_re.comp (continuous_apply 0))).inter
    (isOpen_Ioo.preimage (Complex.continuous_im.comp (continuous_apply 0)))

private theorem bh9_openSquare_zero : (0 : Fin 1 → ℂ) ∈ bh9_openSquare := by
  constructor <;> constructor <;> norm_num

private def bh9_openSquareParams : bh9_openSquare ≃ₜ
    (Set.Ioo (0 : ℝ) 1 × Set.Ioo (0 : ℝ) 1) where
  toFun q := (⟨((q.val 0).re + 1) / 2, by
    have h := q.property.1; constructor <;> linarith [h.1, h.2]⟩,
    ⟨((q.val 0).im + 1) / 2, by
    have h := q.property.2; constructor <;> linarith [h.1, h.2]⟩)
  invFun p := ⟨fun _ ↦ Complex.mk (2 * p.1.val - 1) (2 * p.2.val - 1), by
    constructor
    · change -1 < 2 * p.1.val - 1 ∧ 2 * p.1.val - 1 < 1
      constructor <;> linarith [p.1.property.1, p.1.property.2]
    · change -1 < 2 * p.2.val - 1 ∧ 2 * p.2.val - 1 < 1
      constructor <;> linarith [p.2.property.1, p.2.property.2]⟩
  left_inv q := by
    apply Subtype.ext
    funext i
    fin_cases i
    apply Complex.ext <;> dsimp <;> ring
  right_inv p := by
    apply Prod.ext <;> apply Subtype.ext <;> dsimp <;> ring
  continuous_toFun := by
    apply Continuous.prodMk
    · apply Continuous.subtype_mk
      exact ((Complex.continuous_re.comp ((continuous_apply 0).comp continuous_subtype_val)).add
        continuous_const).div_const 2
    · apply Continuous.subtype_mk
      exact ((Complex.continuous_im.comp ((continuous_apply 0).comp continuous_subtype_val)).add
        continuous_const).div_const 2
  continuous_invFun := by
    apply Continuous.subtype_mk
    apply continuous_pi
    intro i
    change Continuous (fun p : Set.Ioo (0 : ℝ) 1 × Set.Ioo (0 : ℝ) 1 ↦
      Complex.equivRealProdCLM.symm (2 * p.1.val - 1, 2 * p.2.val - 1))
    exact Complex.equivRealProdCLM.symm.continuous.comp
      (((continuous_const.mul (continuous_subtype_val.comp continuous_fst)).sub continuous_const).prodMk
        ((continuous_const.mul (continuous_subtype_val.comp continuous_snd)).sub continuous_const))

private theorem bh9_squareTorus_chart (q : bh9_openSquare) :
    bh9_squareTorus q.val =
      (bh9_openCellHomeomorph (bh9_openSquareParams q)).val := by
  have hq : (fun _ : Fin 1 ↦ Complex.mk
      (2 * (bh9_openSquareParams q).1.val - 1)
      (2 * (bh9_openSquareParams q).2.val - 1)) = q.val :=
    congrArg Subtype.val (bh9_openSquareParams.symm_apply_apply q)
  conv_lhs => rw [← hq]
  exact bh9_squareTorus_openCell (bh9_openSquareParams q)

private theorem bh9_half_ne_zero : ((1 / 2 : ℝ) : UnitAddCircle) ≠ 0 := by
  intro h
  have hh := (AddCircle.coe_eq_coe_iff_of_mem_Ico (p := (1 : ℝ)) (a := 0)
    (x := 1 / 2) (y := 0) (by constructor <;> norm_num)
    (by constructor <;> norm_num)).mp h
  norm_num at hh

private theorem bh9_clamp_eq_half (r : ℝ)
    (h : (bh5_clamp r : UnitAddCircle) = ((1 / 2 : ℝ) : UnitAddCircle)) :
    r = 1 / 2 := by
  have hlo : 0 ≤ bh5_clamp r := le_max_left _ _
  have hhi : bh5_clamp r ≤ 1 := max_le (by norm_num) (min_le_left _ _)
  have hne : bh5_clamp r ≠ 1 := by
    intro hh
    rw [hh, AddCircle.coe_period] at h
    exact bh9_half_ne_zero h.symm
  have hr := (AddCircle.coe_eq_coe_iff_of_mem_Ico (p := (1 : ℝ)) (a := 0)
    (x := bh5_clamp r) (y := 1 / 2) ⟨hlo, by simpa only [zero_add] using lt_of_le_of_ne hhi hne⟩
    (by constructor <;> norm_num)).mp h
  unfold bh5_clamp at hr
  rcases le_total r 0 with h0 | h0
  · rw [min_eq_right (by linarith), max_eq_left h0] at hr
    norm_num at hr
  · rcases le_total 1 r with h1 | h1
    · rw [min_eq_left h1, max_eq_right (by norm_num)] at hr
      norm_num at hr
    · rwa [min_eq_right h1, max_eq_right h0] at hr

/-- The center of the open torus cell has exactly one preimage under the clamped square.
Source: the affine coordinate formula and injectivity of the circle quotient on the open unit interval. -/
theorem bh9_squareTorus_center_fiber (q : Fin 1 → ℂ) :
    bh9_squareTorus q = bh9_squareTorus 0 ↔ q = 0 := by
  constructor
  · intro h
    have hr := congrFun h 0
    have hi := congrFun h 1
    change (bh5_clamp (((q 0).re + 1) / 2) : UnitAddCircle) =
      (bh5_clamp ((0 + 1) / 2) : UnitAddCircle) at hr
    change (bh5_clamp (((q 0).im + 1) / 2) : UnitAddCircle) =
      (bh5_clamp ((0 + 1) / 2) : UnitAddCircle) at hi
    have hc : bh5_clamp ((0 + 1) / 2) = 1 / 2 := by norm_num [bh5_clamp]
    rw [hc] at hr hi
    have hr' := bh9_clamp_eq_half (((q 0).re + 1) / 2) hr
    have hi' := bh9_clamp_eq_half (((q 0).im + 1) / 2) hi
    funext i
    fin_cases i
    apply Complex.ext <;> dsimp <;> linarith
  · rintro rfl
    rfl

private theorem bh9_torusSkeleton_isClosed : IsClosed bh9_torusSkeleton :=
  (isClosed_eq (continuous_apply 0) continuous_const).union
    (isClosed_eq (continuous_apply 1) continuous_const)

private theorem bh9_squareTorus_center_mem :
    bh9_squareTorus 0 ∈ bh9_torusSkeletonᶜ := by
  rw [bh9_squareTorus_chart ⟨0, bh9_openSquare_zero⟩]
  exact (bh9_openCellHomeomorph (bh9_openSquareParams ⟨0, bh9_openSquare_zero⟩)).property

private def bh9_squareTorusLocalMap :
    pointComplementPair (0 : Fin 1 → ℂ) ⟶ pointComplementPair (bh9_squareTorus 0) :=
  TopPair.ofSubsetHom (TopCat.ofHom bh9_squareTorus) (fun q hq h ↦
    hq ((bh9_squareTorus_center_fiber q).mp h))

private def bh9_torusCellToLocal : bh9_torusPair ⟶ pointComplementPair (bh9_squareTorus 0) :=
  TopPair.ofSubsetHom (𝟙 _) (fun _t ht h ↦ bh9_squareTorus_center_mem (h ▸ ht))

private theorem bh9_squareTorusLocalMap_bijective :
    Function.Bijective (relativeHomologyMap ℚ 2 bh9_squareTorusLocalMap) := by
  exact bh9_localHomology_bijective_of_chart (0 : Fin 1 → ℂ) (bh9_squareTorus 0)
    bh9_squareTorusLocalMap bh9_squareTorus_center_fiber
    bh9_openSquare bh9_torusSkeletonᶜ bh9_openSquare_isOpen bh9_torusSkeleton_isClosed.isOpen_compl
    bh9_openSquare_zero bh9_squareTorus_center_mem
    (bh9_openSquareParams.trans bh9_openCellHomeomorph) bh9_squareTorus_chart 2

/-- The clamped square carries the disk class to a nonzero relative torus class.
Source: Hatcher, Algebraic Topology, section 2.1, point excision; near the center,
the clamped square is the ordered affine chart of the open torus cell. -/
theorem bh9_squareTorus_diskClass_ne_zero :
    relativeHomologyMap ℚ 2 bh9_squareTorusMap bh5_diskClass ≠ 0 := by
  let d : bh5_diskPair ⟶ puncturedPair ℂ 1 := supportInclusionPairMap (TopCat.of (Fin 1 → ℂ))
    (Set.singleton_subset_iff.mpr
      (Metric.mem_closedBall_self (by norm_num : (0 : ℝ) ≤ 2)))
  have hd : relativeHomologyMap ℚ 2 d bh5_diskClass = standardComplexLocalClass ℚ 1 :=
    bh9_diskClass_restrict
  have hc : d ≫ bh9_squareTorusLocalMap = bh9_squareTorusMap ≫ bh9_torusCellToLocal := by
    apply MorphismProperty.Arrow.Hom.ext <;> ext u <;> rfl
  intro h
  have hh := congrArg (relativeHomologyMap ℚ 2 bh9_torusCellToLocal) h
  rw [← LinearMap.comp_apply, ← relativeHomologyMap_comp, ← hc,
    relativeHomologyMap_comp, LinearMap.comp_apply, hd] at hh
  simp only [map_zero] at hh
  exact standardComplexLocalClass_ne_zero_for_chart 1
    (bh9_squareTorusLocalMap_bijective.1 (hh.trans (map_zero _).symm))

/-- The image of the prescribed disk class spans the relative top homology of the torus cell.
Source: Hatcher, Algebraic Topology, section 2.2; the relative group has dimension one,
and point excision detects the clamped square class as nonzero. -/
theorem bh9_squareTorus_diskClass_spans (z : RelativeHomology ℚ bh9_torusPair 2) :
    ∃ r : ℚ, r • relativeHomologyMap ℚ 2 bh9_squareTorusMap bh5_diskClass = z := by
  have hspan := (finrank_eq_one_iff_of_nonzero _ bh9_squareTorus_diskClass_ne_zero).mp
    bh9_torus_relativeHomology_finrank
  apply Submodule.mem_span_singleton.mp
  rw [hspan]
  exact Submodule.mem_top

open scoped Simplicial in
/-- On a cut circle, winding is the difference of the integer parts of the two lifted endpoints.
Source: Hatcher, Algebraic Topology, sections 1.1 and 3.1; lift the simplex through
`circleArcHomeomorph` and use invariance of winding under integer translation. -/
theorem bh9_circleWinding_arc (a : ℝ)
    (σ : (TopCat.toSSet.obj (TopCat.of (circleArc a))) _⦋1⦌) :
    circleWinding ((TopCat.toSSet.map
      (topologicalSubsetInclusion (TopCat.of UnitAddCircle) (circleArc a))).app _ σ) =
      ⌊((circleArcHomeomorph a).symm
        ((TopCat.of (circleArc a)).toSSetObjEquiv _ σ (Convexity.StdSimplex.single 1))).val⌋ -
      ⌊((circleArcHomeomorph a).symm
        ((TopCat.of (circleArc a)).toSSetObjEquiv _ σ (Convexity.StdSimplex.single 0))).val⌋ := by
  let F : C(Convexity.StdSimplex ℝ (Fin 2), ℝ) :=
    ⟨fun z ↦ ((circleArcHomeomorph a).symm
      ((TopCat.of (circleArc a)).toSSetObjEquiv _ σ z)).val,
      continuous_subtype_val.comp ((circleArcHomeomorph a).symm.continuous.comp
        ((TopCat.of (circleArc a)).toSSetObjEquiv _ σ).continuous)⟩
  apply circleWinding_eq _ F
  intro z
  exact congrArg Subtype.val ((circleArcHomeomorph a).apply_symm_apply
    ((TopCat.of (circleArc a)).toSSetObjEquiv _ σ z))

open scoped Simplicial in
/-- Winding vanishes on every singular edge that lies in the circle cut at zero.
Source: Hatcher, Algebraic Topology, section 1.1; the canonical lift takes values
strictly between zero and one, so both endpoint integer parts vanish. -/
theorem bh9_circleWinding_arc_zero
    (σ : (TopCat.toSSet.obj (TopCat.of (circleArc 0))) _⦋1⦌) :
    circleWinding ((TopCat.toSSet.map
      (topologicalSubsetInclusion (TopCat.of UnitAddCircle) (circleArc 0))).app _ σ) = 0 := by
  rw [bh9_circleWinding_arc]
  have hf (z : circleArc 0) : ⌊((circleArcHomeomorph 0).symm z).val⌋ = (0 : ℤ) := by
    apply Int.floor_eq_zero_iff.mpr
    exact ⟨((circleArcHomeomorph 0).symm z).property.1.le,
      by simpa only [zero_add] using ((circleArcHomeomorph 0).symm z).property.2⟩
  rw [hf, hf, sub_self]

/-- The clamped square induces an isomorphism in relative degree-two rational homology.
Source: Hatcher, Algebraic Topology, section 2.2; both groups are generated by the
prescribed disk class and its nonzero image. -/
theorem bh9_squareTorus_relativeHomology_bijective :
    Function.Bijective (relativeHomologyMap ℚ 2 bh9_squareTorusMap) := by
  constructor
  · intro x y h
    obtain ⟨r, hr⟩ := bh9_diskClass_spans (x - y)
    have hz : r • relativeHomologyMap ℚ 2 bh9_squareTorusMap bh5_diskClass = 0 := by
      rw [← map_smul, hr, map_sub, h, sub_self]
    have hr0 : r = 0 := (smul_eq_zero.mp hz).resolve_right bh9_squareTorus_diskClass_ne_zero
    rw [hr0, zero_smul] at hr
    exact sub_eq_zero.mp hr.symm
  · intro z
    obtain ⟨r, hr⟩ := bh9_squareTorus_diskClass_spans z
    exact ⟨r • bh5_diskClass, (map_smul _ _ _).trans hr⟩

/-- The cell comparison holds up to a single nonzero rational normalization factor.
Source: Hatcher, Algebraic Topology, sections 2.2 and 3.1; both homology classes
are nonzero generators of the same relative group, and evaluation is natural. -/
theorem bh9_torus_cell_up_to_nonzero_scalar :
    ∃ r : ℚ, r ≠ 0 ∧ ∀ a : RelativeCohomology ℚ bh9_torusPair 2,
      bh8_torusCoefficient (relativeCohomologyToAbsolute ℚ bh9_torusPair 2 a) =
        r * relativeCohomologyEquivDualHomology ℚ bh5_diskPair 2
          (relativeCohomologyMap ℚ 2 bh9_squareTorusMap a) bh5_diskClass := by
  obtain ⟨z, hz, -⟩ := bh9_torus_functional_representable bh8_torusCoefficient
  obtain ⟨r, hr⟩ := bh9_squareTorus_diskClass_spans
    ((relativeHomologyProjection ℚ bh9_torusPair 2).hom z)
  have he (a : RelativeCohomology ℚ bh9_torusPair 2) :
      bh8_torusCoefficient (relativeCohomologyToAbsolute ℚ bh9_torusPair 2 a) =
        r * relativeCohomologyEquivDualHomology ℚ bh5_diskPair 2
          (relativeCohomologyMap ℚ 2 bh9_squareTorusMap a) bh5_diskClass := by
    calc
      _ = cohomologyEquivDualHomology ℚ _ 2
          (relativeCohomologyToAbsolute ℚ bh9_torusPair 2 a) z := (hz _).symm
      _ = relativeCohomologyEquivDualHomology ℚ bh9_torusPair 2 a
          ((relativeHomologyProjection ℚ bh9_torusPair 2).hom z) :=
        cohomologyEquivDualHomology_relativeCohomologyToAbsolute ℚ bh9_torusPair 2 a z
      _ = relativeCohomologyEquivDualHomology ℚ bh9_torusPair 2 a
          (r • relativeHomologyMap ℚ 2 bh9_squareTorusMap bh5_diskClass) :=
        congrArg (relativeCohomologyEquivDualHomology ℚ bh9_torusPair 2 a) hr.symm
      _ = r * relativeCohomologyEquivDualHomology ℚ bh9_torusPair 2 a
          (relativeHomologyMap ℚ 2 bh9_squareTorusMap bh5_diskClass) := map_smul _ _ _
      _ = _ := congrArg (r * ·)
        (relativeCohomologyEquivDualHomology_relativeCohomologyMap ℚ 2
          bh9_squareTorusMap a bh5_diskClass).symm
  refine ⟨r, ?_, he⟩
  intro hr0
  obtain ⟨a, ha, -⟩ := bh9_torus_topCup_relative_lift
  have h := he a
  rw [ha, bh9_coefficient_cup, hr0, zero_mul] at h
  exact one_ne_zero h

private def bh9_arcWindingPrimitive (a : ℝ) :
    AlgebraicTopology.Simplicial.Cochain ℚ (TopCat.toSSet.obj (TopCat.of (circleArc a))) 0 :=
  simplexCochain ℚ _ 0 (fun σ ↦
    (⌊((circleArcHomeomorph a).symm ((TopCat.of (circleArc a)).toSSetObjEquiv _ σ
      (Convexity.StdSimplex.single 0))).val⌋ : ℚ))

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
open scoped Simplicial in
/-- The integer-part zero-cochain on each cut circle is a primitive of winding.
Source: Hatcher, Algebraic Topology, sections 1.1 and 3.1; the singular coboundary
is the difference of endpoint values. -/
theorem bh9_arcWindingPrimitive_coboundary (a : ℝ)
    (σ : (TopCat.toSSet.obj (TopCat.of (circleArc a))) _⦋1⦌) :
    AlgebraicTopology.Simplicial.coboundary ℚ 0 (bh9_arcWindingPrimitive a)
      (AlgebraicTopology.Simplicial.chainOfSimplex ℚ σ) =
        (circleWinding ((TopCat.toSSet.map
          (topologicalSubsetInclusion (TopCat.of UnitAddCircle) (circleArc a))).app _ σ) : ℚ) := by
  have hface (i : Fin 2) :
      (TopCat.of (circleArc a)).toSSetObjEquiv _
        ((TopCat.toSSet.obj (TopCat.of (circleArc a))).δ i σ) (Convexity.StdSimplex.single 0) =
      (TopCat.of (circleArc a)).toSSetObjEquiv _ σ (Convexity.StdSimplex.single (i.succAbove 0)) := by
    rw [TopCat.toSSetObjEquiv_δ_apply, Convexity.StdSimplex.map_single]
  rw [AlgebraicTopology.Simplicial.coboundary_chainOfSimplex, Fin.sum_univ_two,
    bh9_circleWinding_arc]
  simp only [bh9_arcWindingPrimitive, simplexCochain_apply_chainOfSimplex]
  norm_num
  rw [hface, hface]
  simp only [
    show (0 : Fin 2).succAbove 0 = 1 from rfl,
    show (1 : Fin 2).succAbove 0 = 0 from rfl, sub_eq_add_neg]

/-- The half-cut lift has integer part one on the lower overlap arc.
Source: the quotient interval model of the circle; the lift of `t` lies at `t + 1`. -/
theorem bh9_halfArc_floor_lower (z : circleArc (1 / 2 : ℝ))
    (t : ℝ) (ht : t ∈ Set.Ioo (0 : ℝ) (1 / 2)) (hz : z.val = (t : UnitAddCircle)) :
    ⌊((circleArcHomeomorph (1 / 2 : ℝ)).symm z).val⌋ = (1 : ℤ) := by
  have hmem : t + 1 ∈ Set.Ioo (1 / 2 : ℝ) (1 / 2 + 1) := by
    constructor <;> linarith [ht.1, ht.2]
  have he : (circleArcHomeomorph (1 / 2 : ℝ)).symm z = ⟨t + 1, hmem⟩ := by
    apply (circleArcHomeomorph (1 / 2 : ℝ)).injective
    rw [Homeomorph.apply_symm_apply]
    apply Subtype.ext
    change z.val = ((t + 1 : ℝ) : UnitAddCircle)
    rw [AddCircle.coe_add_period]
    exact hz
  rw [he]
  apply Int.floor_eq_iff.mpr
  norm_num only [Int.cast_one]
  constructor <;> linarith [ht.1, ht.2]

/-- The half-cut lift has integer part zero on the upper overlap arc.
Source: the quotient interval model of the circle; the lift is `t` itself. -/
theorem bh9_halfArc_floor_upper (z : circleArc (1 / 2 : ℝ))
    (t : ℝ) (ht : t ∈ Set.Ioo (1 / 2 : ℝ) 1) (hz : z.val = (t : UnitAddCircle)) :
    ⌊((circleArcHomeomorph (1 / 2 : ℝ)).symm z).val⌋ = (0 : ℤ) := by
  have hmem : t ∈ Set.Ioo (1 / 2 : ℝ) (1 / 2 + 1) := by
    exact ⟨ht.1, by linarith [ht.2]⟩
  have he : (circleArcHomeomorph (1 / 2 : ℝ)).symm z = ⟨t, hmem⟩ := by
    apply (circleArcHomeomorph (1 / 2 : ℝ)).injective
    rw [Homeomorph.apply_symm_apply]
    exact Subtype.ext hz
  rw [he]
  exact Int.floor_eq_zero_iff.mpr ⟨by linarith [ht.1], ht.2⟩

open scoped Simplicial in
private theorem bh9_cochain_ext {Y : SSet.{0}} {n : ℕ}
    {f g : AlgebraicTopology.Simplicial.Cochain ℚ Y n}
    (h : ∀ σ : Y _⦋n⦌, f (AlgebraicTopology.Simplicial.chainOfSimplex ℚ σ) =
      g (AlgebraicTopology.Simplicial.chainOfSimplex ℚ σ)) : f = g := by
  have he : ModuleCat.ofHom f = ModuleCat.ofHom g := by
    apply SSet.chainComplex_hom_ext
    intro σ
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro r
    have hi : (Y.ιChainComplex (R := ModuleCat.of ℚ ℚ) σ).hom r =
        r • AlgebraicTopology.Simplicial.chainOfSimplex ℚ σ := by
      rw [AlgebraicTopology.Simplicial.chainOfSimplex, ← map_smul]
      simp
    change f ((Y.ιChainComplex (R := ModuleCat.of ℚ ℚ) σ).hom r) =
      g ((Y.ιChainComplex (R := ModuleCat.of ℚ ℚ) σ).hom r)
    rw [hi, map_smul, map_smul, h]
  exact congrArg ModuleCat.Hom.hom he

/-- The winding cochain restricts to the coboundary of the integer-part primitive on a cut circle.
Source: Hatcher, Algebraic Topology, section 3.1; the endpoint formula for singular coboundaries. -/
theorem bh9_winding_restrict_eq_coboundary (a : ℝ) :
    AlgebraicTopology.Simplicial.cochainMap ℚ (TopCat.toSSet.map
      (topologicalSubsetInclusion (TopCat.of UnitAddCircle) (circleArc a))) 1
      circleWindingCochain =
    AlgebraicTopology.Simplicial.coboundary ℚ 0 (bh9_arcWindingPrimitive a) := by
  apply bh9_cochain_ext
  intro σ
  rw [bh9_arcWindingPrimitive_coboundary]
  simp only [AlgebraicTopology.Simplicial.cochainMap_apply,
    AlgebraicTopology.Simplicial.chainOfSimplex_map, circleWindingCochain,
    simplexCochain_apply_chainOfSimplex]

open scoped Simplicial in
private def bh9_squareTriangle (upper : Bool) :
    (TopCat.toSSet.obj (TopCat.of (UnitAddTorus (Fin 2)))) _⦋2⦌ :=
  ((TopCat.of (UnitAddTorus (Fin 2))).toSSetObjEquiv _).symm
    ⟨fun t ↦ if upper then
        ![(t.weights 2 : UnitAddCircle), ((t.weights 1 + t.weights 2 : ℝ) : UnitAddCircle)]
      else ![((t.weights 1 + t.weights 2 : ℝ) : UnitAddCircle), (t.weights 2 : UnitAddCircle)],
      by cases upper <;> dsimp <;> fun_prop⟩

open scoped Simplicial in
private theorem bh9_squareTriangle_faces (i : Fin 3) :
    (TopCat.toSSet.obj (TopCat.of (UnitAddTorus (Fin 2)))).δ i (bh9_squareTriangle false) =
      (TopCat.toSSet.obj (TopCat.of (UnitAddTorus (Fin 2)))).δ (2 - i) (bh9_squareTriangle true) := by
  apply ((TopCat.of (UnitAddTorus (Fin 2))).toSSetObjEquiv _).injective
  ext t j
  rw [TopCat.toSSetObjEquiv_δ_apply, TopCat.toSSetObjEquiv_δ_apply]
  have ht := t.total_of_fintype
  rw [Fin.sum_univ_two] at ht
  simp only [bh9_squareTriangle, Equiv.apply_symm_apply, ContinuousMap.coe_mk,
    Bool.false_eq_true, ↓reduceIte]
  fin_cases i <;> fin_cases j <;>
    simp only [Convexity.StdSimplex.weights_map_apply, Finset.sum_filter, Fin.sum_univ_succ,
      Finset.univ_unique, Finset.sum_singleton] <;>
    norm_num [ht, show Fin.succAbove (2 : Fin 3) (1 : Fin 2) = 1 from rfl,
      AddCircle.coe_period]

/-- The two ordered triangles of the unit square form an absolute singular torus cycle.
Source: Hatcher, Algebraic Topology, section 2.2; opposite square edges agree modulo one. -/
theorem bh9_squareTriangle_cycle :
    AlgebraicTopology.Simplicial.boundary ℚ 1
      (AlgebraicTopology.Simplicial.chainOfSimplex ℚ (bh9_squareTriangle false) -
        AlgebraicTopology.Simplicial.chainOfSimplex ℚ (bh9_squareTriangle true)) = 0 := by
  rw [map_sub, AlgebraicTopology.Simplicial.boundary_chainOfSimplex,
    AlgebraicTopology.Simplicial.boundary_chainOfSimplex]
  simp only [Fin.sum_univ_succ, Finset.univ_unique, Finset.sum_singleton,
    bh9_squareTriangle_faces]
  norm_num
  abel

private def bh9_squareTriangleLift (upper : Bool) :
    C(Convexity.StdSimplex ℝ (Fin 3), Fin 2 → ℝ) :=
  ⟨fun t ↦ if upper then ![t.weights 2, t.weights 1 + t.weights 2]
    else ![t.weights 1 + t.weights 2, t.weights 2],
    by cases upper <;> dsimp <;> fun_prop⟩

open scoped Simplicial in
private theorem bh9_squareTriangle_coordinate (upper : Bool)
    (t : Convexity.StdSimplex ℝ (Fin 3)) (j : Fin 2) :
    (TopCat.of (UnitAddTorus (Fin 2))).toSSetObjEquiv _ (bh9_squareTriangle upper) t j =
      (bh9_squareTriangleLift upper t j : UnitAddCircle) := by
  cases upper <;> fin_cases j <;> rfl

open scoped Simplicial in
/-- Each edge of an affine torus triangle has winding given by the lifted endpoint coordinates.
Source: Hatcher, Algebraic Topology, section 1.1; path lifting through the real universal cover. -/
theorem bh9_squareTriangle_winding (upper : Bool) (i : Fin 3) (j : Fin 2) :
    circleWinding ((TopCat.toSSet.map
      (TopCat.ofHom ⟨fun t : UnitAddTorus (Fin 2) ↦ t j, continuous_apply j⟩)).app _
        ((TopCat.toSSet.obj (TopCat.of (UnitAddTorus (Fin 2)))).δ i
          (bh9_squareTriangle upper))) =
      ⌊bh9_squareTriangleLift upper (Convexity.StdSimplex.single (i.succAbove 1)) j⌋ -
      ⌊bh9_squareTriangleLift upper (Convexity.StdSimplex.single (i.succAbove 0)) j⌋ := by
  let F : C(Convexity.StdSimplex ℝ (Fin 2), ℝ) :=
    ⟨fun t ↦ bh9_squareTriangleLift upper (Convexity.StdSimplex.map i.succAbove t) j,
      (continuous_apply j).comp ((bh9_squareTriangleLift upper).continuous.comp
        (Convexity.StdSimplex.continuous_map (R := ℝ) _))⟩
  have hv (k : Fin 2) : F (Convexity.StdSimplex.single k) =
      bh9_squareTriangleLift upper (Convexity.StdSimplex.single (i.succAbove k)) j := by
    simp only [F, ContinuousMap.coe_mk, Convexity.StdSimplex.map_single]
  rw [← hv 1, ← hv 0]
  apply circleWinding_eq _ F
  intro t
  change (bh9_squareTriangleLift upper (Convexity.StdSimplex.map i.succAbove t) j :
      UnitAddCircle) =
        (TopCat.of (UnitAddTorus (Fin 2))).toSSetObjEquiv _
          ((TopCat.toSSet.obj (TopCat.of (UnitAddTorus (Fin 2)))).δ i
            (bh9_squareTriangle upper)) t j
  rw [TopCat.toSSetObjEquiv_δ_apply, bh9_squareTriangle_coordinate]

private def bh9_coordinateWinding (j : Fin 2) :
    AlgebraicTopology.Simplicial.Cochain ℚ
      (TopCat.toSSet.obj (TopCat.of (UnitAddTorus (Fin 2)))) 1 :=
  AlgebraicTopology.Simplicial.cochainMap ℚ (TopCat.toSSet.map
    (TopCat.ofHom ⟨fun t : UnitAddTorus (Fin 2) ↦ t j, continuous_apply j⟩)) 1
      circleWindingCochain

open scoped Simplicial in
private theorem bh9_front_back_triangle (upper : Bool) :
    AlgebraicTopology.Simplicial.frontFace (p := 1) (q := 1)
      (TopCat.toSSet.obj (TopCat.of (UnitAddTorus (Fin 2)))) (bh9_squareTriangle upper) =
      (TopCat.toSSet.obj (TopCat.of (UnitAddTorus (Fin 2)))).δ 2 (bh9_squareTriangle upper) ∧
    AlgebraicTopology.Simplicial.backFace (p := 1) (q := 1)
      (TopCat.toSSet.obj (TopCat.of (UnitAddTorus (Fin 2)))) (bh9_squareTriangle upper) =
      (TopCat.toSSet.obj (TopCat.of (UnitAddTorus (Fin 2)))).δ 0 (bh9_squareTriangle upper) := by
  have hf : AlgebraicTopology.Simplicial.frontInclusion 1 1 =
      SimplexCategory.δ (2 : Fin 3) := by
    ext k
    fin_cases k <;> rfl
  have hb : AlgebraicTopology.Simplicial.backInclusion 1 1 =
      SimplexCategory.δ (0 : Fin 3) := by
    ext k
    fin_cases k <;> rfl
  constructor
  · simp only [AlgebraicTopology.Simplicial.frontFace, hf, SimplicialObject.δ_def]
  · simp only [AlgebraicTopology.Simplicial.backFace, hb, SimplicialObject.δ_def]

/-- The ordered winding cup cochain evaluates to one on the lower triangle and zero on the upper triangle.
Source: Hatcher, Algebraic Topology, section 3.2; the Alexander–Whitney front-edge/back-edge formula. -/
theorem bh9_windingCup_triangle (upper : Bool) :
    cupCochain (TopCat.of (UnitAddTorus (Fin 2))) 1 1
      (bh9_coordinateWinding 0) (bh9_coordinateWinding 1)
        (AlgebraicTopology.Simplicial.chainOfSimplex ℚ (bh9_squareTriangle upper)) =
      if upper then 0 else 1 := by
  rw [cupCochain_apply_simplex, (bh9_front_back_triangle upper).1,
    (bh9_front_back_triangle upper).2]
  simp only [bh9_coordinateWinding, AlgebraicTopology.Simplicial.cochainMap_apply,
    AlgebraicTopology.Simplicial.chainOfSimplex_map, circleWindingCochain,
    simplexCochain_apply_chainOfSimplex, bh9_squareTriangle_winding]
  cases upper <;> norm_num [bh9_squareTriangleLift,
    show Fin.succAbove (2 : Fin 3) (1 : Fin 2) = 1 from rfl]

/-- The ordered winding cup cochain has value one on the oriented square cycle.
Source: Hatcher, Algebraic Topology, Example 3.11; direct evaluation on the two square triangles. -/
theorem bh9_windingCup_square :
    cupCochain (TopCat.of (UnitAddTorus (Fin 2))) 1 1
      (bh9_coordinateWinding 0) (bh9_coordinateWinding 1)
        (AlgebraicTopology.Simplicial.chainOfSimplex ℚ (bh9_squareTriangle false) -
          AlgebraicTopology.Simplicial.chainOfSimplex ℚ (bh9_squareTriangle true)) = 1 := by
  rw [map_sub, bh9_windingCup_triangle, bh9_windingCup_triangle]
  norm_num

private def bh9_squareCycle :
    LinearMap.ker ((SingularChainComplex ℚ (TopCat.of (UnitAddTorus (Fin 2)))).sc 2).g.hom :=
  ⟨AlgebraicTopology.Simplicial.chainOfSimplex ℚ (bh9_squareTriangle false) -
    AlgebraicTopology.Simplicial.chainOfSimplex ℚ (bh9_squareTriangle true),
    by
      change ((SingularChainComplex ℚ (TopCat.of (UnitAddTorus (Fin 2)))).d
        2 ((ComplexShape.down ℕ).next 2)).hom _ = 0
      rw [ChainComplex.next_nat_succ]
      exact bh9_squareTriangle_cycle⟩

/-- The absolute torus homology class represented by the ordered two-triangle unit square.
Source: Hatcher, Algebraic Topology, section 2.2, the fundamental square with opposite edges identified. -/
def bh9_squareClass : Homology ℚ (TopCat.of (UnitAddTorus (Fin 2))) 2 :=
  ((SingularChainComplex ℚ (TopCat.of (UnitAddTorus (Fin 2)))).sc 2).moduleCatHomologyClass
    bh9_squareCycle

example : bh9_squareClass =
    ((SingularChainComplex ℚ (TopCat.of (UnitAddTorus (Fin 2)))).sc 2).moduleCatHomologyClass
      bh9_squareCycle := rfl

private theorem bh9_coordinateWinding_closed (j : Fin 2) :
    AlgebraicTopology.Simplicial.coboundary ℚ 1 (bh9_coordinateWinding j) = 0 := by
  rw [bh9_coordinateWinding, coboundary_cochainMap, coboundary_circleWindingCochain]
  exact map_zero _

private def bh9_windingCupCocycle : AlgebraicTopology.Simplicial.Cocycle ℚ
    (TopCat.toSSet.obj (TopCat.of (UnitAddTorus (Fin 2)))) 2 :=
  ⟨cupCochain (TopCat.of (UnitAddTorus (Fin 2))) 1 1
    (bh9_coordinateWinding 0) (bh9_coordinateWinding 1), by
    change AlgebraicTopology.Simplicial.coboundary ℚ (1 + 1)
      (cupCochain (TopCat.of (UnitAddTorus (Fin 2))) 1 1
        (bh9_coordinateWinding 0) (bh9_coordinateWinding 1)) = 0
    rw [coboundary_cupCochain, bh9_coordinateWinding_closed, bh9_coordinateWinding_closed]
    simp only [map_zero, LinearMap.zero_apply, LinearMap.zero_comp, smul_zero, add_zero]⟩

/-- The winding cup cocycle pairs to one with the explicit absolute square class.
Source: Hatcher, Algebraic Topology, sections 3.1–3.2; evaluation of a cocycle on a representing cycle. -/
theorem bh9_squareClass_winding_pairing :
    cohomologyEquivDualHomology ℚ (TopCat.of (UnitAddTorus (Fin 2))) 2
      (cohomologyClass (TopCat.of (UnitAddTorus (Fin 2))) 2 bh9_windingCupCocycle)
        bh9_squareClass = 1 := by
  rw [bh9_squareClass, cohomologyEquivDualHomology_cohomologyClass]
  exact bh9_windingCup_square

/-- The oriented square gives a nonzero absolute torus homology class.
Source: Hatcher, Algebraic Topology, Example 3.11; its ordered winding cup pairing is one. -/
theorem bh9_squareClass_ne_zero : bh9_squareClass ≠ 0 := by
  intro h
  have he := bh9_squareClass_winding_pairing
  rw [h, map_zero] at he
  exact zero_ne_one he

attribute [local implicit_reducible] ShortComplex.moduleCatMk ShortComplex.moduleCatLeftHomologyData

set_option backward.isDefEq.respectTransparency false in
/-- The singular cup product is represented by the Alexander–Whitney product of representing cocycles.
Source: Hatcher, Algebraic Topology, section 3.2, descent of the cochain cup product. -/
theorem bh9_cup_cohomologyClass (Y : TopCat.{0}) (p q : ℕ)
    (φ : AlgebraicTopology.Simplicial.Cocycle ℚ (TopCat.toSSet.obj Y) p)
    (ψ : AlgebraicTopology.Simplicial.Cocycle ℚ (TopCat.toSSet.obj Y) q)
    (η : AlgebraicTopology.Simplicial.Cocycle ℚ (TopCat.toSSet.obj Y) (p + q))
    (hη : η.1 = cupCochain Y p q φ.1 ψ.1) :
    cup Y rfl (cohomologyClass Y p φ) (cohomologyClass Y q ψ) =
      cohomologyClass Y (p + q) η := by
  let θ : AlgebraicTopology.Simplicial.Cocycle ℚ (TopCat.toSSet.obj Y) (p + q) :=
    ⟨cupCochain Y p q φ.1 ψ.1, hη ▸ η.property⟩
  unfold cup
  dsimp only [cohomologyClass, LinearMap.comp_apply, LinearEquiv.coe_coe]
  simp only [LinearMap.coe_mk, AddHom.coe_mk, LinearMap.coe_comp,
    Function.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
  change cohomologyClass Y (p + q) θ = cohomologyClass Y (p + q) η
  congr 1
  exact Subtype.ext hη.symm

set_option backward.isDefEq.respectTransparency false in
/-- The cocycle-class map agrees with the concrete homology class of the singular cochain complex.
Source: Hatcher, Algebraic Topology, section 3.1; the two quotient constructions of cohomology. -/
theorem bh9_cohomologyClass_cochain (Y : TopCat.{0}) (n : ℕ)
    (φ : AlgebraicTopology.Simplicial.Cocycle ℚ (TopCat.toSSet.obj Y) n)
    (hφ : ((SingularCochainComplex ℚ Y).sc n).g.hom φ.1 = 0) :
    cohomologyClass Y n φ =
      ((SingularCochainComplex ℚ Y).sc n).moduleCatHomologyClass ⟨φ.1, hφ⟩ := by
  let S := (SingularChainComplex ℚ Y).sc n
  let e := HomologicalComplex.linearDualCochainComplexScIso (SingularChainComplex ℚ Y) n
  let z : LinearMap.ker S.linearDual.g.hom := ⟨φ.1, by
    change (((SingularChainComplex ℚ Y).d ((ComplexShape.down ℕ).prev n) n).hom.dualMap)
      φ.1 = 0
    rw [ChainComplex.prev]
    exact φ.2⟩
  change (ShortComplex.homologyMap e.inv).hom (S.linearDual.moduleCatHomologyClass z) = _
  rw [ShortComplex.moduleCatHomologyClass_naturality]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- The categorical cycle lift and the concrete cycle quotient give the same homology element.
Source: the universal property of cycles and the concrete module homology quotient. -/
theorem bh9_liftCycles_class (K : CochainComplex (ModuleCat ℚ) ℕ) (n : ℕ)
    (x : ModuleCat.of ℚ ℚ ⟶ K.X n)
    (hx : x ≫ K.d n (n + 1) = 0)
    (z : LinearMap.ker (K.sc n).g.hom) (hz : x.hom 1 = z.1) :
    (K.liftCycles x (n + 1) (by simp) hx ≫ K.homologyπ n).hom 1 =
      (K.sc n).moduleCatHomologyClass z := by
  have he : (K.liftCycles x (n + 1) (by simp) hx).hom 1 =
      (K.sc n).moduleCatCyclesIso.inv.hom z := by
    apply (ModuleCat.mono_iff_injective (K.iCycles n)).mp inferInstance
    have hleft := ConcreteCategory.congr_hom (K.liftCycles_i x (n + 1) (by simp) hx) 1
    have hright := ConcreteCategory.congr_hom (K.sc n).moduleCatCyclesIso_inv_iCycles z
    exact hleft.trans (hz.trans hright.symm)
  change (K.homologyπ n).hom ((K.liftCycles x (n + 1) (by simp) hx).hom 1) = _
  rw [he]
  exact ConcreteCategory.congr_hom (K.sc n).moduleCatCyclesIso_inv_π z

set_option backward.isDefEq.respectTransparency false in
/-- The connecting homomorphism sends a lifted cocycle to the class of its lifted differential.
Source: Hatcher, Algebraic Topology, section 3.1; the cohomological connecting-map construction. -/
theorem bh9_connecting_class
    (S : CategoryTheory.ShortComplex (CochainComplex (ModuleCat ℚ) ℕ))
    (hS : S.ShortExact) (n : ℕ)
    (z₃ : LinearMap.ker (S.X₃.sc n).g.hom)
    (x₂ : S.X₂.X n)
    (z₁ : LinearMap.ker (S.X₁.sc (n + 1)).g.hom)
    (h₂ : (S.g.f n).hom x₂ = z₃.1)
    (h₁ : (S.f.f (n + 1)).hom z₁.1 = (S.X₂.d n (n + 1)).hom x₂) :
    (hS.δ n (n + 1) (by simp)).hom ((S.X₃.sc n).moduleCatHomologyClass z₃) =
      (S.X₁.sc (n + 1)).moduleCatHomologyClass z₁ := by
  let a₃ : ModuleCat.of ℚ ℚ ⟶ S.X₃.X n :=
    ModuleCat.ofHom (LinearMap.toSpanSingleton ℚ _ z₃.1)
  let a₂ : ModuleCat.of ℚ ℚ ⟶ S.X₂.X n :=
    ModuleCat.ofHom (LinearMap.toSpanSingleton ℚ _ x₂)
  let a₁ : ModuleCat.of ℚ ℚ ⟶ S.X₁.X (n + 1) :=
    ModuleCat.ofHom (LinearMap.toSpanSingleton ℚ _ z₁.1)
  have hz₃ : (S.X₃.d n (n + 1)).hom z₃.1 = 0 := by
    have h := z₃.property
    change (S.X₃.d n ((ComplexShape.up ℕ).next n)).hom z₃.1 = 0 at h
    rw [CochainComplex.next] at h
    exact h
  have ha₃ : a₃ ≫ S.X₃.d n (n + 1) = 0 := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro r
    change (S.X₃.d n (n + 1)).hom (r • z₃.1) = 0
    rw [map_smul, hz₃, smul_zero]
  have ha₂ : a₂ ≫ S.g.f n = a₃ := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro r
    change (S.g.f n).hom (r • x₂) = r • z₃.1
    rw [map_smul, h₂]
  have ha₁ : a₁ ≫ S.f.f (n + 1) = a₂ ≫ S.X₂.d n (n + 1) := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro r
    change (S.f.f (n + 1)).hom (r • z₁.1) = (S.X₂.d n (n + 1)).hom (r • x₂)
    rw [map_smul, map_smul, h₁]
  have h := ConcreteCategory.congr_hom
    (hS.δ_eq n (n + 1) (by simp) a₃ ha₃ a₂ ha₂ a₁ ha₁ (n + 1 + 1) (by simp)) 1
  have he₃ := bh9_liftCycles_class S.X₃ n a₃ ha₃ z₃ (by dsimp [a₃]; simp)
  have hz₁ : (S.X₁.d (n + 1) (n + 1 + 1)).hom z₁.1 = 0 := by
    have hz := z₁.property
    change (S.X₁.d (n + 1) ((ComplexShape.up ℕ).next (n + 1))).hom z₁.1 = 0 at hz
    rw [CochainComplex.next] at hz
    exact hz
  have hc₁ : a₁ ≫ S.X₁.d (n + 1) (n + 1 + 1) = 0 := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro r
    change (S.X₁.d (n + 1) (n + 1 + 1)).hom (r • z₁.1) = 0
    rw [map_smul, hz₁, smul_zero]
  have he₁ := bh9_liftCycles_class S.X₁ (n + 1) a₁ hc₁ z₁ (by dsimp [a₁]; simp)
  change (hS.δ n (n + 1) (by simp)).hom
    ((S.X₃.liftCycles a₃ (n + 1) (by simp) ha₃ ≫ S.X₃.homologyπ n).hom 1) =
      (S.X₁.liftCycles a₁ (n + 1 + 1) (by simp) _ ≫ S.X₁.homologyπ (n + 1)).hom 1 at h
  rw [he₃, he₁] at h
  exact h

private abbrev bh9_SlitInterval := {x : ℝ // 0 < x ∧ x < 1 ∧ x ≠ 1 / 2}

private theorem bh9_coe_interval_eq_half_iff (x : ℝ) (h0 : 0 < x) (h1 : x < 1) :
    (x : UnitAddCircle) = ((1 / 2 : ℝ) : UnitAddCircle) ↔ x = 1 / 2 :=
  AddCircle.coe_eq_coe_iff_of_mem_Ico (p := (1 : ℝ)) (a := 0)
    ⟨le_of_lt h0, by simpa using h1⟩ (by constructor <;> norm_num)

private def bh9_slitIntervalHomeomorph : bh9_SlitInterval ≃ₜ
    ↥(circleArc 0 ∩ circleArc (1 / 2)) where
  toFun x := ⟨(x.val : UnitAddCircle),
    (circleArcHomeomorph 0 ⟨x.val, x.2.1, by simpa using x.2.2.1⟩).2,
    fun h => x.2.2.2 ((bh9_coe_interval_eq_half_iff x.val x.2.1 x.2.2.1).mp h)⟩
  invFun y :=
    let x := (circleArcHomeomorph 0).symm ⟨y.val, y.2.1⟩
    ⟨x.val, x.2.1, by simpa using x.2.2, by
      intro hx
      have he : (x.val : UnitAddCircle) = y.val :=
        congrArg Subtype.val ((circleArcHomeomorph 0).apply_symm_apply ⟨y.val, y.2.1⟩)
      exact y.2.2 (he.symm.trans (congrArg (fun t : ℝ => (t : UnitAddCircle)) hx))⟩
  left_inv x := by
    apply Subtype.ext
    change ((circleArcHomeomorph 0).symm ((circleArcHomeomorph 0)
      ⟨x.val, x.2.1, by simpa using x.2.2.1⟩)).val = x.val
    exact congrArg Subtype.val ((circleArcHomeomorph 0).symm_apply_apply
      ⟨x.val, x.2.1, by simpa using x.2.2.1⟩)
  right_inv y := by
    apply Subtype.ext
    change ((circleArcHomeomorph 0) ((circleArcHomeomorph 0).symm ⟨y.val, y.2.1⟩)).val = y.val
    exact congrArg Subtype.val ((circleArcHomeomorph 0).apply_symm_apply ⟨y.val, y.2.1⟩)
  continuous_toFun := ((AddCircle.continuous_mk' (1 : ℝ)).comp continuous_subtype_val).subtype_mk _
  continuous_invFun :=
    (continuous_subtype_val.comp ((circleArcHomeomorph 0).symm.continuous.comp
      (continuous_subtype_val.subtype_mk _))).subtype_mk _

private def bh9_slitLeft : Set bh9_SlitInterval := {x | x.val < 1 / 2}
private def bh9_slitRight : Set bh9_SlitInterval := {x | 1 / 2 < x.val}

private def bh9_slitCohomologyEquiv (n : ℕ) :
    Cohomology ℚ (TopCat.of bh9_SlitInterval) n ≃ₗ[ℚ]
      (Cohomology ℚ (TopCat.of bh9_slitLeft) n × Cohomology ℚ (TopCat.of bh9_slitRight) n) :=
  cohomologyDisjointCoverEquiv (TopCat.of bh9_SlitInterval) bh9_slitLeft bh9_slitRight
    (isOpen_lt continuous_subtype_val continuous_const)
    (isOpen_lt continuous_const continuous_subtype_val)
    (Set.eq_univ_of_forall fun x => lt_or_gt_of_ne x.2.2.2)
    (Set.disjoint_left.mpr fun x h₁ h₂ => (not_lt_of_gt (show x.val < 1 / 2 from h₁)) h₂) n

private def bh9_overlapCohomologyEquiv (n : ℕ) :
    Cohomology ℚ (TopCat.of ↥(circleArc 0 ∩ circleArc (1 / 2))) n ≃ₗ[ℚ]
      (Cohomology ℚ (TopCat.of bh9_slitLeft) n × Cohomology ℚ (TopCat.of bh9_slitRight) n) :=
  (cohomologyHomeomorphEquiv bh9_slitIntervalHomeomorph.symm n).trans (bh9_slitCohomologyEquiv n)

private def bh9_overlapPrimitive : AlgebraicTopology.Simplicial.Cochain ℚ
    (TopCat.toSSet.obj (TopCat.of ↥(circleArc 0 ∩ circleArc (1 / 2)))) 0 :=
  AlgebraicTopology.Simplicial.cochainMap ℚ (TopCat.toSSet.map
    (subsetIntersectionToRight (TopCat.of UnitAddCircle) (circleArc 0) (circleArc (1 / 2)))) 0
      (bh9_arcWindingPrimitive (1 / 2))

private theorem bh9_overlapPrimitive_closed :
    AlgebraicTopology.Simplicial.coboundary ℚ 0 bh9_overlapPrimitive = 0 := by
  rw [bh9_overlapPrimitive, coboundary_cochainMap, ← bh9_winding_restrict_eq_coboundary]
  apply bh9_cochain_ext
  intro σ
  simp only [AlgebraicTopology.Simplicial.cochainMap_apply,
    AlgebraicTopology.Simplicial.chainOfSimplex_map, circleWindingCochain,
    simplexCochain_apply_chainOfSimplex, LinearMap.zero_apply]
  let σ₀ := (TopCat.toSSet.map (subsetIntersectionToLeft (TopCat.of UnitAddCircle)
    (circleArc 0) (circleArc (1 / 2)))).app _ σ
  change (circleWinding ((TopCat.toSSet.map
    (topologicalSubsetInclusion (TopCat.of UnitAddCircle) (circleArc 0))).app _ σ₀) : ℚ) = 0
  rw [bh9_circleWinding_arc_zero, Int.cast_zero]

private def bh9_overlapCocycle : AlgebraicTopology.Simplicial.Cocycle ℚ
    (TopCat.toSSet.obj (TopCat.of ↥(circleArc 0 ∩ circleArc (1 / 2)))) 0 :=
  ⟨bh9_overlapPrimitive, bh9_overlapPrimitive_closed⟩

/-- The chosen circle overlap indicator is fixed by the lower and upper interval components.
Source: the definition of `circleOverlapIndicator` via the two-component cohomology equivalence. -/
theorem bh9_circleOverlapIndicator_components :
    bh9_overlapCohomologyEquiv 0 circleOverlapIndicator =
      (unit (R := ℚ) (TopCat.of bh9_slitLeft), 0) := by
  exact (bh9_overlapCohomologyEquiv 0).apply_symm_apply _

private def bh9_lowerOverlapMap : TopCat.of bh9_slitLeft ⟶
    TopCat.of ↥(circleArc 0 ∩ circleArc (1 / 2)) :=
  topologicalSubsetInclusion (TopCat.of bh9_SlitInterval) bh9_slitLeft ≫
    TopCat.ofHom ⟨bh9_slitIntervalHomeomorph, bh9_slitIntervalHomeomorph.continuous⟩

private def bh9_upperOverlapMap : TopCat.of bh9_slitRight ⟶
    TopCat.of ↥(circleArc 0 ∩ circleArc (1 / 2)) :=
  topologicalSubsetInclusion (TopCat.of bh9_SlitInterval) bh9_slitRight ≫
    TopCat.ofHom ⟨bh9_slitIntervalHomeomorph, bh9_slitIntervalHomeomorph.continuous⟩

open scoped Simplicial in
private theorem bh9_overlapPrimitive_lower :
    AlgebraicTopology.Simplicial.cochainMap ℚ (TopCat.toSSet.map bh9_lowerOverlapMap) 0
      bh9_overlapPrimitive = unitCochain (R := ℚ) (TopCat.of bh9_slitLeft) := by
  apply bh9_cochain_ext
  intro σ
  rw [unitCochain_apply_simplex]
  simp only [bh9_overlapPrimitive, AlgebraicTopology.Simplicial.cochainMap_apply,
    AlgebraicTopology.Simplicial.chainOfSimplex_map, bh9_arcWindingPrimitive,
    simplexCochain_apply_chainOfSimplex]
  let t := (TopCat.of bh9_slitLeft).toSSetObjEquiv _ σ (Convexity.StdSimplex.single 0)
  have h := bh9_halfArc_floor_lower
    ⟨(t.val.val : UnitAddCircle), (bh9_slitIntervalHomeomorph t.val).property.2⟩
    t.val.val ⟨t.val.property.1, t.property⟩ rfl
  exact_mod_cast h

open scoped Simplicial in
private theorem bh9_overlapPrimitive_upper :
    AlgebraicTopology.Simplicial.cochainMap ℚ (TopCat.toSSet.map bh9_upperOverlapMap) 0
      bh9_overlapPrimitive = 0 := by
  apply bh9_cochain_ext
  intro σ
  simp only [bh9_overlapPrimitive, AlgebraicTopology.Simplicial.cochainMap_apply,
    AlgebraicTopology.Simplicial.chainOfSimplex_map, bh9_arcWindingPrimitive,
    simplexCochain_apply_chainOfSimplex, LinearMap.zero_apply]
  let t := (TopCat.of bh9_slitRight).toSSetObjEquiv _ σ (Convexity.StdSimplex.single 0)
  have h := bh9_halfArc_floor_upper
    ⟨(t.val.val : UnitAddCircle), (bh9_slitIntervalHomeomorph t.val).property.2⟩
    t.val.val ⟨t.property, t.val.property.2.1⟩ rfl
  exact_mod_cast h

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The half-cut integer-part cocycle represents the chosen lower-component overlap indicator.
Source: Hatcher, Algebraic Topology, section 3.1; its restrictions to the two overlap intervals are one and zero. -/
theorem bh9_overlapCocycle_class :
    cohomologyClass (TopCat.of ↥(circleArc 0 ∩ circleArc (1 / 2))) 0 bh9_overlapCocycle =
      circleOverlapIndicator := by
  have hl := cohomologyMap_class (R := ℚ)
    (TopCat.of ↥(circleArc 0 ∩ circleArc (1 / 2))) bh9_lowerOverlapMap 0
    bh9_overlapCocycle ⟨unitCochain (TopCat.of bh9_slitLeft), coboundary_unitCochain _⟩
    bh9_overlapPrimitive_lower.symm
  have hr := cohomologyMap_class (R := ℚ)
    (TopCat.of ↥(circleArc 0 ∩ circleArc (1 / 2))) bh9_upperOverlapMap 0
    bh9_overlapCocycle 0 bh9_overlapPrimitive_upper.symm
  rw [map_zero] at hr
  apply (bh9_overlapCohomologyEquiv 0).injective
  rw [bh9_circleOverlapIndicator_components]
  unfold bh9_overlapCohomologyEquiv bh9_slitCohomologyEquiv
  rw [LinearEquiv.trans_apply, cohomologyDisjointCoverEquiv_apply]
  change (cohomologyMap ℚ 0 (topologicalSubsetInclusion (TopCat.of bh9_SlitInterval) bh9_slitLeft)
      (cohomologyMap ℚ 0 (TopCat.ofHom ⟨bh9_slitIntervalHomeomorph,
        bh9_slitIntervalHomeomorph.continuous⟩) _),
    cohomologyMap ℚ 0 (topologicalSubsetInclusion (TopCat.of bh9_SlitInterval) bh9_slitRight)
      (cohomologyMap ℚ 0 (TopCat.ofHom ⟨bh9_slitIntervalHomeomorph,
        bh9_slitIntervalHomeomorph.continuous⟩) _)) = _
  apply Prod.ext
  · simpa only [bh9_lowerOverlapMap, cohomologyMap_comp, LinearMap.comp_apply, unit] using hl
  · simpa only [bh9_upperOverlapMap, cohomologyMap_comp, LinearMap.comp_apply] using hr

open HomologicalComplex CategoryTheory.Limits

set_option backward.isDefEq.respectTransparency false in
private theorem bh9_dual_add {K L : ChainComplex (ModuleCat ℚ) ℕ} (f g : K ⟶ L) :
    linearDualMap (f + g) = linearDualMap f + linearDualMap g := by
  ext n φ
  change Module.Dual ℚ (L.X n) at φ
  apply LinearMap.ext
  intro c
  change φ ((f.f n).hom c + (g.f n).hom c) = φ ((f.f n).hom c) + φ ((g.f n).hom c)
  exact map_add φ _ _

set_option backward.isDefEq.respectTransparency false in
private theorem bh9_dual_neg {K L : ChainComplex (ModuleCat ℚ) ℕ} (f : K ⟶ L) :
    linearDualMap (-f) = -linearDualMap f := by
  ext n φ
  change Module.Dual ℚ (L.X n) at φ
  apply LinearMap.ext
  intro c
  change φ (-((f.f n).hom c)) = -φ ((f.f n).hom c)
  exact map_neg φ _

private abbrev bh9_circleMV :=
  mvCochainShortComplex (TopCat.of UnitAddCircle) (circleArc 0) (circleArc (1 / 2))

private def bh9_circleSmallRestriction : SingularCochainComplex ℚ (TopCat.of UnitAddCircle) ⟶
    bh9_circleMV.X₁ :=
  linearDualMap (twoSubsetSmallChainInclusion (TopCat.of UnitAddCircle)
    (circleArc 0) (circleArc (1 / 2)))

private def bh9_secondCochainInclusion :
    SingularCochainComplex ℚ (TopCat.of (circleArc (1 / 2))) ⟶ bh9_circleMV.X₂ :=
  linearDualMap (biprod.snd :
    SingularChainComplex ℚ (TopCat.of (circleArc 0)) ⊞
      SingularChainComplex ℚ (TopCat.of (circleArc (1 / 2))) ⟶ _)

private def bh9_firstCochainInclusion :
    SingularCochainComplex ℚ (TopCat.of (circleArc 0)) ⟶ bh9_circleMV.X₂ :=
  linearDualMap (biprod.fst :
    SingularChainComplex ℚ (TopCat.of (circleArc 0)) ⊞
      SingularChainComplex ℚ (TopCat.of (circleArc (1 / 2))) ⟶ _)

set_option backward.isDefEq.respectTransparency false in
private theorem bh9_secondCochainInclusion_overlap :
    bh9_secondCochainInclusion ≫ bh9_circleMV.g =
      -singularCochainComplexMap ℚ (subsetIntersectionToRight (TopCat.of UnitAddCircle)
        (circleArc 0) (circleArc (1 / 2))) := by
  change linearDualMap biprod.snd ≫ linearDualMap (biprod.lift _ (-_)) = _
  rw [← linearDualMap_comp, biprod.lift_snd, bh9_dual_neg]
  rfl

set_option backward.isDefEq.respectTransparency false in
private theorem bh9_circleSmallRestriction_middle :
    bh9_circleSmallRestriction ≫ bh9_circleMV.f =
      singularCochainComplexMap ℚ
          (topologicalSubsetInclusion (TopCat.of UnitAddCircle) (circleArc 0)) ≫
        bh9_firstCochainInclusion +
      singularCochainComplexMap ℚ
          (topologicalSubsetInclusion (TopCat.of UnitAddCircle) (circleArc (1 / 2))) ≫
        bh9_secondCochainInclusion := by
  change linearDualMap _ ≫ linearDualMap _ = _
  rw [← linearDualMap_comp]
  change linearDualMap (singularMayerVietorisSumChainMap (TopCat.of UnitAddCircle)
    (circleArc 0) (circleArc (1 / 2))) = _
  rw [singularMayerVietorisSumChainMap_eq, biprod.desc_eq, bh9_dual_add,
    linearDualMap_comp, linearDualMap_comp]
  rfl

/-- The winding cochain restricts to zero on the circle cut at zero.
Source: Hatcher, Algebraic Topology, section 1.1; the cut-circle lift has integer part zero. -/
theorem bh9_windingCochain_zeroArc :
    AlgebraicTopology.Simplicial.cochainMap ℚ (TopCat.toSSet.map
      (topologicalSubsetInclusion (TopCat.of UnitAddCircle) (circleArc 0))) 1
        circleWindingCochain = 0 := by
  apply bh9_cochain_ext
  intro σ
  simp only [AlgebraicTopology.Simplicial.cochainMap_apply,
    AlgebraicTopology.Simplicial.chainOfSimplex_map, circleWindingCochain,
    simplexCochain_apply_chainOfSimplex, LinearMap.zero_apply]
  exact_mod_cast bh9_circleWinding_arc_zero σ

private def bh9_middlePrimitive : bh9_circleMV.X₂.X 0 :=
  (bh9_secondCochainInclusion.f 0).hom (bh9_arcWindingPrimitive (1 / 2))

set_option backward.isDefEq.respectTransparency false in
private theorem bh9_middlePrimitive_overlap :
    (bh9_circleMV.g.f 0).hom bh9_middlePrimitive = -bh9_overlapPrimitive := by
  have h := ConcreteCategory.congr_hom
    (congrArg (fun f ↦ f.f 0) bh9_secondCochainInclusion_overlap)
    (bh9_arcWindingPrimitive (1 / 2))
  exact h

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem bh9_middlePrimitive_d :
    (bh9_circleMV.X₂.d 0 1).hom bh9_middlePrimitive =
      (bh9_circleMV.f.f 1).hom ((bh9_circleSmallRestriction.f 1).hom circleWindingCochain) := by
  have hc := ConcreteCategory.congr_hom (bh9_secondCochainInclusion.comm 0 1)
    (bh9_arcWindingPrimitive (1 / 2))
  symm at hc
  change (bh9_secondCochainInclusion.f 1).hom
    (AlgebraicTopology.Simplicial.coboundary ℚ 0 (bh9_arcWindingPrimitive (1 / 2))) =
      (bh9_circleMV.X₂.d 0 1).hom bh9_middlePrimitive at hc
  rw [← bh9_winding_restrict_eq_coboundary] at hc
  rw [← hc]
  have hm := ConcreteCategory.congr_hom
    (congrArg (fun f : SingularCochainComplex ℚ (TopCat.of UnitAddCircle) ⟶ bh9_circleMV.X₂ ↦
      f.f 1) bh9_circleSmallRestriction_middle)
    (show (SingularCochainComplex ℚ (TopCat.of UnitAddCircle)).X 1 from circleWindingCochain)
  change (bh9_circleMV.f.f 1).hom ((bh9_circleSmallRestriction.f 1).hom circleWindingCochain) =
    (bh9_firstCochainInclusion.f 1).hom
      (AlgebraicTopology.Simplicial.cochainMap ℚ (TopCat.toSSet.map
        (topologicalSubsetInclusion (TopCat.of UnitAddCircle) (circleArc 0))) 1 circleWindingCochain) +
    (bh9_secondCochainInclusion.f 1).hom
      (AlgebraicTopology.Simplicial.cochainMap ℚ (TopCat.toSSet.map
        (topologicalSubsetInclusion (TopCat.of UnitAddCircle) (circleArc (1 / 2)))) 1
        circleWindingCochain) at hm
  rw [bh9_windingCochain_zeroArc, map_zero, zero_add] at hm
  exact hm.symm

private def bh9_windingCocycle : AlgebraicTopology.Simplicial.Cocycle ℚ
    (TopCat.toSSet.obj (TopCat.of UnitAddCircle)) 1 :=
  ⟨circleWindingCochain, coboundary_circleWindingCochain⟩

private def bh9_cochainCycle (Y : TopCat.{0}) (n : ℕ)
    (φ : AlgebraicTopology.Simplicial.Cocycle ℚ (TopCat.toSSet.obj Y) n) :
    LinearMap.ker ((SingularCochainComplex ℚ Y).sc n).g.hom :=
  ⟨φ.1, by
    change ((SingularCochainComplex ℚ Y).d n ((ComplexShape.up ℕ).next n)).hom φ.1 = 0
    rw [CochainComplex.next]
    exact φ.2⟩

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The winding cocycle is the negative of the chosen Mayer–Vietoris circle generator.
Source: Hatcher, Algebraic Topology, section 3.1; the overlap map is first restriction minus second restriction. -/
theorem bh9_windingCocycle_class :
    cohomologyClass (TopCat.of UnitAddCircle) 1 bh9_windingCocycle = -circleClass := by
  let Y := TopCat.of UnitAddCircle
  let O := TopCat.of ↥(circleArc 0 ∩ circleArc (1 / 2))
  let S := bh9_circleMV
  let w := bh9_cochainCycle Y 1 bh9_windingCocycle
  let z₃ := bh9_cochainCycle O 0 (-bh9_overlapCocycle)
  let f := (shortComplexFunctor (ModuleCat ℚ) (ComplexShape.up ℕ) 1).map
    bh9_circleSmallRestriction
  let z₁ := ShortComplex.moduleCatCycleMap f w
  have hδ := bh9_connecting_class S
    (mvCochainShortComplex_shortExact Y (circleArc 0) (circleArc (1 / 2))) 0
    z₃ bh9_middlePrimitive z₁ bh9_middlePrimitive_overlap bh9_middlePrimitive_d.symm
  have hz₃ : (S.X₃.sc 0).moduleCatHomologyClass z₃ = -circleOverlapIndicator := by
    calc
      _ = cohomologyClass O 0 (-bh9_overlapCocycle) :=
        (bh9_cohomologyClass_cochain O 0 (-bh9_overlapCocycle) z₃.property).symm
      _ = -circleOverlapIndicator := by rw [map_neg, bh9_overlapCocycle_class]
  rw [hz₃] at hδ
  let e := smallCochainCohomologyEquiv Y (circleArc 0) (circleArc (1 / 2))
    (isOpen_circleArc 0) (isOpen_circleArc (1 / 2)) circleArc_cover 1
  have he : e.symm (cohomologyClass Y 1 bh9_windingCocycle) =
      (S.X₁.sc 1).moduleCatHomologyClass z₁ := by
    change (homologyMap bh9_circleSmallRestriction 1).hom
      (cohomologyClass Y 1 bh9_windingCocycle) = _
    rw [bh9_cohomologyClass_cochain Y 1 bh9_windingCocycle w.property]
    exact ShortComplex.moduleCatHomologyClass_naturality f w
  have h := congrArg e hδ
  change mvδ Y (circleArc 0) (circleArc (1 / 2))
    (isOpen_circleArc 0) (isOpen_circleArc (1 / 2)) circleArc_cover 0
      (-circleOverlapIndicator) = e ((S.X₁.sc 1).moduleCatHomologyClass z₁) at h
  rw [map_neg, ← he, e.apply_symm_apply] at h
  exact h.symm

private def bh9_coordinateWindingCocycle (j : Fin 2) :
    AlgebraicTopology.Simplicial.Cocycle ℚ (TopCat.toSSet.obj (TopCat.of (UnitAddTorus (Fin 2)))) 1 :=
  ⟨bh9_coordinateWinding j, bh9_coordinateWinding_closed j⟩

/-- A coordinate winding cocycle represents the negative of its coordinate circle class.
Source: naturality of singular cohomology and the Mayer–Vietoris circle normalization. -/
theorem bh9_coordinateWinding_class (j : Fin 2) :
    cohomologyClass (TopCat.of (UnitAddTorus (Fin 2))) 1 (bh9_coordinateWindingCocycle j) =
      -torusCoordinateClass j := by
  have h := cohomologyMap_class (R := ℚ) (TopCat.of UnitAddCircle)
    (TopCat.ofHom ⟨fun t : UnitAddTorus (Fin 2) ↦ t j, continuous_apply j⟩) 1
    bh9_windingCocycle (bh9_coordinateWindingCocycle j) rfl
  rw [bh9_windingCocycle_class, map_neg] at h
  exact h.symm

/-- The two coordinate winding signs cancel in the ordered torus cup product.
Source: Hatcher, Algebraic Topology, Example 3.11; bilinearity of the cup product. -/
theorem bh9_windingCupCocycle_class :
    cohomologyClass (TopCat.of (UnitAddTorus (Fin 2))) 2 bh9_windingCupCocycle =
      cup (R := ℚ) (TopCat.of (UnitAddTorus (Fin 2))) (p := 1) (q := 1) (k := 2) rfl
        (torusCoordinateClass 0) (torusCoordinateClass 1) := by
  rw [← bh9_cup_cohomologyClass (TopCat.of (UnitAddTorus (Fin 2))) 1 1
    (bh9_coordinateWindingCocycle 0) (bh9_coordinateWindingCocycle 1) bh9_windingCupCocycle rfl,
    bh9_coordinateWinding_class, bh9_coordinateWinding_class]
  simp only [map_neg, LinearMap.neg_apply, neg_neg]

/-- The ordered top torus cup product evaluates to one on the explicit square class.
Source: Hatcher, Algebraic Topology, Example 3.11; the normalized winding cup computation. -/
theorem bh9_squareClass_topCup_pairing :
    cohomologyEquivDualHomology ℚ (TopCat.of (UnitAddTorus (Fin 2))) 2
      (cup (R := ℚ) (TopCat.of (UnitAddTorus (Fin 2))) (p := 1) (q := 1) (k := 2) rfl
        (torusCoordinateClass 0) (torusCoordinateClass 1)) bh9_squareClass = 1 := by
  rw [← bh9_windingCupCocycle_class]
  exact bh9_squareClass_winding_pairing

private def bh9_cellVertices : Fin 6 → Fin 3 → Fin 2 → ℝ :=
  ![ ![![1, 1/2], ![1/2, 1], ![0, 0]],
     ![![1, 1/2], ![1/2, 1], ![1, 1]],
     ![![1/2, 1], ![0, 0], ![0, 1/2]],
     ![![1/2, 1], ![0, 1/2], ![0, 1]],
     ![![1/2, 0], ![1, 1/2], ![0, 0]],
     ![![1/2, 0], ![1, 0], ![1, 1/2]] ]

private def bh9_cellLift (k : Fin 6) : C(Convexity.StdSimplex ℝ (Fin 3), Fin 2 → ℝ) :=
  ⟨fun t j ↦ t.weights 0 * bh9_cellVertices k 0 j +
    t.weights 1 * bh9_cellVertices k 1 j + t.weights 2 * bh9_cellVertices k 2 j,
    by fun_prop⟩

open scoped Simplicial in
private def bh9_torusSimplex (F : C(Convexity.StdSimplex ℝ (Fin 3), Fin 2 → ℝ)) :
    (TopCat.toSSet.obj (TopCat.of (UnitAddTorus (Fin 2)))) _⦋2⦌ :=
  ((TopCat.of (UnitAddTorus (Fin 2))).toSSetObjEquiv _).symm
    ⟨fun t j ↦ (F t j : UnitAddCircle), continuous_pi fun j ↦
      (AddCircle.continuous_mk' 1).comp ((continuous_apply j).comp F.continuous)⟩

open scoped Simplicial in
private def bh9_cellSimplex (k : Fin 6) := bh9_torusSimplex (bh9_cellLift k)

private theorem bh9_cellLift_face (k : Fin 6) (i : Fin 3)
    (t : Convexity.StdSimplex ℝ (Fin 2)) (j : Fin 2) :
    bh9_cellLift k (Convexity.StdSimplex.map i.succAbove t) j =
      t.weights 0 * bh9_cellVertices k (i.succAbove 0) j +
        t.weights 1 * bh9_cellVertices k (i.succAbove 1) j := by
  simp only [bh9_cellLift, ContinuousMap.coe_mk, Convexity.StdSimplex.weights_map_apply,
    Finset.sum_filter, Fin.sum_univ_succ, Finset.univ_unique, Finset.sum_singleton]
  fin_cases i <;> norm_num [show Fin.succAbove (2 : Fin 3) (1 : Fin 2) = 1 from rfl]

open scoped Simplicial in
private theorem bh9_cellSimplex_face (k : Fin 6) (i : Fin 3)
    (t : Convexity.StdSimplex ℝ (Fin 2)) (j : Fin 2) :
    (TopCat.of (UnitAddTorus (Fin 2))).toSSetObjEquiv _
      ((TopCat.toSSet.obj (TopCat.of (UnitAddTorus (Fin 2)))).δ i (bh9_cellSimplex k)) t j =
      ((t.weights 0 * bh9_cellVertices k (i.succAbove 0) j +
        t.weights 1 * bh9_cellVertices k (i.succAbove 1) j : ℝ) : UnitAddCircle) := by
  rw [TopCat.toSSetObjEquiv_δ_apply]
  change (bh9_cellLift k (Convexity.StdSimplex.map i.succAbove t) j : UnitAddCircle) = _
  rw [bh9_cellLift_face]

private def bh9_cellFaceLeft : Fin 9 → Fin 6 × Fin 3 :=
  ![(0,0), (0,1), (0,2), (1,0), (1,1), (2,0), (2,1), (3,1), (4,2)]

private def bh9_cellFaceRight : Fin 9 → Fin 6 × Fin 3 :=
  ![(2,2), (4,0), (1,2), (5,2), (3,0), (5,0), (3,2), (4,1), (5,1)]

open scoped Simplicial in
private theorem bh9_cellFaces (i : Fin 9) :
    (TopCat.toSSet.obj (TopCat.of (UnitAddTorus (Fin 2)))).δ (bh9_cellFaceLeft i).2
      (bh9_cellSimplex (bh9_cellFaceLeft i).1) =
    (TopCat.toSSet.obj (TopCat.of (UnitAddTorus (Fin 2)))).δ (bh9_cellFaceRight i).2
      (bh9_cellSimplex (bh9_cellFaceRight i).1) := by
  apply ((TopCat.of (UnitAddTorus (Fin 2))).toSSetObjEquiv _).injective
  ext t j
  rw [bh9_cellSimplex_face, bh9_cellSimplex_face]
  have ht := t.total_of_fintype
  rw [Fin.sum_univ_two] at ht
  fin_cases i <;> fin_cases j <;>
    norm_num [bh9_cellFaceLeft, bh9_cellFaceRight, bh9_cellVertices,
      show Fin.succAbove (2 : Fin 3) (1 : Fin 2) = 1 from rfl, ht, AddCircle.coe_period]

private def bh9_cellChain : AlgebraicTopology.Simplicial.ChainGroup ℚ
    (TopCat.toSSet.obj (TopCat.of (UnitAddTorus (Fin 2)))) 2 :=
  AlgebraicTopology.Simplicial.chainOfSimplex ℚ (bh9_cellSimplex 0) -
  AlgebraicTopology.Simplicial.chainOfSimplex ℚ (bh9_cellSimplex 1) -
  AlgebraicTopology.Simplicial.chainOfSimplex ℚ (bh9_cellSimplex 2) -
  AlgebraicTopology.Simplicial.chainOfSimplex ℚ (bh9_cellSimplex 3) +
  AlgebraicTopology.Simplicial.chainOfSimplex ℚ (bh9_cellSimplex 4) +
  AlgebraicTopology.Simplicial.chainOfSimplex ℚ (bh9_cellSimplex 5)

/-- The six triangles around the standard local simplex form an absolute torus cycle.
Source: Hatcher, Algebraic Topology, section 2.2; cancellation of internal edges and opposite square edges. -/
theorem bh9_cellChain_cycle : AlgebraicTopology.Simplicial.boundary ℚ 1 bh9_cellChain = 0 := by
  have h0 := bh9_cellFaces 0
  have h1 := bh9_cellFaces 1
  have h2 := bh9_cellFaces 2
  have h3 := bh9_cellFaces 3
  have h4 := bh9_cellFaces 4
  have h5 := bh9_cellFaces 5
  have h6 := bh9_cellFaces 6
  have h7 := bh9_cellFaces 7
  have h8 := bh9_cellFaces 8
  norm_num [bh9_cellFaceLeft, bh9_cellFaceRight] at h0 h1 h2 h3 h4 h5 h6 h7 h8
  simp only [bh9_cellChain, map_sub, map_add,
    AlgebraicTopology.Simplicial.boundary_chainOfSimplex, Fin.sum_univ_succ,
    Finset.univ_unique, Finset.sum_singleton]
  norm_num
  simp only [h0, h1, h2, h3, h4, h5, h6, h7, h8]
  abel

open scoped Simplicial in
private theorem bh9_torusSimplex_winding
    (F : C(Convexity.StdSimplex ℝ (Fin 3), Fin 2 → ℝ)) (i : Fin 3) (j : Fin 2) :
    circleWinding ((TopCat.toSSet.map
      (TopCat.ofHom ⟨fun t : UnitAddTorus (Fin 2) ↦ t j, continuous_apply j⟩)).app _
        ((TopCat.toSSet.obj (TopCat.of (UnitAddTorus (Fin 2)))).δ i (bh9_torusSimplex F))) =
      ⌊F (Convexity.StdSimplex.single (i.succAbove 1)) j⌋ -
      ⌊F (Convexity.StdSimplex.single (i.succAbove 0)) j⌋ := by
  let G : C(Convexity.StdSimplex ℝ (Fin 2), ℝ) :=
    ⟨fun t ↦ F (Convexity.StdSimplex.map i.succAbove t) j,
      (continuous_apply j).comp (F.continuous.comp
        (Convexity.StdSimplex.continuous_map (R := ℝ) _))⟩
  have hv (k : Fin 2) : G (Convexity.StdSimplex.single k) =
      F (Convexity.StdSimplex.single (i.succAbove k)) j := by
    simp only [G, ContinuousMap.coe_mk, Convexity.StdSimplex.map_single]
  rw [← hv 1, ← hv 0]
  apply circleWinding_eq _ G
  intro t
  change (F (Convexity.StdSimplex.map i.succAbove t) j : UnitAddCircle) =
    (TopCat.of (UnitAddTorus (Fin 2))).toSSetObjEquiv _
      ((TopCat.toSSet.obj (TopCat.of (UnitAddTorus (Fin 2)))).δ i (bh9_torusSimplex F)) t j
  rw [TopCat.toSSetObjEquiv_δ_apply]
  rfl

/-- The winding cup on a lifted torus simplex is the product of its ordered coordinate increments.
Source: Hatcher, Algebraic Topology, section 3.2; the Alexander–Whitney formula and lifted endpoint winding. -/
theorem bh9_windingCup_liftedSimplex
    (F : C(Convexity.StdSimplex ℝ (Fin 3), Fin 2 → ℝ)) :
    cupCochain (TopCat.of (UnitAddTorus (Fin 2))) 1 1
      (bh9_coordinateWinding 0) (bh9_coordinateWinding 1)
        (AlgebraicTopology.Simplicial.chainOfSimplex ℚ (bh9_torusSimplex F)) =
      ((⌊F (Convexity.StdSimplex.single 1) 0⌋ - ⌊F (Convexity.StdSimplex.single 0) 0⌋ : ℤ) : ℚ) *
      ((⌊F (Convexity.StdSimplex.single 2) 1⌋ - ⌊F (Convexity.StdSimplex.single 1) 1⌋ : ℤ) : ℚ) := by
  have hf : AlgebraicTopology.Simplicial.frontInclusion 1 1 = SimplexCategory.δ (2 : Fin 3) := by
    ext k
    fin_cases k <;> rfl
  have hb : AlgebraicTopology.Simplicial.backInclusion 1 1 = SimplexCategory.δ (0 : Fin 3) := by
    ext k
    fin_cases k <;> rfl
  rw [cupCochain_apply_simplex]
  simp only [AlgebraicTopology.Simplicial.frontFace, AlgebraicTopology.Simplicial.backFace,
    hf, hb, ← SimplicialObject.δ_def, bh9_coordinateWinding,
    AlgebraicTopology.Simplicial.cochainMap_apply, AlgebraicTopology.Simplicial.chainOfSimplex_map,
    circleWindingCochain, simplexCochain_apply_chainOfSimplex, bh9_torusSimplex_winding]
  rfl

/-- Only the standard local triangle contributes to the winding cup evaluation of the six-triangle square.
Source: Hatcher, Algebraic Topology, section 3.2; the explicit affine vertices and Alexander–Whitney evaluation. -/
theorem bh9_windingCup_cellSimplex (k : Fin 6) :
    cupCochain (TopCat.of (UnitAddTorus (Fin 2))) 1 1
      (bh9_coordinateWinding 0) (bh9_coordinateWinding 1)
        (AlgebraicTopology.Simplicial.chainOfSimplex ℚ (bh9_cellSimplex k)) =
      if k = 0 then 1 else 0 := by
  rw [bh9_cellSimplex, bh9_windingCup_liftedSimplex]
  fin_cases k <;> norm_num [bh9_cellLift, bh9_cellVertices]

private theorem bh9_cellLift_bounds (k : Fin 6)
    (t : Convexity.StdSimplex ℝ (Fin 3)) (j : Fin 2) :
    0 ≤ bh9_cellLift k t j ∧ bh9_cellLift k t j ≤ 1 := by
  have h0 := t.weights_nonneg 0
  have h1 := t.weights_nonneg 1
  have h2 := t.weights_nonneg 2
  have ht := t.total_of_fintype
  rw [Fin.sum_univ_three] at ht
  fin_cases k <;> fin_cases j <;> norm_num [bh9_cellLift, bh9_cellVertices] <;>
    (try constructor) <;> linarith

private theorem bh9_unitCoordinate_half (r : ℝ) (hr : 0 ≤ r ∧ r ≤ 1)
    (h : (r : UnitAddCircle) = ((1 / 2 : ℝ) : UnitAddCircle)) : r = 1 / 2 := by
  have hne : r ≠ 1 := by
    intro he
    rw [he, AddCircle.coe_period] at h
    exact bh9_half_ne_zero h.symm
  exact (AddCircle.coe_eq_coe_iff_of_mem_Ico (p := (1 : ℝ)) (a := 0)
    (x := r) (y := 1 / 2) ⟨hr.1, by simpa only [zero_add] using lt_of_le_of_ne hr.2 hne⟩
    (by constructor <;> norm_num)).mp h

open scoped Simplicial in
/-- Every triangle other than the standard local simplex avoids the center of the torus cell.
Source: the affine six-triangle subdivision of the square and the interval model of each circle. -/
theorem bh9_cellSimplex_avoids_center (k : Fin 6) (hk : k ≠ 0)
    (t : Convexity.StdSimplex ℝ (Fin 3)) :
    (TopCat.of (UnitAddTorus (Fin 2))).toSSetObjEquiv _ (bh9_cellSimplex k) t ≠
      bh9_squareTorus 0 := by
  intro h
  have hc (j : Fin 2) : bh9_cellLift k t j = 1 / 2 := by
    apply bh9_unitCoordinate_half _ (bh9_cellLift_bounds k t j)
    have hj := congrFun h j
    change (bh9_cellLift k t j : UnitAddCircle) = bh9_squareTorus 0 j at hj
    convert hj using 1
    fin_cases j <;> norm_num [bh9_squareTorus, bh5_clamp]
  have hx := hc 0
  have hy := hc 1
  have h0 := t.weights_nonneg 0
  have h1 := t.weights_nonneg 1
  have h2 := t.weights_nonneg 2
  have ht := t.total_of_fintype
  rw [Fin.sum_univ_three] at ht
  fin_cases k
  · exact hk rfl
  all_goals norm_num [bh9_cellLift, bh9_cellVertices] at hx hy
  all_goals linarith

set_option backward.isDefEq.respectTransparency false in
open scoped Simplicial in
/-- A singular simplex avoiding the distinguished point is zero in the local relative chain complex.
Source: Hatcher, Algebraic Topology, section 2.1; relative chains quotient by chains in the subspace. -/
theorem bh9_localProjection_simplex_zero {Y : Type} [TopologicalSpace Y]
    (p : Y) (n : ℕ) (σ : (TopCat.toSSet.obj (TopCat.of Y)) _⦋n⦌)
    (hσ : ∀ t, (TopCat.of Y).toSSetObjEquiv _ σ t ≠ p) :
    ((relativeChainProjection ℚ (pointComplementPair p)).f n).hom
      (AlgebraicTopology.Simplicial.chainOfSimplex ℚ σ) = 0 := by
  let τ := ((pointComplementPair p).snd.toSSetObjEquiv _).symm
    ⟨fun t ↦ ⟨(TopCat.of Y).toSSetObjEquiv _ σ t, hσ t⟩,
      ((TopCat.of Y).toSSetObjEquiv _ σ).continuous.subtype_mk _⟩
  have hτ : (TopCat.toSSet.map (pointComplementPair p).map).app _ τ = σ := by
    apply ((TopCat.of Y).toSSetObjEquiv _).injective
    ext t
    rfl
  have h := ConcreteCategory.congr_hom
    (congrArg (fun f ↦ f.f n) (subspaceChainMap_relativeChainProjection ℚ (pointComplementPair p)))
    (AlgebraicTopology.Simplicial.chainOfSimplex ℚ τ)
  change ((relativeChainProjection ℚ (pointComplementPair p)).f n).hom
    (((SSet.chainComplexMap (TopCat.toSSet.map (pointComplementPair p).map) (ModuleCat.of ℚ ℚ)).f n).hom
      (AlgebraicTopology.Simplicial.chainOfSimplex ℚ τ)) = 0 at h
  rw [AlgebraicTopology.Simplicial.chainOfSimplex_map, hτ] at h
  exact h

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The local relative image of the six-triangle cycle is exactly its central simplex.
Source: Hatcher, Algebraic Topology, section 2.1; all five other triangles lie in the punctured torus. -/
theorem bh9_cellChain_local_projection :
    ((relativeChainProjection ℚ (pointComplementPair (bh9_squareTorus 0))).f 2).hom bh9_cellChain =
      ((relativeChainProjection ℚ (pointComplementPair (bh9_squareTorus 0))).f 2).hom
        (AlgebraicTopology.Simplicial.chainOfSimplex ℚ (bh9_cellSimplex 0)) := by
  have hz (k : Fin 6) (hk : k ≠ 0) := bh9_localProjection_simplex_zero
    (bh9_squareTorus 0) 2 (bh9_cellSimplex k) (bh9_cellSimplex_avoids_center k hk)
  simp only [bh9_cellChain, map_add, map_sub, hz 1 (by decide), hz 2 (by decide),
    hz 3 (by decide), hz 4 (by decide), hz 5 (by decide), sub_zero, add_zero]

private theorem bh9_complexCoord_one (z : Fin 1 → ℂ) :
    Complex.piCoordCLE 1 z = ![(z 0).re, (z 0).im] := by
  funext i
  change (Complex.piBasisOneI 1).repr z i = _
  simp only [Complex.piBasisOneI, Module.Basis.repr_reindex_apply,
    Module.Basis.smulTower'_repr, Pi.basisFun_repr, Complex.coe_basisOneI_repr]
  fin_cases i <;> rfl

private def bh9_realTorusLocalMap :
    puncturedPair ℝ 2 ⟶ pointComplementPair (bh9_squareTorus 0) :=
  (standardComplexRealPairIso 1).inv ≫ bh9_squareTorusLocalMap

open scoped Simplicial in
/-- The central affine torus triangle is exactly the image of the defining standard local simplex.
Source: the definition of `standardComplexLocalClass`, consecutive real and imaginary coordinates,
and the affine formula for the clamped square on its interior. -/
theorem bh9_centralSimplex_map :
    (TopCat.toSSet.map (TopPair.Hom.fst bh9_realTorusLocalMap)).app _
      (standardSingularSimplex 2) = bh9_cellSimplex 0 := by
  apply ((TopCat.of (UnitAddTorus (Fin 2))).toSSetObjEquiv _).injective
  ext t j
  let q := (Complex.piCoordCLE 1).symm (standardAffineSimplex 2 t)
  have hq := (bh9_complexCoord_one q).symm.trans
    ((Complex.piCoordCLE 1).apply_symm_apply (standardAffineSimplex 2 t))
  have hr := congrFun hq 0
  have hi := congrFun hq 1
  change (q 0).re = t.weights 0 - t.weights 2 at hr
  change (q 0).im = t.weights 1 - t.weights 2 at hi
  have ht := t.total_of_fintype
  rw [Fin.sum_univ_three] at ht
  have hc (j : Fin 2) : bh5_clamp (bh9_cellLift 0 t j) = bh9_cellLift 0 t j := by
    rw [bh5_clamp, min_eq_right (bh9_cellLift_bounds 0 t j).2,
      max_eq_right (bh9_cellLift_bounds 0 t j).1]
  change bh9_squareTorus q j = (bh9_cellLift 0 t j : UnitAddCircle)
  fin_cases j
  · change (bh5_clamp (((q 0).re + 1) / 2) : UnitAddCircle) = _
    rw [hr, show (t.weights 0 - t.weights 2 + 1) / 2 = bh9_cellLift 0 t 0 by
      norm_num [bh9_cellLift, bh9_cellVertices]
      linarith, hc]
    rfl
  · change (bh5_clamp (((q 0).im + 1) / 2) : UnitAddCircle) = _
    rw [hi, show (t.weights 1 - t.weights 2 + 1) / 2 = bh9_cellLift 0 t 1 by
      norm_num [bh9_cellLift, bh9_cellVertices]
      linarith, hc]
    rfl

private def bh9_cellCycle :
    LinearMap.ker ((SingularChainComplex ℚ (TopCat.of (UnitAddTorus (Fin 2)))).sc 2).g.hom :=
  ⟨bh9_cellChain, by
    change ((SingularChainComplex ℚ (TopCat.of (UnitAddTorus (Fin 2)))).d
      2 ((ComplexShape.down ℕ).next 2)).hom _ = 0
    rw [ChainComplex.next_nat_succ]
    exact bh9_cellChain_cycle⟩

/-- The absolute torus class represented by the six-triangle square containing the standard local simplex.
Source: Hatcher, Algebraic Topology, section 2.2, the triangulated fundamental square. -/
def bh9_cellClass : Homology ℚ (TopCat.of (UnitAddTorus (Fin 2))) 2 :=
  ((SingularChainComplex ℚ (TopCat.of (UnitAddTorus (Fin 2)))).sc 2).moduleCatHomologyClass bh9_cellCycle

example : bh9_cellClass =
    ((SingularChainComplex ℚ (TopCat.of (UnitAddTorus (Fin 2)))).sc 2).moduleCatHomologyClass
      bh9_cellCycle := rfl

/-- The six-triangle square has ordered top cup pairing one.
Source: Hatcher, Algebraic Topology, Example 3.11; the normalized winding cup and explicit triangle evaluations. -/
theorem bh9_cellClass_topCup_pairing :
    cohomologyEquivDualHomology ℚ (TopCat.of (UnitAddTorus (Fin 2))) 2
      (cup (R := ℚ) (TopCat.of (UnitAddTorus (Fin 2))) (p := 1) (q := 1) (k := 2) rfl
        (torusCoordinateClass 0) (torusCoordinateClass 1)) bh9_cellClass = 1 := by
  rw [← bh9_windingCupCocycle_class, bh9_cellClass, cohomologyEquivDualHomology_cohomologyClass]
  change cupCochain (TopCat.of (UnitAddTorus (Fin 2))) 1 1
    (bh9_coordinateWinding 0) (bh9_coordinateWinding 1) bh9_cellChain = 1
  simp only [bh9_cellChain, map_add, map_sub, bh9_windingCup_cellSimplex]
  norm_num

/-- A top homology class with ordered cup pairing one represents the torus coefficient functional.
Source: Hatcher, Algebraic Topology, Example 3.11; the top rational cohomology is spanned by its ordered cup monomial. -/
theorem bh9_torus_pairing_of_topCup
    (z : Homology ℚ (TopCat.of (UnitAddTorus (Fin 2))) 2)
    (hz : cohomologyEquivDualHomology ℚ (TopCat.of (UnitAddTorus (Fin 2))) 2
      (cup (R := ℚ) (TopCat.of (UnitAddTorus (Fin 2))) (p := 1) (q := 1) (k := 2) rfl
        (torusCoordinateClass 0) (torusCoordinateClass 1)) z = 1)
    (a : Cohomology ℚ (TopCat.of (UnitAddTorus (Fin 2))) 2) :
    cohomologyEquivDualHomology ℚ (TopCat.of (UnitAddTorus (Fin 2))) 2 a z =
      bh8_torusCoefficient a := by
  let c := cup (R := ℚ) (TopCat.of (UnitAddTorus (Fin 2))) (p := 1) (q := 1) (k := 2) rfl
    (torusCoordinateClass 0) (torusCoordinateClass 1)
  have hc : c ≠ 0 := by
    intro h0
    have h := bh9_coefficient_cup
    change bh8_torusCoefficient c = 1 at h
    rw [h0, map_zero] at h
    exact zero_ne_one h
  have hspan : Submodule.span ℚ {c} = ⊤ :=
    (finrank_eq_one_iff_of_nonzero c hc).mp
      ((finrank_cohomology_unitAddTorus 2 2).trans (by decide))
  obtain ⟨r, hr⟩ := Submodule.mem_span_singleton.mp
    (show a ∈ Submodule.span ℚ {c} by rw [hspan]; exact Submodule.mem_top)
  rw [← hr]
  simp only [map_smul, LinearMap.smul_apply, c, hz, bh9_coefficient_cup, smul_eq_mul, mul_one]

set_option backward.isDefEq.respectTransparency false in
private theorem bh9_chain_liftCycles_class (K : ChainComplex (ModuleCat ℚ) ℕ) (n : ℕ)
    (x : ModuleCat.of ℚ ℚ ⟶ K.X n)
    (hx : x ≫ K.d n ((ComplexShape.down ℕ).next n) = 0)
    (z : LinearMap.ker (K.sc n).g.hom) (hz : x.hom 1 = z.1) :
    (K.liftCycles x ((ComplexShape.down ℕ).next n) rfl hx ≫ K.homologyπ n).hom 1 =
      (K.sc n).moduleCatHomologyClass z := by
  have he : (K.liftCycles x ((ComplexShape.down ℕ).next n) rfl hx).hom 1 =
      (K.sc n).moduleCatCyclesIso.inv.hom z := by
    apply (ModuleCat.mono_iff_injective (K.iCycles n)).mp inferInstance
    have hleft := ConcreteCategory.congr_hom
      (K.liftCycles_i x ((ComplexShape.down ℕ).next n) rfl hx) 1
    have hright := ConcreteCategory.congr_hom (K.sc n).moduleCatCyclesIso_inv_iCycles z
    exact hleft.trans (hz.trans hright.symm)
  change (K.homologyπ n).hom ((K.liftCycles x ((ComplexShape.down ℕ).next n) rfl hx).hom 1) = _
  rw [he]
  exact ConcreteCategory.congr_hom (K.sc n).moduleCatCyclesIso_inv_π z

private def bh9_standardRealCycle (d : ℕ) :
    LinearMap.ker ((standardLocalRelativeChainComplex ℚ d).sc d).g.hom :=
  ⟨(standardLocalChain ℚ d).hom 1, by
    exact ConcreteCategory.congr_hom (standardLocalChain_boundary ℚ d) 1⟩

/-- The standard real local class is represented by its prescribed affine simplex in relative chains.
Source: the definition of `standardLocalClass` and the concrete homology quotient. -/
theorem bh9_standardLocalClass_cycle (d : ℕ) :
    standardLocalClass ℚ d =
      ((standardLocalRelativeChainComplex ℚ d).sc d).moduleCatHomologyClass
        (bh9_standardRealCycle d) := by
  exact bh9_chain_liftCycles_class (standardLocalRelativeChainComplex ℚ d) d
    (standardLocalChain ℚ d) (standardLocalChain_boundary ℚ d) (bh9_standardRealCycle d) rfl

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- At the center, the six-triangle torus class is the image of the standard real local class.
Source: Hatcher, Algebraic Topology, section 2.1; localization kills the outer triangles and preserves the defining central simplex. -/
theorem bh9_cellClass_local_real :
    (relativeHomologyProjection ℚ (pointComplementPair (bh9_squareTorus 0)) 2).hom bh9_cellClass =
      relativeHomologyMap ℚ 2 bh9_realTorusLocalMap (standardLocalClass ℚ 2) := by
  rw [bh9_cellClass, bh9_standardLocalClass_cycle]
  have hp := ShortComplex.moduleCatHomologyClass_naturality
    ((shortComplexFunctor (ModuleCat ℚ) (ComplexShape.down ℕ) 2).map
      (relativeChainProjection ℚ (pointComplementPair (bh9_squareTorus 0)))) bh9_cellCycle
  have hg := ShortComplex.moduleCatHomologyClass_naturality
    ((shortComplexFunctor (ModuleCat ℚ) (ComplexShape.down ℕ) 2).map
      ((relativeChainFunctor ℚ).map bh9_realTorusLocalMap)) (bh9_standardRealCycle 2)
  refine hp.trans (Eq.trans ?_ hg.symm)
  congr 1
  apply Subtype.ext
  change ((relativeChainProjection ℚ (pointComplementPair (bh9_squareTorus 0))).f 2).hom bh9_cellChain =
    (((relativeChainFunctor ℚ).map bh9_realTorusLocalMap).f 2).hom ((standardLocalChain ℚ 2).hom 1)
  rw [bh9_cellChain_local_projection]
  have h := ConcreteCategory.congr_hom
    (congrArg (fun f ↦ f.f 2)
      (TopPair.Homotopy.relativeChainProjection_naturality (R := ℚ) bh9_realTorusLocalMap))
    (AlgebraicTopology.Simplicial.chainOfSimplex ℚ (standardSingularSimplex 2))
  change (((relativeChainFunctor ℚ).map bh9_realTorusLocalMap).f 2).hom
      ((standardLocalChain ℚ 2).hom 1) =
    ((relativeChainProjection ℚ (pointComplementPair (bh9_squareTorus 0))).f 2).hom
      (((SSet.chainComplexMap (TopCat.toSSet.map (TopPair.Hom.fst bh9_realTorusLocalMap))
        (ModuleCat.of ℚ ℚ)).f 2).hom
          (AlgebraicTopology.Simplicial.chainOfSimplex ℚ (standardSingularSimplex 2))) at h
  rw [AlgebraicTopology.Simplicial.chainOfSimplex_map, bh9_centralSimplex_map] at h
  exact h.symm

/-- The local image of the six-triangle square has the prescribed complex orientation.
Source: the consecutive real/imaginary coordinate transport defining `standardComplexLocalClass`. -/
theorem bh9_cellClass_local_complex :
    (relativeHomologyProjection ℚ (pointComplementPair (bh9_squareTorus 0)) 2).hom bh9_cellClass =
      relativeHomologyMap ℚ 2 bh9_squareTorusLocalMap (standardComplexLocalClass ℚ 1) := by
  rw [bh9_cellClass_local_real, bh9_realTorusLocalMap, relativeHomologyMap_comp, LinearMap.comp_apply]
  rfl

private def bh9_diskToCenter : bh5_diskPair ⟶ puncturedPair ℂ 1 :=
  supportInclusionPairMap (TopCat.of (Fin 1 → ℂ))
    (Set.singleton_subset_iff.mpr (Metric.mem_closedBall_self (by norm_num : (0 : ℝ) ≤ 2)))

private theorem bh9_square_local_commutes :
    (relativeHomologyMap ℚ 2 bh9_torusCellToLocal).comp
      (relativeHomologyMap ℚ 2 bh9_squareTorusMap) =
    (relativeHomologyMap ℚ 2 bh9_squareTorusLocalMap).comp
      (relativeHomologyMap ℚ 2 bh9_diskToCenter) := by
  rw [← relativeHomologyMap_comp, ← relativeHomologyMap_comp]
  congr 1

/-- Localization at the center detects relative torus two-classes.
Source: Hatcher, Algebraic Topology, section 2.1; the disk restriction and local chart maps are isomorphisms. -/
theorem bh9_torusCellToLocal_injective :
    Function.Injective (relativeHomologyMap ℚ 2 bh9_torusCellToLocal) := by
  intro x y h
  obtain ⟨u, rfl⟩ := bh9_squareTorus_relativeHomology_bijective.2 x
  obtain ⟨v, rfl⟩ := bh9_squareTorus_relativeHomology_bijective.2 y
  apply congrArg (relativeHomologyMap ℚ 2 bh9_squareTorusMap)
  apply (HodgeLean.RealDefs.j5c_convex_restrict_bijective
    (convex_closedBall (0 : Fin 1 → ℂ) (2 : ℝ)) (isCompact_closedBall 0 2)
    (Metric.mem_closedBall_self (by norm_num : (0 : ℝ) ≤ 2)) 2).1
  apply bh9_squareTorusLocalMap_bijective.1
  change ((relativeHomologyMap ℚ 2 bh9_torusCellToLocal).comp
    (relativeHomologyMap ℚ 2 bh9_squareTorusMap)) u =
      ((relativeHomologyMap ℚ 2 bh9_torusCellToLocal).comp
        (relativeHomologyMap ℚ 2 bh9_squareTorusMap)) v at h
  rw [bh9_square_local_commutes] at h
  exact h

set_option backward.isDefEq.respectTransparency false in
/-- Absolute-to-relative projection commutes with localization of the torus pair at its center.
Source: naturality of the relative singular-chain quotient. -/
theorem bh9_torusProjection_local
    (z : Homology ℚ (TopCat.of (UnitAddTorus (Fin 2))) 2) :
    relativeHomologyMap ℚ 2 bh9_torusCellToLocal
      ((relativeHomologyProjection ℚ bh9_torusPair 2).hom z) =
    (relativeHomologyProjection ℚ (pointComplementPair (bh9_squareTorus 0)) 2).hom z := by
  have h := congrArg (fun f ↦ HomologicalComplex.homologyMap f 2)
    (TopPair.Homotopy.relativeChainProjection_naturality (R := ℚ) bh9_torusCellToLocal)
  rw [HomologicalComplex.homologyMap_comp, HomologicalComplex.homologyMap_comp] at h
  have he := ConcreteCategory.congr_hom h z
  change relativeHomologyMap ℚ 2 bh9_torusCellToLocal
    ((relativeHomologyProjection ℚ bh9_torusPair 2).hom z) =
      (relativeHomologyProjection ℚ (pointComplementPair (bh9_squareTorus 0)) 2).hom
        (AlgebraicTopology.Singular.homologyMap ℚ 2 (𝟙 _) z) at he
  simpa only [AlgebraicTopology.Singular.homologyMap_id, LinearMap.id_apply] using he

/-- The absolute square class and the clamped disk class agree in relative torus homology.
Source: Hatcher, Algebraic Topology, section 2.2; localization identifies both with the same prescribed complex local simplex. -/
theorem bh9_cellClass_relative :
    (relativeHomologyProjection ℚ bh9_torusPair 2).hom bh9_cellClass =
      relativeHomologyMap ℚ 2 bh9_squareTorusMap bh5_diskClass := by
  apply bh9_torusCellToLocal_injective
  rw [bh9_torusProjection_local, bh9_cellClass_local_complex]
  change relativeHomologyMap ℚ 2 bh9_squareTorusLocalMap (standardComplexLocalClass ℚ 1) =
    ((relativeHomologyMap ℚ 2 bh9_torusCellToLocal).comp
      (relativeHomologyMap ℚ 2 bh9_squareTorusMap)) bh5_diskClass
  rw [bh9_square_local_commutes, LinearMap.comp_apply]
  exact congrArg (relativeHomologyMap ℚ 2 bh9_squareTorusLocalMap) bh9_diskClass_restrict.symm

/-- The ordered torus coefficient is evaluation on the clamped relative square.
Source: Hatcher, Algebraic Topology, section 2.2 and Example 3.11, the oriented
square cell and the increasing product of its two degree-one generators. -/
theorem bh9_torus_cell_aux (a : RelativeCohomology ℚ bh9_torusPair 2) :
    bh8_torusCoefficient (relativeCohomologyToAbsolute ℚ bh9_torusPair 2 a) =
      relativeCohomologyEquivDualHomology ℚ bh5_diskPair 2
        (relativeCohomologyMap ℚ 2 bh9_squareTorusMap a) bh5_diskClass := by
  exact (bh9_torus_cell_iff_homology bh9_cellClass
    (bh9_torus_pairing_of_topCup bh9_cellClass bh9_cellClass_topCup_pairing)).2
      bh9_cellClass_relative a

end HodgeLean.Adapters
