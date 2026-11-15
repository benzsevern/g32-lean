import HodgeLean.RealDefs.FundamentalClass.Point
import HodgeLean.RealDefs.FundamentalClass.SingularChase
import HodgeConjecture.Definitions.AlgebraicTopology.Singular.Sheaf.Cochain

/-! # `[X] = 1`: the constant class through duality

Evaluation of a dual cocycle on a cycle (`linearDualHomologyEquiv_homologyπ_homologyπ`), the
augmentation on homology as the coefficient sum on cycles (`homologyπ_homology₀ε`), and so the
relative class of a cocycle pulling back to the augmentation is `augmentationClass`
(`homologyπ_eq_augmentationClass`). -/

open CategoryTheory Limits

namespace HodgeLean.RealDefs

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The universal-coefficient pairing evaluates a dual cocycle on a cycle. -/
lemma linearDualHomologyEquiv_homologyπ_homologyπ (K : ChainComplex (ModuleCat.{0} ℚ) ℕ) (n : ℕ)
    (c : K.linearDualCochainComplex.cycles n) (w : K.cycles n) :
    HomologicalComplex.linearDualHomologyEquiv K n (K.linearDualCochainComplex.homologyπ n c)
        (K.homologyπ n w) =
      (show Module.Dual ℚ (K.X n) from K.linearDualCochainComplex.iCycles n c) (K.iCycles n w) := by
  let S := K.sc n
  let x : LinearMap.ker S.g.hom := ⟨K.iCycles n w, by
    change (K.iCycles n ≫ K.d n _) w = 0
    rw [HomologicalComplex.iCycles_d]; rfl⟩
  have hw : w = S.moduleCatCyclesIso.inv x := by
    apply (ConcreteCategory.injective_of_mono_of_preservesPullback (K.iCycles n))
    change _ = (S.moduleCatCyclesIso.inv ≫ S.iCycles) x
    rw [ShortComplex.moduleCatCyclesIso_inv_iCycles]
    rfl
  let T := S.linearDual
  let e := HomologicalComplex.linearDualCochainComplexScIso K n
  let φ : LinearMap.ker T.g.hom := ⟨T.iCycles (ShortComplex.cyclesMap e.hom c), by
    change (T.iCycles ≫ T.g) (ShortComplex.cyclesMap e.hom c) = 0
    rw [ShortComplex.iCycles_g]; rfl⟩
  have hc : ShortComplex.cyclesMap e.hom c = T.moduleCatCyclesIso.inv φ := by
    apply (ConcreteCategory.injective_of_mono_of_preservesPullback T.iCycles)
    change _ = (T.moduleCatCyclesIso.inv ≫ T.iCycles) φ
    rw [ShortComplex.moduleCatCyclesIso_inv_iCycles]
    rfl
  change S.linearDualHomologyEquiv (ShortComplex.homologyMap e.hom
    ((K.linearDualCochainComplex.sc n).homologyπ c)) (S.homologyπ w) = _
  have h1 := ConcreteCategory.congr_hom (ShortComplex.homologyπ_naturality e.hom) c
  rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply] at h1
  rw [h1]
  refine (Eq.trans ?_ (ShortComplex.linearDualHomologyEquiv_class_apply_class S φ x)).trans ?_
  · rw [hc]
    conv_lhs => rw [hw]
    rfl
  · have h2 := ConcreteCategory.congr_hom (ShortComplex.cyclesMap_i e.hom) c
    rw [ConcreteCategory.comp_apply] at h2
    simp only [φ, x]
    erw [h2]
    rfl

open AlgebraicTopology.Singular in
set_option backward.isDefEq.respectTransparency false in
/-- The degree-zero augmentation on homology is the coefficient sum on cycles. -/
lemma homologyπ_homology₀ε (S : SSet.{0}) :
    (S.chainComplex (ModuleCat.of ℚ ℚ)).homologyπ 0 ≫ S.homology₀ε (ModuleCat.of ℚ ℚ) =
      (S.chainComplex (ModuleCat.of ℚ ℚ)).iCycles 0 ≫ simplicialZeroAugmentation ℚ S := by
  let K := S.chainComplex (ModuleCat.of ℚ ℚ)
  apply (cancel_epi (SSet.chainComplexXZeroIsoCyclesZero K).hom).1
  apply S.chainComplex_hom_ext
  intro σ
  simp only [SSet.chainComplexXZeroIsoCyclesZero, ← Category.assoc,
    HomologicalComplex.comp_liftCycles]
  rw [HomologicalComplex.liftCycles_i, Category.comp_id,
    ιChainComplex_comp_simplicialZeroAugmentation]
  convert S.liftCycles_ιChainComplex_homologyπ_homology₀ε (ModuleCat.of ℚ ℚ) σ using 2

open AlgebraicTopology.Singular in
set_option backward.isDefEq.respectTransparency false in
/-- A relative `0`-cocycle pulling back to the augmentation represents the constant class. -/
lemma homologyπ_eq_augmentationClass (P : TopPair.{0}) [IsIso (relativeChainProjection ℚ P)]
    (cr : (RelativeCochainComplex ℚ P).cycles 0)
    (hcr : (HomologicalComplex.linearDualMap (relativeChainProjection ℚ P)).f 0
      ((RelativeCochainComplex ℚ P).iCycles 0 cr) =
        (simplicialZeroAugmentation ℚ (TopCat.toSSet.obj P.fst)).hom) :
    (RelativeCochainComplex ℚ P).homologyπ 0 cr = augmentationClass P := by
  apply (relativeCohomologyEquivDualHomology ℚ P 0).injective
  rw [augmentationClass, LinearEquiv.apply_symm_apply]
  ext z
  let K := SingularChainComplex ℚ P.fst
  let e := HomologicalComplex.homologyMapIso (asIso (relativeChainProjection ℚ P)) 0
  obtain ⟨w, hw⟩ : ∃ w : K.cycles 0, K.homologyπ 0 w = e.inv z :=
    (ModuleCat.epi_iff_surjective (K.homologyπ 0)).1 inferInstance _
  have hz : z = HomologicalComplex.homologyMap (relativeChainProjection ℚ P) 0 (K.homologyπ 0 w) := by
    rw [hw]; exact (e.inv_hom_id_apply z).symm
  rw [hz]
  change ((relativeChainFunctor ℚ).obj P).linearDualHomologyEquiv 0
      ((RelativeCochainComplex ℚ P).homologyπ 0 cr)
      (HomologicalComplex.homologyMap (relativeChainProjection ℚ P) 0 (K.homologyπ 0 w)) = _
  rw [← HomologicalComplex.linearDualHomologyEquiv_naturality]
  have h1 := ConcreteCategory.congr_hom (HomologicalComplex.homologyπ_naturality
    (HomologicalComplex.linearDualMap (relativeChainProjection ℚ P)) 0) cr
  rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply] at h1
  rw [h1, linearDualHomologyEquiv_homologyπ_homologyπ]
  have h2 := ConcreteCategory.congr_hom (HomologicalComplex.cyclesMap_i
    (HomologicalComplex.linearDualMap (relativeChainProjection ℚ P)) 0) cr
  rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply] at h2
  change (show Module.Dual ℚ (K.X 0) from _) _ = _
  erw [h2, hcr]
  have h3 := ConcreteCategory.congr_hom (homologyπ_homology₀ε (TopCat.toSSet.obj P.fst)) w
  rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply] at h3
  change _ = (e.inv ≫ P.fst.singularHomology₀ε (ModuleCat.of ℚ ℚ)) (e.hom (K.homologyπ 0 w))
  rw [ConcreteCategory.comp_apply, e.hom_inv_id_apply]
  exact h3.symm

open TopologicalSpace Opposite Simplicial Convexity AlgebraicTopology.Singular


section ConstantRaw

variable (X : TopCat.{0}) (V : Opens X)

/-- The constant raw `0`-cochain `1` on `V`. -/
noncomputable abbrev constantRawCochain : (openRawSingularCochainComplex ℚ X V).X 0 :=
  constantSingularZeroCochain ℚ X (op V) 1

/-- The constant raw cochain is the augmentation. -/
lemma constantRawCochain_eq :
    (constantRawCochain X V : Module.Dual ℚ (OpenChains ℚ X (op V) 0)) =
      (openZeroAugmentation ℚ X (op V)).hom := by
  apply LinearMap.ext
  intro c
  change (1 : ℚ) • (openZeroAugmentation ℚ X (op V)).hom c = _
  rw [one_smul]

/-- The constant raw cochain is a cocycle. -/
lemma constantRawCochain_d :
    (openRawSingularCochainComplex ℚ X V).d 0 1 (constantRawCochain X V) = 0 := by
  have h := congrArg (fun α => α.app (op V)) (constantsToSingularCochainZero_comp_coboundary ℚ X)
  have h' := ConcreteCategory.congr_hom h (1 : ℚ)
  exact h'

/-- Singular cochains on an empty open vanish. -/
lemma openCochains_eq_zero_of_eq_bot {W : Opens X} (hW : W = ⊥) {n : ℕ}
    (φ : OpenCochains ℚ X (op W) n) : φ = 0 := by
  subst hW
  have h : ModuleCat.ofHom φ = 0 := by
    apply SSet.chainComplex_hom_ext
    intro σ
    exfalso
    exact (((Opens.toTopCat X).obj ⊥).toSSetObjEquiv _ σ StdSimplex.barycenter).2
  exact congrArg ModuleCat.Hom.hom h

/-- The simplicial boundary of a one-chain has augmentation zero (upstream's private
`simplicialBoundary_comp_zeroAugmentation`, reproved). -/
lemma boundary_comp_simplicialZeroAugmentation (S : SSet.{0}) :
    (S.chainComplex (ModuleCat.of ℚ ℚ)).d 1 0 ≫ simplicialZeroAugmentation ℚ S = 0 := by
  apply SSet.chainComplex_hom_ext
  intro σ
  rw [← Category.assoc, SSet.ιChainComplex_d, Preadditive.sum_comp]
  simp

/-- An element killed by the differential underlies a cycle (`ℕ`-indexed modules). -/
lemma mod_exists_cycles_zero {K : CochainComplex (ModuleCat.{0} ℚ) ℕ} (x : K.X 0)
    (hx : K.d 0 1 x = 0) : ∃ c : K.cycles 0, K.iCycles 0 c = x := by
  refine ⟨K.liftCycles (ModuleCat.ofHom (LinearMap.toSpanSingleton ℚ _ x)) 1 (by simp) (by
    ext
    simp [hx]) (1 : ℚ), ?_⟩
  rw [← ConcreteCategory.comp_apply, HomologicalComplex.liftCycles_i]
  simp

variable {X} {W : Opens X} (i : W ⟶ V)

lemma isEmpty_openInclusionPair_snd (hW : W = ⊥) : IsEmpty (openInclusionPair X i).snd := by
  subst hW
  exact ⟨fun y => y.2⟩

/-- On `(V, ∅)` there is a relative `0`-cocycle pulling back to the augmentation. -/
lemma exists_relativeAugmentationCocycle (hW : W = ⊥) :
    haveI := isIso_relativeChainProjection _ (isEmpty_openInclusionPair_snd V i hW)
    ∃ cr : (RelativeCochainComplex ℚ (openInclusionPair X i)).cycles 0,
      (HomologicalComplex.linearDualMap (relativeChainProjection ℚ (openInclusionPair X i))).f 0
        ((RelativeCochainComplex ℚ (openInclusionPair X i)).iCycles 0 cr) =
        (simplicialZeroAugmentation ℚ (TopCat.toSSet.obj (openInclusionPair X i).fst)).hom := by
  have := isIso_relativeChainProjection _ (isEmpty_openInclusionPair_snd V i hW)
  let P := openInclusionPair X i
  let p := relativeChainProjection ℚ P
  let a : (SingularChainComplex ℚ P.fst).linearDualCochainComplex.X 0 :=
    (simplicialZeroAugmentation ℚ (TopCat.toSSet.obj P.fst)).hom
  have ha : (SingularChainComplex ℚ P.fst).linearDualCochainComplex.d 0 1 a = 0 := by
    rw [HomologicalComplex.linearDualCochainComplex_d_succ]
    apply LinearMap.ext
    intro z
    exact ConcreteCategory.congr_hom
      (boundary_comp_simplicialZeroAugmentation (TopCat.toSSet.obj P.fst)) z
  obtain ⟨cr, hcr⟩ := mod_exists_cycles_zero
    ((HomologicalComplex.linearDualMap (inv p)).f 0 a) (by
      rw [← ConcreteCategory.comp_apply, (HomologicalComplex.linearDualMap (inv p)).comm,
        ConcreteCategory.comp_apply, ha, map_zero])
  refine ⟨cr, ?_⟩
  rw [hcr, ← ConcreteCategory.comp_apply, ← HomologicalComplex.comp_f,
    ← HomologicalComplex.linearDualMap_comp, IsIso.hom_inv_id, HomologicalComplex.linearDualMap_id]
  rfl

end ConstantRaw

end HodgeLean.RealDefs
