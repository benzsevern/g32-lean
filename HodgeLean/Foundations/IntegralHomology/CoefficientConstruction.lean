import HodgeLean.Foundations.IntegralHomology.Defs

/-! Rational coefficient extension on singular chains and homology.
HC no distance; AV milestone no distance. -/
noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits AlgebraicTopology AlgebraicTopology.Singular
open scoped Simplicial TensorProduct
namespace HodgeLean.Foundations.IntegralHomology

def _root_.AddMonoidHom.integralMap {M N : Type} [AddCommGroup M] [AddCommGroup N]
    [mM : Module ℤ M] [mN : Module ℤ N] (f : M →+ N) : M →ₗ[ℤ] N where
  toFun := f
  map_add' := map_add f
  map_smul' n x := by
    convert! AddMonoidHom.map_zsmul f n x <;> ext <;> apply int_smul_eq_zsmul

abbrev rational_ZChains (X : TopCat) :=
  (TopCat.toSSet.obj X).chainComplex (ModuleCat.of ℤ ℤ)


abbrev rational_QChainsModel (X : TopCat) :=
  (TopCat.toSSet.obj X).chainComplex (ModuleCat.of ℚ ℚ)


local instance (X : TopCat) (n : ℕ) : IsScalarTower ℤ ℚ ((rational_QChainsModel X).X n) :=
  inferInstance


local instance (X : TopCat) (n : ℕ) : IsScalarTower ℤ ℚ (Cohomology ℚ X n) :=
  inferInstance


def rational_zToQChainGroup (X : TopCat) (n : ℕ) :
    (rational_ZChains X).X n →ₗ[ℤ] (rational_QChainsModel X).X n :=
  ((chainGroupFinsuppIso ℚ X n).symm.toLinearEquiv.restrictScalars ℤ).toLinearMap.comp
    ((Finsupp.mapRange.linearMap (Algebra.linearMap ℤ ℚ)).comp
      (chainGroupFinsuppIso ℤ X n).toLinearEquiv.toLinearMap)

@[simp]
lemma rational_zToQChainGroup_iota (X : TopCat) (n : ℕ)
    (x : (TopCat.toSSet.obj X).obj (Opposite.op (SimplexCategory.mk n))) (q : ℤ) :
    rational_zToQChainGroup X n
        ((SSet.ιChainComplex (C := ModuleCat ℤ) (R := ModuleCat.of ℤ ℤ)
          (TopCat.toSSet.obj X) x).hom q) =
      (SSet.ιChainComplex (C := ModuleCat ℚ) (R := ModuleCat.of ℚ ℚ)
        (TopCat.toSSet.obj X) x).hom (algebraMap ℤ ℚ q) := by
  change (chainGroupFinsuppIso ℚ X n).symm.toLinearEquiv
      ((Finsupp.mapRange.linearMap (Algebra.linearMap ℤ ℚ))
        ((chainGroupFinsuppIso ℤ X n).toLinearEquiv
          ((SSet.ιChainComplex (C := ModuleCat ℤ) (R := ModuleCat.of ℤ ℤ)
            (TopCat.toSSet.obj X) x).hom q))) = _
  apply (chainGroupFinsuppIso ℚ X n).toLinearEquiv.injective
  rw [← Iso.toLinearEquiv_symm, LinearEquiv.apply_symm_apply,
    chainGroupFinsuppIso_iota, chainGroupFinsuppIso_iota]
  simp


lemma rational_zToQChainGroup_isBaseChange (X : TopCat) (n : ℕ) :
    IsBaseChange ℚ (rational_zToQChainGroup X n) := by
  apply (IsBaseChange.iff_of_equiv_comm
    (chainGroupFinsuppIso ℤ X n).toLinearEquiv
    (chainGroupFinsuppIso ℚ X n).toLinearEquiv ?_).mpr
  · exact IsBaseChange.finsuppPow _ (IsBaseChange.linearMap ℤ ℚ)
  · ext z
    simp [rational_zToQChainGroup]


abbrev rational_RestrictedQChainsModel (X : TopCat) : ChainComplex (ModuleCat ℤ) ℕ :=
  ((ModuleCat.restrictScalars (algebraMap ℤ ℚ)).mapHomologicalComplex
    (ComplexShape.down ℕ)).obj (rational_QChainsModel X)


def rational_zToQChainMap (X : TopCat) : rational_ZChains X ⟶ rational_RestrictedQChainsModel X where
  f n := ModuleCat.ofHom (X := (rational_ZChains X).X n)
    (Y := (rational_RestrictedQChainsModel X).X n)
    ((rational_zToQChainGroup X n).toAddMonoidHom.integralMap
      (mN := ((rational_RestrictedQChainsModel X).X n).isModule))
  comm' i j hij := by
    rw [ComplexShape.down_Rel] at hij
    obtain rfl : i = j + 1 := hij.symm
    apply SSet.chainComplex_hom_ext (X := TopCat.toSSet.obj X)
    intro x
    ext
    change ((rational_QChainsModel X).d (j + 1) j).hom
        (rational_zToQChainGroup X (j + 1)
          ((SSet.ιChainComplex (C := ModuleCat ℤ) (R := ModuleCat.of ℤ ℤ)
            (TopCat.toSSet.obj X) x).hom 1)) =
      rational_zToQChainGroup X j
        (((rational_ZChains X).d (j + 1) j).hom
          ((SSet.ιChainComplex (C := ModuleCat ℤ) (R := ModuleCat.of ℤ ℤ)
            (TopCat.toSSet.obj X) x).hom 1))
    rw [rational_zToQChainGroup_iota, map_one]
    change ((SSet.ιChainComplex (C := ModuleCat ℚ) (R := ModuleCat.of ℚ ℚ)
        (TopCat.toSSet.obj X) x ≫ (rational_QChainsModel X).d (j + 1) j).hom 1) = _
    rw [SSet.ιChainComplex_d]
    change _ = rational_zToQChainGroup X j
      ((SSet.ιChainComplex (C := ModuleCat ℤ) (R := ModuleCat.of ℤ ℤ)
        (TopCat.toSSet.obj X) x ≫ (rational_ZChains X).d (j + 1) j).hom 1)
    rw [SSet.ιChainComplex_d]
    simp only [ModuleCat.hom_sum, ModuleCat.hom_zsmul, LinearMap.coe_sum,
      Finset.sum_apply, map_sum]
    apply Finset.sum_congr rfl
    intro k hk
    change ((-1 : ℤ) ^ k.val) •
        ((SSet.ιChainComplex (C := ModuleCat ℚ) (R := ModuleCat.of ℚ ℚ)
          (TopCat.toSSet.obj X) ((SimplicialObject.δ (TopCat.toSSet.obj X) k) x)).hom 1) =
      rational_zToQChainGroup X j (((-1 : ℤ) ^ k.val) •
        ((SSet.ιChainComplex (C := ModuleCat ℤ) (R := ModuleCat.of ℤ ℤ)
          (TopCat.toSSet.obj X) ((SimplicialObject.δ (TopCat.toSSet.obj X) k) x)).hom 1))
    rw [map_zsmul]
    refine congrArg (fun z : (rational_QChainsModel X).X j ↦ ((-1 : ℤ) ^ k.val) • z) ?_
    symm
    simpa using (rational_zToQChainGroup_iota X j
      ((SimplicialObject.δ (TopCat.toSSet.obj X) k) x) 1)


abbrev rational_QCyclesModel (X : TopCat) (n : ℕ) :=
  ((rational_QChainsModel X).sc n).homologyData.left.K


local instance (X : TopCat) (n : ℕ) : IsScalarTower ℤ ℚ (rational_QCyclesModel X n) :=
  inferInstance


local instance (X : TopCat) (n : ℕ) : IsScalarTower ℤ ℚ ((rational_QChainsModel X).homology n) :=
  inferInstance


def rational_restrictedQChainsModelCyclesIso (X : TopCat) (n : ℕ) :
    (rational_RestrictedQChainsModel X).cycles n ≅
      (ModuleCat.restrictScalars (algebraMap ℤ ℚ)).obj (rational_QCyclesModel X n) :=
  (((rational_QChainsModel X).sc n).homologyData.left.map
    (ModuleCat.restrictScalars (algebraMap ℤ ℚ))).cyclesIso


def rational_restrictedQChainsModelHomologyIso (X : TopCat) (n : ℕ) :
    (rational_RestrictedQChainsModel X).homology n ≅
      (ModuleCat.restrictScalars (algebraMap ℤ ℚ)).obj ((rational_QChainsModel X).homology n) :=
  (((rational_QChainsModel X).sc n).homologyData.left.map
    (ModuleCat.restrictScalars (algebraMap ℤ ℚ))).homologyIso


def rational_zToQCycles (X : TopCat) (n : ℕ) :
    (rational_ZChains X).cycles n →ₗ[ℤ] rational_QCyclesModel X n :=
  (HomologicalComplex.cyclesMap (rational_zToQChainMap X) n ≫
    (rational_restrictedQChainsModelCyclesIso X n).hom).hom.toAddMonoidHom.integralMap (mN := AddCommGroup.toIntModule _)


def rational_zToQHomology (X : TopCat) (n : ℕ) :
    (rational_ZChains X).homology n →ₗ[ℤ] (rational_QChainsModel X).homology n :=
  (HomologicalComplex.homologyMap (rational_zToQChainMap X) n ≫
    (rational_restrictedQChainsModelHomologyIso X n).hom).hom.toAddMonoidHom.integralMap (mN := AddCommGroup.toIntModule _)

lemma rational_iCycles_comp_zToQChainGroup (X : TopCat) (n : ℕ) :
    (rational_zToQChainGroup X n).comp ((rational_ZChains X).iCycles n).hom =
      (((rational_QChainsModel X).sc n).homologyData.left.i.hom.restrictScalars ℤ).comp
        (rational_zToQCycles X n) := by
  ext z
  have h₁ := DFunLike.congr_fun
    (congrArg ModuleCat.Hom.hom
      (HomologicalComplex.cyclesMap_i (rational_zToQChainMap X) n).symm) z
  have h₂ := DFunLike.congr_fun
    (congrArg ModuleCat.Hom.hom
      (((rational_QChainsModel X).sc n).homologyData.left.map
        (ModuleCat.restrictScalars (algebraMap ℤ ℚ))).cyclesIso_hom_comp_i)
    ((HomologicalComplex.cyclesMap (rational_zToQChainMap X) n).hom z)
  exact h₁.trans h₂.symm

lemma rational_restrictedQChainsModel_homologyπ_iso (X : TopCat) (n : ℕ) :
    (rational_RestrictedQChainsModel X).homologyπ n ≫
        (rational_restrictedQChainsModelHomologyIso X n).hom =
      (rational_restrictedQChainsModelCyclesIso X n).hom ≫
        (((rational_QChainsModel X).sc n).homologyData.left.map
          (ModuleCat.restrictScalars (algebraMap ℤ ℚ))).π :=
  (((rational_QChainsModel X).sc n).homologyData.left.map
    (ModuleCat.restrictScalars (algebraMap ℤ ℚ))).homologyπ_comp_homologyIso_hom

lemma rational_homologyπ_comp_zToQHomology (X : TopCat) (n : ℕ) :
    (rational_ZChains X).homologyπ n ≫ (HomologicalComplex.homologyMap (rational_zToQChainMap X) n ≫
      (rational_restrictedQChainsModelHomologyIso X n).hom) =
      (HomologicalComplex.cyclesMap (rational_zToQChainMap X) n ≫
      (rational_restrictedQChainsModelCyclesIso X n).hom) ≫
        (((rational_QChainsModel X).sc n).homologyData.left.map
          (ModuleCat.restrictScalars (algebraMap ℤ ℚ))).π := by
  change (rational_ZChains X).homologyπ n ≫
      (HomologicalComplex.homologyMap (rational_zToQChainMap X) n ≫
        (rational_restrictedQChainsModelHomologyIso X n).hom) =
    (HomologicalComplex.cyclesMap (rational_zToQChainMap X) n ≫
      (rational_restrictedQChainsModelCyclesIso X n).hom) ≫
        (((rational_QChainsModel X).sc n).homologyData.left.map
          (ModuleCat.restrictScalars (algebraMap ℤ ℚ))).π
  rw [HomologicalComplex.homologyπ_naturality_assoc]
  simp only [rational_restrictedQChainsModel_homologyπ_iso]
  rfl


lemma rational_zToQCycles_isBaseChange (X : TopCat) (n : ℕ) :
    IsBaseChange ℚ (rational_zToQCycles X n) := by
  have ht₁ : IsScalarTower ℤ ℚ (rational_QCyclesModel X n) :=
    inferInstance
  have ht₂ : IsScalarTower ℤ ℚ ((rational_QChainsModel X).X n) :=
    inferInstance
  have ht₃ : IsScalarTower ℤ ℚ
      ((rational_QChainsModel X).X ((ComplexShape.down ℕ).next n)) :=
    inferInstance
  let hQ := (rational_ZChains X).sc n |>.leftHomologyData
  let hC := (rational_QChainsModel X).sc n |>.homologyData.left
  refine @IsBaseChange.of_left_exact
    ℤ _ ℚ _ _
    ((rational_ZChains X).cycles n) ((rational_ZChains X).X n)
    ((rational_ZChains X).X ((ComplexShape.down ℕ).next n))
    (rational_QCyclesModel X n) ((rational_QChainsModel X).X n)
    ((rational_QChainsModel X).X ((ComplexShape.down ℕ).next n))
    _ _ _ _ _ _
    _ _ _ _ _ _
    _ _ _ ht₁ ht₂ ht₃
    (rational_zToQCycles X n) (rational_zToQChainGroup X n)
    (rational_zToQChainGroup X ((ComplexShape.down ℕ).next n))
    hQ.i.hom ((rational_ZChains X).d n ((ComplexShape.down ℕ).next n)).hom
    hC.i.hom ((rational_QChainsModel X).d n ((ComplexShape.down ℕ).next n)).hom
    ?_ ?_ _ (rational_zToQChainGroup_isBaseChange X n)
    (rational_zToQChainGroup_isBaseChange X ((ComplexShape.down ℕ).next n)) ?_ ?_ ?_ ?_
  · ext z
    exact DFunLike.congr_fun (rational_iCycles_comp_zToQChainGroup X n) z
  · ext z
    have h := (rational_zToQChainMap X).comm n ((ComplexShape.down ℕ).next n)
    exact DFunLike.congr_fun (congrArg ModuleCat.Hom.hom h.symm) z
  · let T := ShortComplex.mk hQ.i ((rational_ZChains X).sc n).g hQ.wi
    exact (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact T).mp
      (T.exact_of_f_is_kernel hQ.hi)
  · exact (ModuleCat.mono_iff_injective hQ.i).mp
      (Limits.mono_of_isLimit_fork hQ.hi)
  · let T := ShortComplex.mk hC.i ((rational_QChainsModel X).sc n).g hC.wi
    exact (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact T).mp
      (T.exact_of_f_is_kernel hC.hi)
  · exact (ModuleCat.mono_iff_injective hC.i).mp
      (Limits.mono_of_isLimit_fork hC.hi)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
lemma rational_restrictedQChainsModel_toCycles_iso (X : TopCat) (n : ℕ) :
    ((rational_RestrictedQChainsModel X).sc n).toCycles ≫
        (rational_restrictedQChainsModelCyclesIso X n).hom =
      (((rational_QChainsModel X).sc n).homologyData.left.map
        (ModuleCat.restrictScalars (algebraMap ℤ ℚ))).f' := by
  rw [← cancel_mono (((rational_QChainsModel X).sc n).homologyData.left.map
    (ModuleCat.restrictScalars (algebraMap ℤ ℚ))).i, Category.assoc,
    show (rational_restrictedQChainsModelCyclesIso X n).hom ≫
      (((rational_QChainsModel X).sc n).homologyData.left.map
        (ModuleCat.restrictScalars (algebraMap ℤ ℚ))).i =
      ((rational_RestrictedQChainsModel X).sc n).iCycles from
      (((rational_QChainsModel X).sc n).homologyData.left.map
        (ModuleCat.restrictScalars (algebraMap ℤ ℚ))).cyclesIso_hom_comp_i,
    ShortComplex.toCycles_i]
  simp only [ShortComplex.LeftHomologyData.map_f',
    ShortComplex.LeftHomologyData.map_i, ← Functor.map_comp,
    ShortComplex.LeftHomologyData.f'_i]
  rfl

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
lemma rational_toCycles_comp_zToQCycles (X : TopCat) (n : ℕ) :
    (rational_zToQCycles X n).comp (((rational_ZChains X).sc n).toCycles.hom) =
      (((rational_QChainsModel X).sc n).homologyData.left.f'.hom.restrictScalars ℤ).comp
        (rational_zToQChainGroup X ((ComplexShape.down ℕ).prev n)) := by
  ext z
  let φ := (HomologicalComplex.shortComplexFunctor (ModuleCat ℤ)
    (ComplexShape.down ℕ) n).map (rational_zToQChainMap X)
  have h : (((rational_ZChains X).sc n).toCycles ≫
      ShortComplex.cyclesMap φ) ≫ (rational_restrictedQChainsModelCyclesIso X n).hom =
      φ.τ₁ ≫ (((rational_QChainsModel X).sc n).homologyData.left.map
        (ModuleCat.restrictScalars (algebraMap ℤ ℚ))).f' := by
    rw [ShortComplex.toCycles_naturality, Category.assoc, rational_restrictedQChainsModel_toCycles_iso]
  rw [ShortComplex.LeftHomologyData.map_f'] at h
  exact DFunLike.congr_fun (congrArg ModuleCat.Hom.hom h) z


lemma rational_zToQHomology_isBaseChange (X : TopCat) (n : ℕ) :
    IsBaseChange ℚ (rational_zToQHomology X n) := by
  have ht₁ : IsScalarTower ℤ ℚ
      ((rational_QChainsModel X).X ((ComplexShape.down ℕ).prev n)) :=
    inferInstance
  have ht₂ : IsScalarTower ℤ ℚ (rational_QCyclesModel X n) :=
    inferInstance
  have ht₃ : IsScalarTower ℤ ℚ ((rational_QChainsModel X).homology n) :=
    inferInstance
  let hC := (rational_QChainsModel X).sc n |>.homologyData.left
  refine @IsBaseChange.of_right_exact
    ℤ _ ℚ _ _
    ((rational_ZChains X).X ((ComplexShape.down ℕ).prev n)) ((rational_ZChains X).cycles n)
    ((rational_ZChains X).homology n)
    ((rational_QChainsModel X).X ((ComplexShape.down ℕ).prev n)) (rational_QCyclesModel X n)
    ((rational_QChainsModel X).homology n)
    _ _ _ _ _ _
    _ _ _ _ _ _
    _ _ _ ht₁ ht₂ ht₃
    (rational_zToQChainGroup X ((ComplexShape.down ℕ).prev n))
    (rational_zToQCycles X n) (rational_zToQHomology X n)
    ((rational_ZChains X).sc n).toCycles.hom ((rational_ZChains X).homologyπ n).hom
    hC.f'.hom hC.π.hom
    ?_ ?_ (rational_zToQChainGroup_isBaseChange X ((ComplexShape.down ℕ).prev n))
    (rational_zToQCycles_isBaseChange X n) ?_ ?_ ?_ ?_
  · ext z
    have hz := DFunLike.congr_fun (rational_toCycles_comp_zToQCycles X n) z
    change rational_zToQCycles X n (((rational_ZChains X).sc n).toCycles.hom z) =
      hC.f'.hom (rational_zToQChainGroup X ((ComplexShape.down ℕ).prev n) z)
    exact hz
  · ext z
    have h := rational_homologyπ_comp_zToQHomology X n
    have hz := DFunLike.congr_fun (congrArg ModuleCat.Hom.hom h) z
    change rational_zToQHomology X n (((rational_ZChains X).homologyπ n).hom z) =
      hC.π.hom (rational_zToQCycles X n z)
    rw [ShortComplex.LeftHomologyData.map_π] at hz
    exact hz
  · let T := ShortComplex.mk ((rational_ZChains X).sc n).toCycles
      ((rational_ZChains X).homologyπ n) ((rational_ZChains X).sc n).toCycles_comp_homologyπ
    exact (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact T).mp
      (T.exact_of_g_is_cokernel ((rational_ZChains X).sc n).homologyIsCokernel)
  · exact (ModuleCat.epi_iff_surjective ((rational_ZChains X).homologyπ n)).mp inferInstance
  · let T := ShortComplex.mk hC.f' hC.π hC.wπ
    exact (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact T).mp
      (T.exact_of_g_is_cokernel hC.hπ)
  · exact (ModuleCat.epi_iff_surjective hC.π).mp
      (Limits.epi_of_isColimit_cofork hC.hπ)


end HodgeLean.Foundations.IntegralHomology
