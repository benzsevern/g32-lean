import HodgeLean.Foundations.Program.SchoenTransferC1a6IntegralCoefficients
import Mathlib.RingTheory.Flat.TorsionFree
import HodgeLean.Foundations.Program.SchoenTransferC1a6IntegralIntFunctor

/-! Coefficient extension of integral singular homology to complex coefficients. -/
noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits AlgebraicTopology AlgebraicTopology.Singular
open scoped Simplicial TensorProduct
namespace HodgeLean.Foundations.Program

abbrev s4_c1a6_zbc_ZChains (X : TopCat) :=
  (TopCat.toSSet.obj X).chainComplex (ModuleCat.of ℤ ℤ)


abbrev s4_c1a6_zbc_CChains (X : TopCat) :=
  (TopCat.toSSet.obj X).chainComplex (ModuleCat.of ℂ ℂ)


local instance (X : TopCat) (n : ℕ) : IsScalarTower ℤ ℂ ((s4_c1a6_zbc_CChains X).X n) :=
  inferInstance


local instance (X : TopCat) (n : ℕ) : IsScalarTower ℤ ℂ (Cohomology ℂ X n) :=
  inferInstance


def s4_c1a6_zbc_zToCChainGroup (X : TopCat) (n : ℕ) :
    (s4_c1a6_zbc_ZChains X).X n →ₗ[ℤ] (s4_c1a6_zbc_CChains X).X n :=
  ((chainGroupFinsuppIso ℂ X n).symm.toLinearEquiv.restrictScalars ℤ).toLinearMap.comp
    ((Finsupp.mapRange.linearMap (Algebra.linearMap ℤ ℂ)).comp
      (chainGroupFinsuppIso ℤ X n).toLinearEquiv.toLinearMap)

@[simp]
lemma s4_c1a6_zbc_zToCChainGroup_iota (X : TopCat) (n : ℕ)
    (x : (TopCat.toSSet.obj X).obj (Opposite.op (SimplexCategory.mk n))) (q : ℤ) :
    s4_c1a6_zbc_zToCChainGroup X n
        ((SSet.ιChainComplex (C := ModuleCat ℤ) (R := ModuleCat.of ℤ ℤ)
          (TopCat.toSSet.obj X) x).hom q) =
      (SSet.ιChainComplex (C := ModuleCat ℂ) (R := ModuleCat.of ℂ ℂ)
        (TopCat.toSSet.obj X) x).hom (algebraMap ℤ ℂ q) := by
  change (chainGroupFinsuppIso ℂ X n).symm.toLinearEquiv
      ((Finsupp.mapRange.linearMap (Algebra.linearMap ℤ ℂ))
        ((chainGroupFinsuppIso ℤ X n).toLinearEquiv
          ((SSet.ιChainComplex (C := ModuleCat ℤ) (R := ModuleCat.of ℤ ℤ)
            (TopCat.toSSet.obj X) x).hom q))) = _
  apply (chainGroupFinsuppIso ℂ X n).toLinearEquiv.injective
  rw [← Iso.toLinearEquiv_symm, LinearEquiv.apply_symm_apply,
    chainGroupFinsuppIso_iota, chainGroupFinsuppIso_iota]
  simp


lemma s4_c1a6_zbc_zToCChainGroup_isBaseChange (X : TopCat) (n : ℕ) :
    IsBaseChange ℂ (s4_c1a6_zbc_zToCChainGroup X n) := by
  apply (IsBaseChange.iff_of_equiv_comm
    (chainGroupFinsuppIso ℤ X n).toLinearEquiv
    (chainGroupFinsuppIso ℂ X n).toLinearEquiv ?_).mpr
  · exact IsBaseChange.finsuppPow _ (IsBaseChange.linearMap ℤ ℂ)
  · ext z
    simp [s4_c1a6_zbc_zToCChainGroup]


abbrev s4_c1a6_zbc_RestrictedCChains (X : TopCat) : ChainComplex (ModuleCat ℤ) ℕ :=
  (s4_c1a6_forgetComplexToInt.mapHomologicalComplex
    (ComplexShape.down ℕ)).obj (s4_c1a6_zbc_CChains X)


def s4_c1a6_zbc_zToCChainMap (X : TopCat) : s4_c1a6_zbc_ZChains X ⟶ s4_c1a6_zbc_RestrictedCChains X where
  f n := ModuleCat.ofHom (s4_c1a6_zbc_zToCChainGroup X n)
  comm' i j hij := by
    rw [ComplexShape.down_Rel] at hij
    obtain rfl : i = j + 1 := hij.symm
    apply SSet.chainComplex_hom_ext (X := TopCat.toSSet.obj X)
    intro x
    ext
    change ((s4_c1a6_zbc_CChains X).d (j + 1) j).hom
        (s4_c1a6_zbc_zToCChainGroup X (j + 1)
          ((SSet.ιChainComplex (C := ModuleCat ℤ) (R := ModuleCat.of ℤ ℤ)
            (TopCat.toSSet.obj X) x).hom 1)) =
      s4_c1a6_zbc_zToCChainGroup X j
        (((s4_c1a6_zbc_ZChains X).d (j + 1) j).hom
          ((SSet.ιChainComplex (C := ModuleCat ℤ) (R := ModuleCat.of ℤ ℤ)
            (TopCat.toSSet.obj X) x).hom 1))
    rw [s4_c1a6_zbc_zToCChainGroup_iota, map_one]
    change ((SSet.ιChainComplex (C := ModuleCat ℂ) (R := ModuleCat.of ℂ ℂ)
        (TopCat.toSSet.obj X) x ≫ (s4_c1a6_zbc_CChains X).d (j + 1) j).hom 1) = _
    rw [SSet.ιChainComplex_d]
    change _ = s4_c1a6_zbc_zToCChainGroup X j
      ((SSet.ιChainComplex (C := ModuleCat ℤ) (R := ModuleCat.of ℤ ℤ)
        (TopCat.toSSet.obj X) x ≫ (s4_c1a6_zbc_ZChains X).d (j + 1) j).hom 1)
    rw [SSet.ιChainComplex_d]
    simp only [ModuleCat.hom_sum, ModuleCat.hom_zsmul, LinearMap.coe_sum,
      Finset.sum_apply, map_sum]
    apply Finset.sum_congr rfl
    intro k hk
    change ((-1 : ℤ) ^ k.val) •
        ((SSet.ιChainComplex (C := ModuleCat ℂ) (R := ModuleCat.of ℂ ℂ)
          (TopCat.toSSet.obj X) ((SimplicialObject.δ (TopCat.toSSet.obj X) k) x)).hom 1) =
      s4_c1a6_zbc_zToCChainGroup X j (((-1 : ℤ) ^ k.val) •
        ((SSet.ιChainComplex (C := ModuleCat ℤ) (R := ModuleCat.of ℤ ℤ)
          (TopCat.toSSet.obj X) ((SimplicialObject.δ (TopCat.toSSet.obj X) k) x)).hom 1))
    rw [map_zsmul]
    refine congrArg (fun z : (s4_c1a6_zbc_CChains X).X j ↦ ((-1 : ℤ) ^ k.val) • z) ?_
    symm
    simpa using (s4_c1a6_zbc_zToCChainGroup_iota X j
      ((SimplicialObject.δ (TopCat.toSSet.obj X) k) x) 1)


abbrev s4_c1a6_zbc_CCyclesModel (X : TopCat) (n : ℕ) :=
  ((s4_c1a6_zbc_CChains X).sc n).homologyData.left.K


local instance (X : TopCat) (n : ℕ) : IsScalarTower ℤ ℂ (s4_c1a6_zbc_CCyclesModel X n) :=
  inferInstance


local instance (X : TopCat) (n : ℕ) : IsScalarTower ℤ ℂ ((s4_c1a6_zbc_CChains X).homology n) :=
  inferInstance


def s4_c1a6_zbc_restrictedCChainsCyclesIso (X : TopCat) (n : ℕ) :
    (s4_c1a6_zbc_RestrictedCChains X).cycles n ≅
      s4_c1a6_forgetComplexToInt.obj (s4_c1a6_zbc_CCyclesModel X n) :=
  (((s4_c1a6_zbc_CChains X).sc n).homologyData.left.map
    s4_c1a6_forgetComplexToInt).cyclesIso


def s4_c1a6_zbc_restrictedCChainsHomologyIso (X : TopCat) (n : ℕ) :
    (s4_c1a6_zbc_RestrictedCChains X).homology n ≅
      s4_c1a6_forgetComplexToInt.obj ((s4_c1a6_zbc_CChains X).homology n) :=
  (((s4_c1a6_zbc_CChains X).sc n).homologyData.left.map
    s4_c1a6_forgetComplexToInt).homologyIso


def s4_c1a6_zbc_zToCCycles (X : TopCat) (n : ℕ) :
    (s4_c1a6_zbc_ZChains X).cycles n →ₗ[ℤ] s4_c1a6_zbc_CCyclesModel X n :=
  (s4_c1a6_zbc_restrictedCChainsCyclesIso X n).hom.hom.comp
    (HomologicalComplex.cyclesMap (s4_c1a6_zbc_zToCChainMap X) n).hom


def s4_c1a6_zbc_zToCHomology (X : TopCat) (n : ℕ) :
    (s4_c1a6_zbc_ZChains X).homology n →ₗ[ℤ] (s4_c1a6_zbc_CChains X).homology n :=
  (HomologicalComplex.homologyMap (s4_c1a6_zbc_zToCChainMap X) n ≫
    (s4_c1a6_zbc_restrictedCChainsHomologyIso X n).hom).hom

lemma s4_c1a6_zbc_iCycles_comp_zToCChainGroup (X : TopCat) (n : ℕ) :
    (s4_c1a6_zbc_zToCChainGroup X n).comp ((s4_c1a6_zbc_ZChains X).iCycles n).hom =
      (((s4_c1a6_zbc_CChains X).sc n).homologyData.left.map
        s4_c1a6_forgetComplexToInt).i.hom.comp
        (s4_c1a6_zbc_zToCCycles X n) := by
  ext z
  have h₁ := DFunLike.congr_fun
    (congrArg ModuleCat.Hom.hom
      (HomologicalComplex.cyclesMap_i (s4_c1a6_zbc_zToCChainMap X) n).symm) z
  have h₂ := DFunLike.congr_fun
    (congrArg ModuleCat.Hom.hom
      (((s4_c1a6_zbc_CChains X).sc n).homologyData.left.map
        s4_c1a6_forgetComplexToInt).cyclesIso_hom_comp_i)
    ((HomologicalComplex.cyclesMap (s4_c1a6_zbc_zToCChainMap X) n).hom z)
  exact h₁.trans h₂.symm

lemma s4_c1a6_zbc_restrictedCChains_homologyπ_iso (X : TopCat) (n : ℕ) :
    (s4_c1a6_zbc_RestrictedCChains X).homologyπ n ≫
        (s4_c1a6_zbc_restrictedCChainsHomologyIso X n).hom =
      (s4_c1a6_zbc_restrictedCChainsCyclesIso X n).hom ≫
        (((s4_c1a6_zbc_CChains X).sc n).homologyData.left.map
          s4_c1a6_forgetComplexToInt).π :=
  (((s4_c1a6_zbc_CChains X).sc n).homologyData.left.map
    s4_c1a6_forgetComplexToInt).homologyπ_comp_homologyIso_hom

lemma s4_c1a6_zbc_homologyπ_comp_zToCHomology (X : TopCat) (n : ℕ) :
    (s4_c1a6_zbc_ZChains X).homologyπ n ≫ ModuleCat.ofHom (s4_c1a6_zbc_zToCHomology X n) =
      ModuleCat.ofHom (s4_c1a6_zbc_zToCCycles X n) ≫
        (((s4_c1a6_zbc_CChains X).sc n).homologyData.left.map
          s4_c1a6_forgetComplexToInt).π := by
  change (s4_c1a6_zbc_ZChains X).homologyπ n ≫
      (HomologicalComplex.homologyMap (s4_c1a6_zbc_zToCChainMap X) n ≫
        (s4_c1a6_zbc_restrictedCChainsHomologyIso X n).hom) =
    (HomologicalComplex.cyclesMap (s4_c1a6_zbc_zToCChainMap X) n ≫
      (s4_c1a6_zbc_restrictedCChainsCyclesIso X n).hom) ≫
        (((s4_c1a6_zbc_CChains X).sc n).homologyData.left.map
          s4_c1a6_forgetComplexToInt).π
  rw [HomologicalComplex.homologyπ_naturality_assoc]
  simp only [s4_c1a6_zbc_restrictedCChains_homologyπ_iso]
  rfl


lemma s4_c1a6_zbc_zToCCycles_isBaseChange (X : TopCat) (n : ℕ) :
    IsBaseChange ℂ (s4_c1a6_zbc_zToCCycles X n) := by
  have ht₁ : IsScalarTower ℤ ℂ (s4_c1a6_zbc_CCyclesModel X n) :=
    inferInstance
  have ht₂ : IsScalarTower ℤ ℂ ((s4_c1a6_zbc_CChains X).X n) :=
    inferInstance
  have ht₃ : IsScalarTower ℤ ℂ
      ((s4_c1a6_zbc_CChains X).X ((ComplexShape.down ℕ).next n)) :=
    inferInstance
  let hQ := (s4_c1a6_zbc_ZChains X).sc n |>.leftHomologyData
  let hC := (s4_c1a6_zbc_CChains X).sc n |>.homologyData.left
  refine @IsBaseChange.of_left_exact
    ℤ _ ℂ _ _
    ((s4_c1a6_zbc_ZChains X).cycles n) ((s4_c1a6_zbc_ZChains X).X n)
    ((s4_c1a6_zbc_ZChains X).X ((ComplexShape.down ℕ).next n))
    (s4_c1a6_zbc_CCyclesModel X n) ((s4_c1a6_zbc_CChains X).X n)
    ((s4_c1a6_zbc_CChains X).X ((ComplexShape.down ℕ).next n))
    _ _ _ _ _ _
    _ _ _ _ _ _
    _ _ _ ht₁ ht₂ ht₃
    (s4_c1a6_zbc_zToCCycles X n) (s4_c1a6_zbc_zToCChainGroup X n)
    (s4_c1a6_zbc_zToCChainGroup X ((ComplexShape.down ℕ).next n))
    hQ.i.hom ((s4_c1a6_zbc_ZChains X).d n ((ComplexShape.down ℕ).next n)).hom
    hC.i.hom ((s4_c1a6_zbc_CChains X).d n ((ComplexShape.down ℕ).next n)).hom
    ?_ ?_ _ (s4_c1a6_zbc_zToCChainGroup_isBaseChange X n)
    (s4_c1a6_zbc_zToCChainGroup_isBaseChange X ((ComplexShape.down ℕ).next n)) ?_ ?_ ?_ ?_
  · ext z
    exact DFunLike.congr_fun (s4_c1a6_zbc_iCycles_comp_zToCChainGroup X n) z
  · ext z
    have h := (s4_c1a6_zbc_zToCChainMap X).comm n ((ComplexShape.down ℕ).next n)
    exact DFunLike.congr_fun (congrArg ModuleCat.Hom.hom h.symm) z
  · let T := ShortComplex.mk hQ.i ((s4_c1a6_zbc_ZChains X).sc n).g hQ.wi
    exact (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact T).mp
      (T.exact_of_f_is_kernel hQ.hi)
  · exact (ModuleCat.mono_iff_injective hQ.i).mp
      (Limits.mono_of_isLimit_fork hQ.hi)
  · let T := ShortComplex.mk hC.i ((s4_c1a6_zbc_CChains X).sc n).g hC.wi
    exact (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact T).mp
      (T.exact_of_f_is_kernel hC.hi)
  · exact (ModuleCat.mono_iff_injective hC.i).mp
      (Limits.mono_of_isLimit_fork hC.hi)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
lemma s4_c1a6_zbc_restrictedCChains_toCycles_iso (X : TopCat) (n : ℕ) :
    ((s4_c1a6_zbc_RestrictedCChains X).sc n).toCycles ≫
        (s4_c1a6_zbc_restrictedCChainsCyclesIso X n).hom =
      (((s4_c1a6_zbc_CChains X).sc n).homologyData.left.map
        s4_c1a6_forgetComplexToInt).f' := by
  rw [← cancel_mono (((s4_c1a6_zbc_CChains X).sc n).homologyData.left.map
    s4_c1a6_forgetComplexToInt).i, Category.assoc,
    show (s4_c1a6_zbc_restrictedCChainsCyclesIso X n).hom ≫
      (((s4_c1a6_zbc_CChains X).sc n).homologyData.left.map
        s4_c1a6_forgetComplexToInt).i =
      ((s4_c1a6_zbc_RestrictedCChains X).sc n).iCycles from
      (((s4_c1a6_zbc_CChains X).sc n).homologyData.left.map
        s4_c1a6_forgetComplexToInt).cyclesIso_hom_comp_i,
    ShortComplex.toCycles_i]
  simp only [ShortComplex.LeftHomologyData.map_f',
    ShortComplex.LeftHomologyData.map_i, ← Functor.map_comp,
    ShortComplex.LeftHomologyData.f'_i]
  rfl

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
lemma s4_c1a6_zbc_toCycles_comp_zToCCycles (X : TopCat) (n : ℕ) :
    (s4_c1a6_zbc_zToCCycles X n).comp (((s4_c1a6_zbc_ZChains X).sc n).toCycles.hom) =
      (((s4_c1a6_zbc_CChains X).sc n).homologyData.left.map
        s4_c1a6_forgetComplexToInt).f'.hom.comp
        (s4_c1a6_zbc_zToCChainGroup X ((ComplexShape.down ℕ).prev n)) := by
  ext z
  let φ := (HomologicalComplex.shortComplexFunctor (ModuleCat ℤ)
    (ComplexShape.down ℕ) n).map (s4_c1a6_zbc_zToCChainMap X)
  have h : (((s4_c1a6_zbc_ZChains X).sc n).toCycles ≫
      ShortComplex.cyclesMap φ) ≫ (s4_c1a6_zbc_restrictedCChainsCyclesIso X n).hom =
      φ.τ₁ ≫ (((s4_c1a6_zbc_CChains X).sc n).homologyData.left.map
        s4_c1a6_forgetComplexToInt).f' := by
    rw [ShortComplex.toCycles_naturality, Category.assoc, s4_c1a6_zbc_restrictedCChains_toCycles_iso]
  exact DFunLike.congr_fun (congrArg ModuleCat.Hom.hom h) z


lemma s4_c1a6_zbc_zToCHomology_isBaseChange (X : TopCat) (n : ℕ) :
    IsBaseChange ℂ (s4_c1a6_zbc_zToCHomology X n) := by
  have ht₁ : IsScalarTower ℤ ℂ
      ((s4_c1a6_zbc_CChains X).X ((ComplexShape.down ℕ).prev n)) :=
    inferInstance
  have ht₂ : IsScalarTower ℤ ℂ (s4_c1a6_zbc_CCyclesModel X n) :=
    inferInstance
  have ht₃ : IsScalarTower ℤ ℂ ((s4_c1a6_zbc_CChains X).homology n) :=
    inferInstance
  let hC := (s4_c1a6_zbc_CChains X).sc n |>.homologyData.left
  refine @IsBaseChange.of_right_exact
    ℤ _ ℂ _ _
    ((s4_c1a6_zbc_ZChains X).X ((ComplexShape.down ℕ).prev n)) ((s4_c1a6_zbc_ZChains X).cycles n)
    ((s4_c1a6_zbc_ZChains X).homology n)
    ((s4_c1a6_zbc_CChains X).X ((ComplexShape.down ℕ).prev n)) (s4_c1a6_zbc_CCyclesModel X n)
    ((s4_c1a6_zbc_CChains X).homology n)
    _ _ _ _ _ _
    _ _ _ _ _ _
    _ _ _ ht₁ ht₂ ht₃
    (s4_c1a6_zbc_zToCChainGroup X ((ComplexShape.down ℕ).prev n))
    (s4_c1a6_zbc_zToCCycles X n) (s4_c1a6_zbc_zToCHomology X n)
    ((s4_c1a6_zbc_ZChains X).sc n).toCycles.hom ((s4_c1a6_zbc_ZChains X).homologyπ n).hom
    hC.f'.hom hC.π.hom
    ?_ ?_ (s4_c1a6_zbc_zToCChainGroup_isBaseChange X ((ComplexShape.down ℕ).prev n))
    (s4_c1a6_zbc_zToCCycles_isBaseChange X n) ?_ ?_ ?_ ?_
  · ext z
    have hz := DFunLike.congr_fun (s4_c1a6_zbc_toCycles_comp_zToCCycles X n) z
    change s4_c1a6_zbc_zToCCycles X n (((s4_c1a6_zbc_ZChains X).sc n).toCycles.hom z) =
      hC.f'.hom (s4_c1a6_zbc_zToCChainGroup X ((ComplexShape.down ℕ).prev n) z)
    rw [ShortComplex.LeftHomologyData.map_f'] at hz
    exact hz
  · ext z
    have h := s4_c1a6_zbc_homologyπ_comp_zToCHomology X n
    have hz := DFunLike.congr_fun (congrArg ModuleCat.Hom.hom h) z
    change s4_c1a6_zbc_zToCHomology X n (((s4_c1a6_zbc_ZChains X).homologyπ n).hom z) =
      hC.π.hom (s4_c1a6_zbc_zToCCycles X n z)
    rw [ShortComplex.LeftHomologyData.map_π] at hz
    exact hz
  · let T := ShortComplex.mk ((s4_c1a6_zbc_ZChains X).sc n).toCycles
      ((s4_c1a6_zbc_ZChains X).homologyπ n) ((s4_c1a6_zbc_ZChains X).sc n).toCycles_comp_homologyπ
    exact (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact T).mp
      (T.exact_of_g_is_cokernel ((s4_c1a6_zbc_ZChains X).sc n).homologyIsCokernel)
  · exact (ModuleCat.epi_iff_surjective ((s4_c1a6_zbc_ZChains X).homologyπ n)).mp inferInstance
  · let T := ShortComplex.mk hC.f' hC.π hC.wπ
    exact (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact T).mp
      (T.exact_of_g_is_cokernel hC.hπ)
  · exact (ModuleCat.epi_iff_surjective hC.π).mp
      (Limits.epi_of_isColimit_cofork hC.hπ)


end HodgeLean.Foundations.Program
