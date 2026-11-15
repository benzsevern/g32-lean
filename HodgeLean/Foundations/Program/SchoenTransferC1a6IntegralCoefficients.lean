import HodgeLean.Foundations.Program.SchoenTransferC1a6IntegralDescent
import HodgeLean.Foundations.Port.AlgebraicTopology.Singular.CoefficientBaseChange

/-! Integral coefficient extension for evaluating complex singular cocycles. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 200000
open CategoryTheory AlgebraicTopology.Singular
open scoped Simplicial
namespace HodgeLean.Foundations.Program
abbrev s4_c1a6_ZChains (X : TopCat) :=
  (TopCat.toSSet.obj X).chainComplex (ModuleCat.of ℤ ℤ)

def s4_c1a6_zToCChainGroup (X : TopCat) (n : ℕ) :
    (s4_c1a6_ZChains X).X n →ₗ[ℤ] (CChains X).X n :=
  ((chainGroupFinsuppIso ℂ X n).symm.toLinearEquiv.restrictScalars ℤ).toLinearMap.comp
    ((Finsupp.mapRange.linearMap ((Int.castAddHom ℂ).toIntLinearMap)).comp
      (chainGroupFinsuppIso ℤ X n).toLinearEquiv.toLinearMap)

@[simp]
lemma s4_c1a6_zToCChainGroup_iota (X : TopCat) (n : ℕ)
    (x : (TopCat.toSSet.obj X).obj (Opposite.op (SimplexCategory.mk n))) (q : ℤ) :
    s4_c1a6_zToCChainGroup X n
        ((SSet.ιChainComplex (C := ModuleCat ℤ) (R := ModuleCat.of ℤ ℤ)
          (TopCat.toSSet.obj X) x).hom q) =
      (SSet.ιChainComplex (C := ModuleCat ℂ) (R := ModuleCat.of ℂ ℂ)
        (TopCat.toSSet.obj X) x).hom ((q : ℂ)) := by
  change (chainGroupFinsuppIso ℂ X n).symm.toLinearEquiv
      ((Finsupp.mapRange.linearMap ((Int.castAddHom ℂ).toIntLinearMap))
        ((chainGroupFinsuppIso ℤ X n).toLinearEquiv
          ((SSet.ιChainComplex (C := ModuleCat ℤ) (R := ModuleCat.of ℤ ℤ)
            (TopCat.toSSet.obj X) x).hom q))) = _
  apply (chainGroupFinsuppIso ℂ X n).toLinearEquiv.injective
  rw [← Iso.toLinearEquiv_symm, LinearEquiv.apply_symm_apply,
    chainGroupFinsuppIso_iota, chainGroupFinsuppIso_iota]
  simp


theorem s4_c1a6_zToCChainGroup_d (X : TopCat) (j : ℕ) :
    (((CChains X).d (j + 1) j).hom.restrictScalars ℤ).comp
      (s4_c1a6_zToCChainGroup X (j + 1)) =
    (s4_c1a6_zToCChainGroup X j).comp
      ((s4_c1a6_ZChains X).d (j + 1) j).hom := by
  suffices h :
      (ModuleCat.ofHom ((((CChains X).d (j + 1) j).hom.restrictScalars ℤ).comp
        (s4_c1a6_zToCChainGroup X (j + 1))) :
          (s4_c1a6_ZChains X).X (j + 1) ⟶
            ModuleCat.of ℤ ((CChains X).X j)) =
      ModuleCat.ofHom ((s4_c1a6_zToCChainGroup X j).comp
        ((s4_c1a6_ZChains X).d (j + 1) j).hom) by
    exact congrArg ModuleCat.Hom.hom h
  apply SSet.chainComplex_hom_ext (X := TopCat.toSSet.obj X)
  intro x
  ext
  change ((CChains X).d (j + 1) j).hom
      (s4_c1a6_zToCChainGroup X (j + 1)
        ((SSet.ιChainComplex (R := ModuleCat.of ℤ ℤ) (TopCat.toSSet.obj X) x).hom 1)) =
    s4_c1a6_zToCChainGroup X j
      (((s4_c1a6_ZChains X).d (j + 1) j).hom
        ((SSet.ιChainComplex (R := ModuleCat.of ℤ ℤ) (TopCat.toSSet.obj X) x).hom 1))
  rw [s4_c1a6_zToCChainGroup_iota, Int.cast_one]
  change ((SSet.ιChainComplex (R := ModuleCat.of ℂ ℂ) (TopCat.toSSet.obj X) x ≫
    (CChains X).d (j + 1) j).hom 1) = _
  rw [SSet.ιChainComplex_d]
  change _ = s4_c1a6_zToCChainGroup X j
    ((SSet.ιChainComplex (R := ModuleCat.of ℤ ℤ) (TopCat.toSSet.obj X) x ≫
      (s4_c1a6_ZChains X).d (j + 1) j).hom 1)
  rw [SSet.ιChainComplex_d]
  simp only [ModuleCat.hom_sum, ModuleCat.hom_zsmul, LinearMap.coe_sum,
    Finset.sum_apply, map_sum]
  apply Finset.sum_congr rfl
  intro k hk
  change ((-1 : ℤ) ^ k.val) •
      ((SSet.ιChainComplex (R := ModuleCat.of ℂ ℂ) (TopCat.toSSet.obj X)
        ((TopCat.toSSet.obj X).δ k x)).hom 1) =
    s4_c1a6_zToCChainGroup X j (((-1 : ℤ) ^ k.val) •
      ((SSet.ιChainComplex (R := ModuleCat.of ℤ ℤ) (TopCat.toSSet.obj X)
        ((TopCat.toSSet.obj X).δ k x)).hom 1))
  rw [map_zsmul, s4_c1a6_zToCChainGroup_iota, Int.cast_one]

/-- Evaluation of a complex singular cocycle on an integral chain. -/
def s4_c1a6_integralCocycleChain (X : TopCat)
    (ψ : AlgebraicTopology.Simplicial.Cocycle ℂ (TopCat.toSSet.obj X) 1) :
    (s4_c1a6_ZChains X).X 1 →ₗ[ℤ] ℂ :=
  (ψ.val.restrictScalars ℤ).comp (s4_c1a6_zToCChainGroup X 1)

theorem s4_c1a6_integralCocycleChain_boundary_two (X : TopCat)
    (ψ : AlgebraicTopology.Simplicial.Cocycle ℂ (TopCat.toSSet.obj X) 1) :
    (s4_c1a6_integralCocycleChain X ψ).comp
      ((s4_c1a6_ZChains X).d 2 1).hom = 0 := by
  ext z
  change ψ.val (s4_c1a6_zToCChainGroup X 1
    (((s4_c1a6_ZChains X).d 2 1).hom z)) = 0
  have h := LinearMap.congr_fun (s4_c1a6_zToCChainGroup_d X 1) z
  change ((CChains X).d 2 1).hom (s4_c1a6_zToCChainGroup X 2 z) =
    s4_c1a6_zToCChainGroup X 1 (((s4_c1a6_ZChains X).d 2 1).hom z) at h
  rw [← h]
  exact LinearMap.congr_fun (LinearMap.mem_ker.mp ψ.property) _

theorem s4_c1a6_integralCocycleChain_boundary (X : TopCat)
    (ψ : AlgebraicTopology.Simplicial.Cocycle ℂ (TopCat.toSSet.obj X) 1) (i : ℕ) :
    (s4_c1a6_integralCocycleChain X ψ).comp
      ((s4_c1a6_ZChains X).d i 1).hom = 0 := by
  by_cases h : i = 2
  · subst i
    exact s4_c1a6_integralCocycleChain_boundary_two X ψ
  · rw [HomologicalComplex.shape _ _ _ (by simp only [ComplexShape.down_Rel]; omega)]
    simp only [ModuleCat.hom_zero, LinearMap.comp_zero]

/-- The pairing of a complex singular cocycle with integral homology modulo torsion. -/
def s4_c1a6_integralCocyclePairing (X : TopCat)
    (ψ : AlgebraicTopology.Simplicial.Cocycle ℂ (TopCat.toSSet.obj X) 1) :
    ((s4_c1a6_ZChains X).homology 1 ⧸
      Submodule.torsion ℤ ((s4_c1a6_ZChains X).homology 1)) →ₗ[ℤ] ℂ :=
  s4_c1a6_boundaryTorsionDesc ((s4_c1a6_ZChains X).sc 1)
    (s4_c1a6_integralCocycleChain X ψ)
    (s4_c1a6_integralCocycleChain_boundary X ψ _)

theorem s4_c1a6_integralCocyclePairing_cycle (X : TopCat)
    (ψ : AlgebraicTopology.Simplicial.Cocycle ℂ (TopCat.toSSet.obj X) 1)
    (z : (s4_c1a6_ZChains X).cycles 1) :
    s4_c1a6_integralCocyclePairing X ψ
      (Submodule.Quotient.mk ((s4_c1a6_ZChains X).homologyπ 1 z)) =
      ψ.val (s4_c1a6_zToCChainGroup X 1 ((s4_c1a6_ZChains X).iCycles 1 z)) :=
  s4_c1a6_boundaryTorsionDesc_cycle _ _ _ _

end HodgeLean.Foundations.Program
