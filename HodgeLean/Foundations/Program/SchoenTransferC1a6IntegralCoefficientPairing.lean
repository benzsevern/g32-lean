import HodgeLean.Foundations.Program.SchoenTransferC1a6IntegralBaseChange
import HodgeLean.Foundations.Program.SchoenTransferC1a6IntegralMap

/-! Evaluation of cohomology after integral coefficient extension. -/
noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicTopology.Singular
open HodgeLean.Adapters
namespace HodgeLean.Foundations.Program

theorem s4_c1a6_cohomologyClass_homologyπ (X : TopCat)
    (ψ : AlgebraicTopology.Simplicial.Cocycle ℂ (TopCat.toSSet.obj X) 1)
    (z : (CChains X).cycles 1) :
    AlgebraicTopology.Singular.cohomologyEquivDualHomology ℂ X 1
      (Singular.cohomologyClass X 1 ψ) ((CChains X).homologyπ 1 z) =
      ψ.val ((CChains X).iCycles 1 z) := by
  let S := (CChains X).sc 1
  have hp : S.moduleCatHomologyClass (S.moduleCatCyclesIso.hom z) = S.homologyπ z := by
    change ((S.moduleCatCyclesIso.hom ≫ S.moduleCatLeftHomologyData.π) ≫
      S.moduleCatHomologyIso.inv) z = _
    rw [← S.π_moduleCatCyclesIso_hom, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  erw [← hp, cohomologyEquivDualHomology_cohomologyClass]
  exact congrArg ψ.val (congrArg (fun k => k.hom z) S.moduleCatCyclesIso_hom_i)

theorem s4_c1a6_cohomologyClass_zToCHomology (X : TopCat)
    (ψ : AlgebraicTopology.Simplicial.Cocycle ℂ (TopCat.toSSet.obj X) 1)
    (z : (s4_c1a6_ZChains X).cycles 1) :
    AlgebraicTopology.Singular.cohomologyEquivDualHomology ℂ X 1
      (Singular.cohomologyClass X 1 ψ)
      (s4_c1a6_zbc_zToCHomology X 1 ((s4_c1a6_ZChains X).homologyπ 1 z)) =
    s4_c1a6_integralCocyclePairing X ψ
      (Submodule.Quotient.mk ((s4_c1a6_ZChains X).homologyπ 1 z)) := by
  rw [s4_c1a6_integralCocyclePairing_cycle]
  have h := DFunLike.congr_fun (congrArg ModuleCat.Hom.hom
    (s4_c1a6_zbc_homologyπ_comp_zToCHomology X 1)) z
  let hc := ((CChains X).sc 1).homologyData.left
  have hid : hc.homologyIso.inv = 𝟙 _ := by
    dsimp [hc, ShortComplex.LeftHomologyData.homologyIso,
      ShortComplex.leftHomologyIso, ShortComplex.LeftHomologyData.leftHomologyIso]
    exact Iso.inv_hom_id _
  have hp := hc.π_comp_homologyIso_inv
  rw [hid, Category.comp_id] at hp
  have he := DFunLike.congr_fun (congrArg ModuleCat.Hom.hom hp)
    (s4_c1a6_zbc_zToCCycles X 1 z)
  change s4_c1a6_zbc_zToCHomology X 1 ((s4_c1a6_ZChains X).homologyπ 1 z) =
    hc.π (s4_c1a6_zbc_zToCCycles X 1 z) at h
  change hc.π (s4_c1a6_zbc_zToCCycles X 1 z) =
    (CChains X).homologyπ 1 (hc.cyclesIso.inv (s4_c1a6_zbc_zToCCycles X 1 z)) at he
  erw [h, he, s4_c1a6_cohomologyClass_homologyπ]
  have hi := DFunLike.congr_fun (s4_c1a6_zbc_iCycles_comp_zToCChainGroup X 1) z
  have hi' := DFunLike.congr_fun (congrArg ModuleCat.Hom.hom hc.cyclesIso_inv_comp_iCycles)
    (s4_c1a6_zbc_zToCCycles X 1 z)
  change (CChains X).iCycles 1 (hc.cyclesIso.inv (s4_c1a6_zbc_zToCCycles X 1 z)) =
    hc.i (s4_c1a6_zbc_zToCCycles X 1 z) at hi'
  erw [hi', ← hi]
  rfl

end HodgeLean.Foundations.Program
