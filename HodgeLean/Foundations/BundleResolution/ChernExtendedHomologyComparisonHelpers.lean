import HodgeLean.Foundations.BundleResolution.ChernDegreeLoweringChainHelpers

/-! # Homology of the actual integer-extended comparison

The middle chain component determines its action on cycles and therefore
its action on the unchanged homology groups, including degree zero.
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory HomologicalComplex
namespace HodgeLean.Foundations.BundleResolution

variable (K L : ChainComplex (ModuleCat ℚ) ℕ) (p n : ℕ)

private theorem sourceIndex : (ComplexShape.embeddingUpIntLE (p : ℤ)).f (p + n) = -(n : ℤ) := by
  simp only [ComplexShape.embeddingUpIntLE_f]
  omega

private theorem targetIndex : (ComplexShape.embeddingUpIntLE 0).f n = -(n : ℤ) := by
  simp only [ComplexShape.embeddingUpIntLE_f]
  omega

theorem i1_extendedHomologyMap_of_middle
    (F : K.extend (ComplexShape.embeddingUpIntLE (p : ℤ)) ⟶
      L.extend (ComplexShape.embeddingUpIntLE 0))
    (τ : K.sc (p + n) ⟶ L.sc n)
    (h : (K.extendXIso _ (sourceIndex p n)).inv ≫ F.f (-(n : ℤ)) ≫
      (L.extendXIso _ (targetIndex n)).hom = τ.τ₂) :
    (K.extendHomologyIso _ (sourceIndex p n)).inv ≫ homologyMap F (-(n : ℤ)) ≫
      (L.extendHomologyIso _ (targetIndex n)).hom = ShortComplex.homologyMap τ := by
  have hc : (K.extendCyclesIso _ (sourceIndex p n)).inv ≫ cyclesMap F (-(n : ℤ)) ≫
      (L.extendCyclesIso _ (targetIndex n)).hom = ShortComplex.cyclesMap τ := by
    apply (cancel_mono (L.iCycles n)).mp
    simp only [Category.assoc, extendCyclesIso_hom_iCycles, cyclesMap_i_assoc,
      extendCyclesIso_inv_iCycles_assoc]
    have hh := (congrArg (fun t => K.iCycles (p + n) ≫ t) h).trans
      (ShortComplex.cyclesMap_i τ).symm
    simpa only [HomologicalComplex.cycles, HomologicalComplex.iCycles,
      HomologicalComplex.homologyπ, Category.assoc] using hh
  apply (cancel_epi (K.homologyπ (p + n))).mp
  simp only [← Category.assoc, homologyπ_extendHomologyIso_inv]
  simp only [Category.assoc, homologyπ_naturality_assoc, homologyπ_extendHomologyIso_hom,
    ]
  have hh := (congrArg (fun t => t ≫ L.homologyπ n) hc).trans
    (ShortComplex.homologyπ_naturality τ).symm
  simpa only [HomologicalComplex.cycles, HomologicalComplex.iCycles,
    HomologicalComplex.homologyπ, Category.assoc] using hh

end HodgeLean.Foundations.BundleResolution
