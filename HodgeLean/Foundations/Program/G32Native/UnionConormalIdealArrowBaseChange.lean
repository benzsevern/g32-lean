import HodgeLean.Foundations.Program.G32Native.UnionConormalBaseChangeMono
import Mathlib.CategoryTheory.Comma.Arrow

/-! # Natural ideal arrows under invertible ambient comparisons -/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program.G32Native
open AlgebraicGeometry.Conormal

/-- Invertible vertical ideal comparisons identify the two first ideal arrows. -/
def unionConormalIdealArrowBaseChangeIso
    {Q₀ Q₁ W Q₀' Q₁' W' : Scheme.{0}}
    (i₀ : Q₀ ⟶ W) (i₁ : Q₁ ⟶ W) (a : Q₁ ⟶ Q₀) (ha : a ≫ i₀ = i₁)
    (i₀' : Q₀' ⟶ W') (i₁' : Q₁' ⟶ W') (a' : Q₁' ⟶ Q₀')
    (ha' : a' ≫ i₀' = i₁') (j : W' ⟶ W)
    (b₀ : Q₀' ⟶ Q₀) (b₁ : Q₁' ⟶ Q₁)
    (h₀ : b₀ ≫ i₀ = i₀' ≫ j) (h₁ : b₁ ≫ i₁ = i₁' ≫ j)
    (hb : a' ≫ b₀ = b₁ ≫ a)
    [IsIso (idealPullbackMap i₀ i₀' j b₀ h₀)]
    [IsIso (idealPullbackMap i₁ i₁' j b₁ h₁)] :
    Arrow.mk ((Scheme.Modules.pullback j).map
      (idealPullbackMap i₀ i₁ (𝟙 W) a (ha.trans (Category.comp_id i₁).symm))) ≅
      Arrow.mk (idealPullbackMap i₀' i₁' (𝟙 W') a'
        (ha'.trans (Category.comp_id i₁').symm)) := by
  let H := idealPullbackMap i₀ i₁ (𝟙 W) a (ha.trans (Category.comp_id i₁).symm)
  let H₀ := idealPullbackMap i₀ i₀' j b₀ h₀
  let H₁ := idealPullbackMap i₁ i₁' j b₁ h₁
  let H' := idealPullbackMap i₀' i₁' (𝟙 W') a' (ha'.trans (Category.comp_id i₁').symm)
  have ht : (b₁ ≫ a) ≫ i₀ = i₁' ≫ j := by rw [Category.assoc, ha, h₁]
  let T := idealPullbackMap i₀ i₁' j (b₁ ≫ a) ht
  let c₀ := (Scheme.Modules.pullbackComp (𝟙 W') j) ≪≫
    Scheme.Modules.pullbackCongr (Category.id_comp j)
  let c₁ := (Scheme.Modules.pullbackComp j (𝟙 W)) ≪≫
    Scheme.Modules.pullbackCongr (Category.comp_id j)
  have he₀ : c₀.inv.app (idealModule i₀) ≫
      (Scheme.Modules.pullback (𝟙 W')).map H₀ ≫ H' = T := by
    have htot : (a' ≫ b₀) ≫ i₀ = i₁' ≫ ((𝟙 W') ≫ j) := by
      rw [hb, Category.id_comp]; exact ht
    have hc := idealPullbackMap_comp i₀ i₀' i₁' j (𝟙 W') b₀ a' h₀
      (ha'.trans (Category.comp_id i₁').symm) htot
    have ht' := unionConormal_idealMap_congr_transport i₀ i₁'
      (Category.id_comp j) hb htot ht
    change (Scheme.Modules.pullbackCongr (Category.id_comp j)).inv.app (idealModule i₀) ≫
      (Scheme.Modules.pullbackComp (𝟙 W') j).inv.app (idealModule i₀) ≫
        (Scheme.Modules.pullback (𝟙 W')).map H₀ ≫ H' = T
    rw [hc, ← ht', Iso.inv_hom_id_app_assoc]
  have he₁ : c₁.inv.app (idealModule i₀) ≫
      (Scheme.Modules.pullback j).map H ≫ H₁ = T := by
    have htot : (b₁ ≫ a) ≫ i₀ = i₁' ≫ (j ≫ 𝟙 W) := by
      rw [Category.comp_id]; exact ht
    have hc := idealPullbackMap_comp i₀ i₁ i₁' (𝟙 W) j a b₁
      (ha.trans (Category.comp_id i₁).symm) h₁ htot
    have ht' := unionConormal_idealMap_congr_transport i₀ i₁'
      (Category.comp_id j) rfl htot ht
    change (Scheme.Modules.pullbackCongr (Category.comp_id j)).inv.app (idealModule i₀) ≫
      (Scheme.Modules.pullbackComp j (𝟙 W)).inv.app (idealModule i₀) ≫
        (Scheme.Modules.pullback j).map H ≫ H₁ = T
    rw [hc, ← ht', Iso.inv_hom_id_app_assoc]
  let e := (c₁.app (idealModule i₀)) ≪≫ (c₀.app (idealModule i₀)).symm ≪≫
    (Scheme.Modules.pullback (𝟙 W')).mapIso (asIso H₀)
  refine Arrow.isoMk e (asIso H₁) ?_
  change (c₁.hom.app (idealModule i₀) ≫ c₀.inv.app (idealModule i₀) ≫
    (Scheme.Modules.pullback (𝟙 W')).map H₀) ≫ H' =
      (Scheme.Modules.pullback j).map H ≫ H₁
  apply (cancel_epi (c₁.inv.app (idealModule i₀))).mp
  simp only [Category.assoc, Iso.inv_hom_id_app_assoc]
  exact he₀.trans he₁.symm

end HodgeLean.Foundations.Program.G32Native
