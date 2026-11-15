import HodgeLean.Foundations.Program.G32Native.UnionConormalIdealArrowBaseChange
import HodgeLean.Foundations.Program.G32Native.UnionConormalMaps

/-! # The first conormal arrow under invertible ideal comparisons -/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program.G32Native
open AlgebraicGeometry.Conormal

/-- Ambient and source identifications carry the actual first conormal arrow. -/
def unionConormalFirstArrowBaseChangeIso
    {Q₀ Q₁ W Q₀' Q₁' W' : Scheme.{0}}
    (i₀ : Q₀ ⟶ W) (i₁ : Q₁ ⟶ W) (a : Q₁ ⟶ Q₀) (ha : a ≫ i₀ = i₁)
    (i₀' : Q₀' ⟶ W') (i₁' : Q₁' ⟶ W') (a' : Q₁' ⟶ Q₀')
    (ha' : a' ≫ i₀' = i₁') (j : W' ⟶ W)
    (b₀ : Q₀' ⟶ Q₀) (b₁ : Q₁' ⟶ Q₁)
    (h₀ : b₀ ≫ i₀ = i₀' ≫ j) (h₁ : b₁ ≫ i₁ = i₁' ≫ j)
    (hb : a' ≫ b₀ = b₁ ≫ a)
    [IsIso (idealPullbackMap i₀ i₀' j b₀ h₀)]
    [IsIso (idealPullbackMap i₁ i₁' j b₁ h₁)] :
    Arrow.mk ((Scheme.Modules.pullback b₁).map (unionConormalFirst i₀ i₁ a ha)) ≅
      Arrow.mk (unionConormalFirst i₀' i₁' a' ha') := by
  let H := idealPullbackMap i₀ i₁ (𝟙 W) a (ha.trans (Category.comp_id i₁).symm)
  let H' := idealPullbackMap i₀' i₁' (𝟙 W') a' (ha'.trans (Category.comp_id i₁').symm)
  let G := Scheme.Modules.pullback b₁
  let F := Scheme.Modules.pullback i₁'
  let p := unionConormalComparisonPrefixIso i₀ i₁ (𝟙 W) a
    (ha.trans (Category.comp_id i₁).symm)
  let p' := unionConormalComparisonPrefixIso i₀' i₁' (𝟙 W') a'
    (ha'.trans (Category.comp_id i₁').symm)
  let eA : Arrow.mk (G.map (unionConormalFirst i₀ i₁ a ha)) ≅
      Arrow.mk (G.map ((Scheme.Modules.pullback i₁).map H)) :=
    Arrow.isoMk (G.mapIso p) (Iso.refl _) (by
      change G.map p.hom ≫ G.map ((Scheme.Modules.pullback i₁).map H) =
        G.map (unionConormalFirst i₀ i₁ a ha) ≫ 𝟙 _
      rw [Category.comp_id, ← Functor.map_comp]
      congr 1)
  let eB := Arrow.isoOfNatIso (unionConormalSquarePullbackIso i₁ i₁' j b₁ h₁)
    (Arrow.mk H)
  let eC := F.mapArrow.mapIso
    (unionConormalIdealArrowBaseChangeIso i₀ i₁ a ha i₀' i₁' a' ha' j b₀ b₁ h₀ h₁ hb)
  let eD : Arrow.mk (F.map H') ≅ Arrow.mk (unionConormalFirst i₀' i₁' a' ha') :=
    Arrow.isoMk p'.symm (Iso.refl _) (by
      change p'.inv ≫ unionConormalFirst i₀' i₁' a' ha' = F.map H' ≫ 𝟙 _
      rw [Category.comp_id, unionConormalFirst, unionConormal_comparisonMap_eq_prefix]
      exact Iso.inv_hom_id_assoc p' _)
  exact eA ≪≫ eB ≪≫ eC ≪≫ eD

end HodgeLean.Foundations.Program.G32Native
