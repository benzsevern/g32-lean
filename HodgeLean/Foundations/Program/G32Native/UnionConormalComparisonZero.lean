import HodgeLean.Foundations.Program.G32Native.UnionConormalFactorZero
import HodgeLean.Foundations.Program.G32Native.UnionConormalSquarePullback
import HodgeLean.Foundations.AlgebraicGeometry.ConormalComparisonComposition

/-! # Zero composites of natural conormal comparisons -/
noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace HodgeLean.Foundations.Program.G32Native
open AlgebraicGeometry.Conormal

/-- Two ideal comparisons compose to zero if their ambient composite factors
through the original closed subscheme. -/
lemma unionConormal_idealPullbackMap_comp_zero
    {Q₀ Q₁ Q₂ W₀ W₁ W₂ : Scheme.{0}}
    (i₀ : Q₀ ⟶ W₀) (i₁ : Q₁ ⟶ W₁) (i₂ : Q₂ ⟶ W₂)
    (f : W₁ ⟶ W₀) (f' : W₂ ⟶ W₁) (g : Q₁ ⟶ Q₀) (g' : Q₂ ⟶ Q₁)
    (h : g ≫ i₀ = i₁ ≫ f) (h' : g' ≫ i₁ = i₂ ≫ f')
    (b : W₂ ⟶ Q₀) (hb : f' ≫ f = b ≫ i₀) :
    (Scheme.Modules.pullback f').map (idealPullbackMap i₀ i₁ f g h) ≫
      idealPullbackMap i₁ i₂ f' g' h' = 0 := by
  have hc : (g' ≫ g) ≫ i₀ = i₂ ≫ (f' ≫ f) := by
    rw [Category.assoc, h, ← Category.assoc, h', Category.assoc]
  have hz : idealPullbackMap i₀ i₂ (f' ≫ f) (g' ≫ g) hc = 0 := by
    exact unionConormal_idealPullbackMap_factor_zero_of_eq i₀ i₂
      (f' ≫ f) (g' ≫ g) hc b hb
  apply (cancel_epi ((Scheme.Modules.pullbackComp f' f).inv.app (idealModule i₀))).mp
  rw [comp_zero, idealPullbackMap_comp i₀ i₁ i₂ f f' g g' h h' hc, hz]

/-- The conormal comparisons inherit the vanishing ideal composite. -/
lemma unionConormal_comparisonMap_comp_zero
    {Q₀ Q₁ Q₂ W₀ W₁ W₂ : Scheme.{0}}
    (i₀ : Q₀ ⟶ W₀) (i₁ : Q₁ ⟶ W₁) (i₂ : Q₂ ⟶ W₂)
    (f : W₁ ⟶ W₀) (f' : W₂ ⟶ W₁) (g : Q₁ ⟶ Q₀) (g' : Q₂ ⟶ Q₁)
    (h : g ≫ i₀ = i₁ ≫ f) (h' : g' ≫ i₁ = i₂ ≫ f')
    (b : W₂ ⟶ Q₀) (hb : f' ≫ f = b ≫ i₀) :
    (Scheme.Modules.pullback g').map (comparisonMap i₀ i₁ f g h) ≫
      comparisonMap i₁ i₂ f' g' h' = 0 := by
  have hz := unionConormal_idealPullbackMap_comp_zero i₀ i₁ i₂ f f' g g' h h' b hb
  have hn := (unionConormalSquarePullbackIso i₁ i₂ f' g' h').hom.naturality
    (idealPullbackMap i₀ i₁ f g h)
  simp only [Functor.comp_map] at hn
  rw [unionConormal_comparisonMap_eq_prefix i₀ i₁ f g h,
    unionConormal_comparisonMap_eq_prefix i₁ i₂ f' g' h',
    ← unionConormalSquarePullbackIso_ideal_hom i₁ i₂ f' g' h', Functor.map_comp]
  simp only [Category.assoc]
  rw [reassoc_of% hn, ← Functor.map_comp, hz, Functor.map_zero]
  simp only [comp_zero]

end HodgeLean.Foundations.Program.G32Native
