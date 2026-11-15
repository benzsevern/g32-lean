import HodgeLean.Foundations.Program.G32Native.PairedC3RouteNRestrictedComparisonFactor
import Mathlib.CategoryTheory.Limits.Shapes.Kernels

/-! # The natural cokernel under a source-restricted ideal comparison -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace HodgeLean.Foundations.Program.G32Native
open AlgebraicGeometry.Conormal

/-- An ideal comparison invertible after restriction to the retained source
identifies the cokernel of the composite natural conormal map with that
of the second comparison. The codomain map is the identity.
Source: Hartshorne, Algebraic Geometry, II.8, conormal functoriality. -/
def pairedConormalCompositeCokernelIso
    {Q₀ Q₁ Q₂ W₀ W₁ W₂ : Scheme.{0}}
    (i₀ : Q₀ ⟶ W₀) (i₁ : Q₁ ⟶ W₁) (i₂ : Q₂ ⟶ W₂)
    (f : W₁ ⟶ W₀) (f' : W₂ ⟶ W₁) (g : Q₁ ⟶ Q₀) (g' : Q₂ ⟶ Q₁)
    (h : g ≫ i₀ = i₁ ≫ f) (h' : g' ≫ i₁ = i₂ ≫ f')
    (h'' : (g' ≫ g) ≫ i₀ = i₂ ≫ (f' ≫ f))
    [IsIso ((Scheme.Modules.pullback i₂).map
      ((Scheme.Modules.pullback f').map (idealPullbackMap i₀ i₁ f g h)))] :
    cokernel (comparisonMap i₀ i₂ (f' ≫ f) (g' ≫ g) h'') ≅
      cokernel (comparisonMap i₁ i₂ f' g' h') := by
  let e₀ := unionConormalComparisonPrefixIso i₀ i₂ (f' ≫ f) (g' ≫ g) h''
  let e₁ := unionConormalComparisonPrefixIso i₁ i₂ f' g' h'
  let e₂ := (Scheme.Modules.pullback i₂).mapIso
    ((Scheme.Modules.pullbackComp f' f).symm.app (idealModule i₀))
  let e₃ := asIso ((Scheme.Modules.pullback i₂).map
    ((Scheme.Modules.pullback f').map (idealPullbackMap i₀ i₁ f g h)))
  let e := e₀ ≪≫ e₂ ≪≫ e₃ ≪≫ e₁.symm
  apply cokernel.mapIso _ _ e (Iso.refl _)
  simp only [Iso.refl_hom, Category.comp_id]
  rw [unionConormal_comparisonMap_eq_prefix,
    unionConormal_comparisonMap_eq_prefix]
  change e₀.hom ≫ (Scheme.Modules.pullback i₂).map
      (idealPullbackMap i₀ i₂ (f' ≫ f) (g' ≫ g) h'') =
    (e₀.hom ≫ e₂.hom ≫ e₃.hom ≫ e₁.inv) ≫
      (e₁.hom ≫ (Scheme.Modules.pullback i₂).map (idealPullbackMap i₁ i₂ f' g' h'))
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  change e₀.hom ≫ (Scheme.Modules.pullback i₂).map
      (idealPullbackMap i₀ i₂ (f' ≫ f) (g' ≫ g) h'') =
    e₀.hom ≫ (Scheme.Modules.pullback i₂).map
        ((Scheme.Modules.pullbackComp f' f).inv.app (idealModule i₀)) ≫
      (Scheme.Modules.pullback i₂).map
        ((Scheme.Modules.pullback f').map (idealPullbackMap i₀ i₁ f g h)) ≫
      (Scheme.Modules.pullback i₂).map (idealPullbackMap i₁ i₂ f' g' h')
  simp only [← Functor.map_comp]
  rw [idealPullbackMap_comp i₀ i₁ i₂ f f' g g' h h' h'']

#print axioms pairedConormalCompositeCokernelIso
end HodgeLean.Foundations.Program.G32Native
