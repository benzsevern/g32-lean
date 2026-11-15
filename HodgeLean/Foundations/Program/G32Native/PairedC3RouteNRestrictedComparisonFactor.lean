import HodgeLean.Foundations.AlgebraicGeometry.ConormalComparisonComposition
import HodgeLean.Foundations.Program.G32Native.UnionConormalAffineComparison

/-! # Monicity transported through a comparison restricted to the retained source -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program.G32Native
open AlgebraicGeometry.Conormal

/-- Invertibility of the first ideal comparison only after restriction to
the retained source suffices for monicity of the composite conormal map.
Source: Hartshorne, Algebraic Geometry, II.8, functoriality of conormal pullback. -/
lemma paired_conormal_composite_mono_on_source
    {Q₀ Q₁ Q₂ W₀ W₁ W₂ : Scheme.{0}}
    (i₀ : Q₀ ⟶ W₀) (i₁ : Q₁ ⟶ W₁) (i₂ : Q₂ ⟶ W₂)
    (f : W₁ ⟶ W₀) (f' : W₂ ⟶ W₁) (g : Q₁ ⟶ Q₀) (g' : Q₂ ⟶ Q₁)
    (h : g ≫ i₀ = i₁ ≫ f) (h' : g' ≫ i₁ = i₂ ≫ f')
    (h'' : (g' ≫ g) ≫ i₀ = i₂ ≫ (f' ≫ f))
    [IsIso ((Scheme.Modules.pullback i₂).map
      ((Scheme.Modules.pullback f').map (idealPullbackMap i₀ i₁ f g h)))]
    [Mono (comparisonMap i₁ i₂ f' g' h')] :
    Mono (comparisonMap i₀ i₂ (f' ≫ f) (g' ≫ g) h'') := by
  have hm : Mono ((unionConormalComparisonPrefixIso i₁ i₂ f' g' h').hom ≫
      (Scheme.Modules.pullback i₂).map (idealPullbackMap i₁ i₂ f' g' h')) := by
    rw [← unionConormal_comparisonMap_eq_prefix]
    infer_instance
  haveI : Mono ((Scheme.Modules.pullback i₂).map (idealPullbackMap i₁ i₂ f' g' h')) :=
    (mono_comp_iff_of_isIso _ _).mp hm
  rw [unionConormal_comparisonMap_eq_prefix]
  rw [← idealPullbackMap_comp i₀ i₁ i₂ f f' g g' h h' h'']
  simp only [Functor.map_comp]
  infer_instance

#print axioms paired_conormal_composite_mono_on_source
end HodgeLean.Foundations.Program.G32Native
