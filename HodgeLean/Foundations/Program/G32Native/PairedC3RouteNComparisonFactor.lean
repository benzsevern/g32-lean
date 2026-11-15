import HodgeLean.Foundations.Program.G32Native.PairedC3RouteNRestrictedComparisonFactor

/-! # Monicity transported through a natural ideal comparison -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program.G32Native
open AlgebraicGeometry.Conormal

/-- An invertible first ideal comparison transports monicity of the second
conormal comparison to the composite square.
Source: Hartshorne, Algebraic Geometry, II.8, functoriality of conormal pullback. -/
lemma paired_conormal_composite_mono
    {Q₀ Q₁ Q₂ W₀ W₁ W₂ : Scheme.{0}}
    (i₀ : Q₀ ⟶ W₀) (i₁ : Q₁ ⟶ W₁) (i₂ : Q₂ ⟶ W₂)
    (f : W₁ ⟶ W₀) (f' : W₂ ⟶ W₁) (g : Q₁ ⟶ Q₀) (g' : Q₂ ⟶ Q₁)
    (h : g ≫ i₀ = i₁ ≫ f) (h' : g' ≫ i₁ = i₂ ≫ f')
    (h'' : (g' ≫ g) ≫ i₀ = i₂ ≫ (f' ≫ f))
    [IsIso (idealPullbackMap i₀ i₁ f g h)]
    [Mono (comparisonMap i₁ i₂ f' g' h')] :
    Mono (comparisonMap i₀ i₂ (f' ≫ f) (g' ≫ g) h'') := by
  haveI : IsIso ((Scheme.Modules.pullback i₂).map
      ((Scheme.Modules.pullback f').map (idealPullbackMap i₀ i₁ f g h))) := inferInstance
  exact paired_conormal_composite_mono_on_source i₀ i₁ i₂ f f' g g' h h' h''

#print axioms paired_conormal_composite_mono
end HodgeLean.Foundations.Program.G32Native
