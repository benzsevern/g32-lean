import HodgeLean.Foundations.AlgebraicGeometry.ConormalComparisonCompositionIso

/-! # Transport from supplied chart comparisons to the original square -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program.G32Native
open AlgebraicGeometry.Conormal

/-- Invertible chart restriction comparisons identify an invertible local
comparison with the restriction of the original natural ideal map.
Only the ambient faces of the cube need to be specified: the ideal map
is independent of the chosen morphisms between the immersed schemes.
Source: Hartshorne, Algebraic Geometry, II.8, naturality of ideal pullback. -/
lemma paired_conormal_chart_ideal_map_isIso
    {Q₀ Q₁ Q₀' Q₁' W₀ W₁ W₀' W₁' : Scheme.{0}}
    (i₀ : Q₀ ⟶ W₀) (i₁ : Q₁ ⟶ W₁)
    (i₀' : Q₀' ⟶ W₀') (i₁' : Q₁' ⟶ W₁')
    (f : W₁ ⟶ W₀) (g : Q₁ ⟶ Q₀) (h : g ≫ i₀ = i₁ ≫ f)
    (f' : W₁' ⟶ W₀') (g' : Q₁' ⟶ Q₀') (h' : g' ≫ i₀' = i₁' ≫ f')
    (u₀ : W₀' ⟶ W₀) (u₁ : W₁' ⟶ W₁)
    (v₀ : Q₀' ⟶ Q₀) (v₁ : Q₁' ⟶ Q₁)
    (h₀ : v₀ ≫ i₀ = i₀' ≫ u₀) (h₁ : v₁ ≫ i₁ = i₁' ≫ u₁)
    (hf : f' ≫ u₀ = u₁ ≫ f)
    [IsIso (idealPullbackMap i₀ i₀' u₀ v₀ h₀)]
    [IsIso (idealPullbackMap i₁ i₁' u₁ v₁ h₁)]
    [IsIso (idealPullbackMap i₀' i₁' f' g' h')] :
    IsIso ((Scheme.Modules.pullback u₁).map (idealPullbackMap i₀ i₁ f g h)) := by
  have hA : (g' ≫ v₀) ≫ i₀ = i₁' ≫ (f' ≫ u₀) := by
    rw [Category.assoc, h₀, ← Category.assoc, h', Category.assoc]
  have hB : (v₁ ≫ g) ≫ i₀ = i₁' ≫ (u₁ ≫ f) := by
    rw [Category.assoc, h, ← Category.assoc, h₁, Category.assoc]
  haveI := idealPullbackMap_comp_isIso i₀ i₀' i₁' u₀ f' v₀ g' h₀ h' hA
  haveI : IsIso (idealPullbackMap i₀ i₁' (u₁ ≫ f) (v₁ ≫ g) hB) :=
    (idealPullbackMap_isIso_congr i₀ i₁' _ _ hf _ _ hA hB).mp inferInstance
  exact idealPullbackMap_map_isIso_of_comp i₀ i₁ i₁' f u₁ g v₁ h h₁ hB

#print axioms paired_conormal_chart_ideal_map_isIso
end HodgeLean.Foundations.Program.G32Native
