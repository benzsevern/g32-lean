import HodgeLean.Foundations.AlgebraicGeometry.ConormalIsoComparison

/-! # Invertibility and composition of ideal comparisons
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry

namespace AlgebraicGeometry.Conormal

/-- Two invertible ideal comparisons have an invertible composite comparison. -/
lemma idealPullbackMap_comp_isIso
    {Q₀ Q₁ Q₂ W₀ W₁ W₂ : Scheme.{0}}
    (i₀ : Q₀ ⟶ W₀) (i₁ : Q₁ ⟶ W₁) (i₂ : Q₂ ⟶ W₂)
    (f : W₁ ⟶ W₀) (f' : W₂ ⟶ W₁) (g : Q₁ ⟶ Q₀) (g' : Q₂ ⟶ Q₁)
    (h : g ≫ i₀ = i₁ ≫ f) (h' : g' ≫ i₁ = i₂ ≫ f')
    (h'' : (g' ≫ g) ≫ i₀ = i₂ ≫ (f' ≫ f))
    [IsIso (idealPullbackMap i₀ i₁ f g h)] [IsIso (idealPullbackMap i₁ i₂ f' g' h')] :
    IsIso (idealPullbackMap i₀ i₂ (f' ≫ f) (g' ≫ g) h'') := by
  rw [← idealPullbackMap_comp i₀ i₁ i₂ f f' g g' h h' h'']
  infer_instance

/-- An invertible first comparison and total comparison force the second comparison invertible. -/
lemma idealPullbackMap_isIso_of_comp
    {Q₀ Q₁ Q₂ W₀ W₁ W₂ : Scheme.{0}}
    (i₀ : Q₀ ⟶ W₀) (i₁ : Q₁ ⟶ W₁) (i₂ : Q₂ ⟶ W₂)
    (f : W₁ ⟶ W₀) (f' : W₂ ⟶ W₁) (g : Q₁ ⟶ Q₀) (g' : Q₂ ⟶ Q₁)
    (h : g ≫ i₀ = i₁ ≫ f) (h' : g' ≫ i₁ = i₂ ≫ f')
    (h'' : (g' ≫ g) ≫ i₀ = i₂ ≫ (f' ≫ f))
    [IsIso (idealPullbackMap i₀ i₁ f g h)]
    [IsIso (idealPullbackMap i₀ i₂ (f' ≫ f) (g' ≫ g) h'')] :
    IsIso (idealPullbackMap i₁ i₂ f' g' h') := by
  let a := (Scheme.Modules.pullbackComp f' f).inv.app (idealModule i₀) ≫
    (Scheme.Modules.pullback f').map (idealPullbackMap i₀ i₁ f g h)
  have : IsIso a := by dsimp only [a]; infer_instance
  have : IsIso (a ≫ idealPullbackMap i₁ i₂ f' g' h') := by
    change IsIso (((Scheme.Modules.pullbackComp f' f).inv.app (idealModule i₀) ≫
      (Scheme.Modules.pullback f').map (idealPullbackMap i₀ i₁ f g h)) ≫ _)
    rw [Category.assoc, idealPullbackMap_comp i₀ i₁ i₂ f f' g g' h h' h'']
    infer_instance
  exact IsIso.of_isIso_comp_left a _

/-- Invertibility of the second and total comparisons implies invertibility of the pulled-back first map. -/
lemma idealPullbackMap_map_isIso_of_comp
    {Q₀ Q₁ Q₂ W₀ W₁ W₂ : Scheme.{0}}
    (i₀ : Q₀ ⟶ W₀) (i₁ : Q₁ ⟶ W₁) (i₂ : Q₂ ⟶ W₂)
    (f : W₁ ⟶ W₀) (f' : W₂ ⟶ W₁) (g : Q₁ ⟶ Q₀) (g' : Q₂ ⟶ Q₁)
    (h : g ≫ i₀ = i₁ ≫ f) (h' : g' ≫ i₁ = i₂ ≫ f')
    (h'' : (g' ≫ g) ≫ i₀ = i₂ ≫ (f' ≫ f))
    [IsIso (idealPullbackMap i₁ i₂ f' g' h')]
    [IsIso (idealPullbackMap i₀ i₂ (f' ≫ f) (g' ≫ g) h'')] :
    IsIso ((Scheme.Modules.pullback f').map (idealPullbackMap i₀ i₁ f g h)) := by
  have : IsIso ((Scheme.Modules.pullbackComp f' f).inv.app (idealModule i₀) ≫
      (Scheme.Modules.pullback f').map (idealPullbackMap i₀ i₁ f g h) ≫
      idealPullbackMap i₁ i₂ f' g' h') := by
    rw [idealPullbackMap_comp i₀ i₁ i₂ f f' g g' h h' h'']
    infer_instance
  have : IsIso ((Scheme.Modules.pullback f').map (idealPullbackMap i₀ i₁ f g h) ≫
      idealPullbackMap i₁ i₂ f' g' h') :=
    IsIso.of_isIso_comp_left ((Scheme.Modules.pullbackComp f' f).inv.app (idealModule i₀)) _
  exact IsIso.of_isIso_comp_right
    ((Scheme.Modules.pullback f').map (idealPullbackMap i₀ i₁ f g h))
    (idealPullbackMap i₁ i₂ f' g' h')

end AlgebraicGeometry.Conormal
