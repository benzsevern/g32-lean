import HodgeLean.Foundations.AlgebraicGeometry.ConormalComparisonCompositionIso

/-! # Epimorphy and composition of natural ideal comparisons -/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program.G32Native
open AlgebraicGeometry.Conormal

/-- Composing two epic ideal comparisons gives an epic total comparison. -/
lemma unionConormal_idealMap_comp_epi
    {Q₀ Q₁ Q₂ W₀ W₁ W₂ : Scheme.{0}}
    (i₀ : Q₀ ⟶ W₀) (i₁ : Q₁ ⟶ W₁) (i₂ : Q₂ ⟶ W₂)
    (f : W₁ ⟶ W₀) (f' : W₂ ⟶ W₁) (g : Q₁ ⟶ Q₀) (g' : Q₂ ⟶ Q₁)
    (h : g ≫ i₀ = i₁ ≫ f) (h' : g' ≫ i₁ = i₂ ≫ f')
    (h'' : (g' ≫ g) ≫ i₀ = i₂ ≫ (f' ≫ f))
    [Epi (idealPullbackMap i₀ i₁ f g h)] [Epi (idealPullbackMap i₁ i₂ f' g' h')] :
    Epi (idealPullbackMap i₀ i₂ (f' ≫ f) (g' ≫ g) h'') := by
  rw [← idealPullbackMap_comp i₀ i₁ i₂ f f' g g' h h' h'']
  infer_instance

/-- Epimorphy of a total ideal comparison implies epimorphy of its second factor. -/
lemma unionConormal_idealMap_epi_of_comp
    {Q₀ Q₁ Q₂ W₀ W₁ W₂ : Scheme.{0}}
    (i₀ : Q₀ ⟶ W₀) (i₁ : Q₁ ⟶ W₁) (i₂ : Q₂ ⟶ W₂)
    (f : W₁ ⟶ W₀) (f' : W₂ ⟶ W₁) (g : Q₁ ⟶ Q₀) (g' : Q₂ ⟶ Q₁)
    (h : g ≫ i₀ = i₁ ≫ f) (h' : g' ≫ i₁ = i₂ ≫ f')
    (h'' : (g' ≫ g) ≫ i₀ = i₂ ≫ (f' ≫ f))
    [Epi (idealPullbackMap i₀ i₂ (f' ≫ f) (g' ≫ g) h'')] :
    Epi (idealPullbackMap i₁ i₂ f' g' h') := by
  have ht : Epi (((Scheme.Modules.pullbackComp f' f).inv.app (idealModule i₀) ≫
      (Scheme.Modules.pullback f').map (idealPullbackMap i₀ i₁ f g h)) ≫
      idealPullbackMap i₁ i₂ f' g' h') := by
    rw [Category.assoc, idealPullbackMap_comp i₀ i₁ i₂ f f' g g' h h' h'']
    infer_instance
  exact epi_of_epi
    ((Scheme.Modules.pullbackComp f' f).inv.app (idealModule i₀) ≫
      (Scheme.Modules.pullback f').map (idealPullbackMap i₀ i₁ f g h)) _

/-- An invertible second comparison permits cancellation from an epic total comparison. -/
lemma unionConormal_idealMap_map_epi_of_comp
    {Q₀ Q₁ Q₂ W₀ W₁ W₂ : Scheme.{0}}
    (i₀ : Q₀ ⟶ W₀) (i₁ : Q₁ ⟶ W₁) (i₂ : Q₂ ⟶ W₂)
    (f : W₁ ⟶ W₀) (f' : W₂ ⟶ W₁) (g : Q₁ ⟶ Q₀) (g' : Q₂ ⟶ Q₁)
    (h : g ≫ i₀ = i₁ ≫ f) (h' : g' ≫ i₁ = i₂ ≫ f')
    (h'' : (g' ≫ g) ≫ i₀ = i₂ ≫ (f' ≫ f))
    [IsIso (idealPullbackMap i₁ i₂ f' g' h')]
    [Epi (idealPullbackMap i₀ i₂ (f' ≫ f) (g' ≫ g) h'')] :
    Epi ((Scheme.Modules.pullback f').map (idealPullbackMap i₀ i₁ f g h)) := by
  have ht : Epi ((Scheme.Modules.pullbackComp f' f).inv.app (idealModule i₀) ≫
      (Scheme.Modules.pullback f').map (idealPullbackMap i₀ i₁ f g h) ≫
      idealPullbackMap i₁ i₂ f' g' h') := by
    rw [idealPullbackMap_comp i₀ i₁ i₂ f f' g g' h h' h'']
    infer_instance
  have ht' : Epi ((Scheme.Modules.pullback f').map (idealPullbackMap i₀ i₁ f g h) ≫
      idealPullbackMap i₁ i₂ f' g' h') :=
    epi_of_epi ((Scheme.Modules.pullbackComp f' f).inv.app (idealModule i₀)) _
  exact (epi_comp_iff_of_isIso _ _).mp ht'

/-- Equality of ambient maps retains epimorphy of natural ideal comparisons. -/
lemma unionConormal_idealMap_epi_congr
    {Q Q' W W' : Scheme.{0}} (i : Q ⟶ W) (i' : Q' ⟶ W')
    (f f' : W' ⟶ W) (hf : f = f') (g g' : Q' ⟶ Q)
    (h : g ≫ i = i' ≫ f) (h' : g' ≫ i = i' ≫ f')
    [Epi (idealPullbackMap i i' f g h)] : Epi (idealPullbackMap i i' f' g' h') := by
  subst f'
  rw [← idealPullbackMap_eq_of_ambient i i' f g g' h h']
  infer_instance

end HodgeLean.Foundations.Program.G32Native
