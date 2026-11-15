import Mathlib.CategoryTheory.Iso

noncomputable section
set_option maxHeartbeats 400000
open CategoryTheory
namespace HodgeLean.Foundations.Program

/-- Two actual categorical quotients for the same invariant morphisms are canonically isomorphic under their source. -/
theorem s2_invariantQuotient_iso {C : Type*} [Category C] {X W Z : C} {I : Type*}
    (a : I → (X ⟶ X)) (q : X ⟶ W) (p : X ⟶ Z)
    (hqinv : ∀ i, a i ≫ q = q)
    (hq : ∀ (T : C) (f : X ⟶ T), (∀ i, a i ≫ f = f) → ∃! d : W ⟶ T, q ≫ d = f)
    (hpinv : ∀ i, a i ≫ p = p)
    (hp : ∀ (T : C) (f : X ⟶ T), (∀ i, a i ≫ f = f) → ∃! d : Z ⟶ T, p ≫ d = f) :
    ∃ e : Z ≅ W, p ≫ e.hom = q := by
  obtain ⟨f, hf, _⟩ := hq Z p hpinv
  obtain ⟨g, hg, _⟩ := hp W q hqinv
  have hfg : f ≫ g = 𝟙 W := by
    obtain ⟨u, _, hu⟩ := hq W q hqinv
    apply (hu (f ≫ g) ?_).trans (hu (𝟙 W) ?_).symm
    · rw [← Category.assoc, hf, hg]
    · exact Category.comp_id q
  have hgf : g ≫ f = 𝟙 Z := by
    obtain ⟨u, _, hu⟩ := hp Z p hpinv
    apply (hu (g ≫ f) ?_).trans (hu (𝟙 Z) ?_).symm
    · rw [← Category.assoc, hg, hf]
    · exact Category.comp_id p
  exact ⟨⟨g, f, hgf, hfg⟩, hg⟩

end HodgeLean.Foundations.Program
