import Mathlib.CategoryTheory.EpiMono

noncomputable section
set_option maxHeartbeats 400000
open CategoryTheory
namespace HodgeLean.Foundations.Program

/-- An actual categorical quotient for invariant morphisms is an epimorphism in its retained category. -/
theorem s2_invariantQuotient_epi {C : Type*} [Category C] {X W : C} {I : Type*}
    (a : I → (X ⟶ X)) (q : X ⟶ W) (hqinv : ∀ i, a i ≫ q = q)
    (hq : ∀ (T : C) (f : X ⟶ T), (∀ i, a i ≫ f = f) → ∃! d : W ⟶ T, q ≫ d = f) :
    Epi q := by
  constructor
  intro T f g hfg
  have hinv : ∀ i, a i ≫ (q ≫ f) = q ≫ f := by
    intro i
    rw [← Category.assoc, hqinv i]
  obtain ⟨u, _, hu⟩ := hq T (q ≫ f) hinv
  exact (hu f rfl).trans (hu g hfg.symm).symm

end HodgeLean.Foundations.Program
