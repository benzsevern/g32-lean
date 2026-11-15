import Mathlib.Algebra.Group.Basic
import Mathlib.Data.Set.Function
import Mathlib.Tactic.Abel

noncomputable section
namespace HodgeLean.Foundations.Program

variable {V P : Type*} [AddCommGroup V]
    (p : V → P) (hs : Function.Surjective p)
    (hrel : ∀ a z w, p z = p w → p (z + a) = p (w + a))

def b54_pointTranslation (a : V) (x : P) : P := p ((hs x).choose + a)

include hrel in
theorem b54_pointTranslation_param (a z : V) :
    b54_pointTranslation p hs a (p z) = p (z + a) :=
  hrel a _ _ (hs (p z)).choose_spec

def b54_pointTranslationEquiv (a : V) : P ≃ P where
  toFun := b54_pointTranslation p hs a
  invFun := b54_pointTranslation p hs (-a)
  left_inv x := by
    obtain ⟨z, rfl⟩ := hs x
    rw [b54_pointTranslation_param p hs hrel, b54_pointTranslation_param p hs hrel]
    simp
  right_inv x := by
    obtain ⟨z, rfl⟩ := hs x
    rw [b54_pointTranslation_param p hs hrel, b54_pointTranslation_param p hs hrel]
    simp

theorem b54_pointTranslationEquiv_param (a z : V) :
    b54_pointTranslationEquiv p hs hrel a (p z) = p (z + a) :=
  b54_pointTranslation_param p hs hrel a z

theorem b54_pointTranslationEquiv_symm_param (a z : V) :
    (b54_pointTranslationEquiv p hs hrel a).symm (p z) = p (z + -a) :=
  b54_pointTranslation_param p hs hrel (-a) z

theorem b54_pointTranslation_transitive (x y : P) :
    ∃ a, b54_pointTranslationEquiv p hs hrel a x = y := by
  obtain ⟨z, rfl⟩ := hs x
  obtain ⟨w, rfl⟩ := hs y
  refine ⟨w - z, ?_⟩
  rw [b54_pointTranslationEquiv_param]
  congr 1
  abel

end HodgeLean.Foundations.Program
