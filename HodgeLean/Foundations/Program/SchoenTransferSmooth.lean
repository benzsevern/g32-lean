import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.CategoryTheory.Comma.Over.Basic

/-! Smooth ambient opens for the unramified support construction. -/
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

theorem s4_smooth_of_etale_over {B W T : Scheme} (b : B ⟶ T) (w : W ⟶ T)
    (β : W ⟶ B) [Smooth b] [Etale β] (hβ : β ≫ b = w) : Smooth w := by
  rw [← hβ]
  infer_instance

theorem s4_smooth_open_at {W T : Scheme} (w : W ⟶ T) [Smooth w] (x : W) :
    ∃ U : W.Opens, x ∈ U ∧ Smooth (U.ι ≫ w) :=
  ⟨⊤, trivial, inferInstance⟩

end HodgeLean.Foundations.Program
