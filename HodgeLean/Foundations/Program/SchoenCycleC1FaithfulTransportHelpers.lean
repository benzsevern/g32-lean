import HodgeLean.Foundations.Program.SchoenCycleC1DeckHelpers

/-! # Transport of faithful powers through a dominant equivariant map -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- Faithful powers on the target remain faithful on a dominant equivariant
source over the complex base. -/
theorem s2e_c1_faithful_powers_of_dominant_equivariant
    {X Y : Over (Spec ↧ℂ)} [IsReduced Y.left] [IsSeparated Y.hom]
    (w : X ⟶ Y) [IsDominant w.left] (dX : X ⟶ X) (dY : Y ⟶ Y)
    (hd : dX ≫ w = w ≫ dY) (m : ℕ)
    (hfaith : ∀ n, n < m → End.of dY ^ n = 1 → n = 0) :
    ∀ n, n < m → End.of dX ^ n = 1 → n = 0 := by
  intro n hn hpow
  have hc := s2e_c1_equivariant_generator_power w dX dY hd n
  rw [hpow] at hc
  have he : w ≫ (End.of dY ^ n).asHom = w := hc.symm.trans (Category.id_comp w)
  have hy : (End.of dY ^ n).asHom = 𝟙 Y := by
    apply Over.OverMorphism.ext
    apply ext_of_isDominant_of_isSeparated Y.hom
      ((Over.w (End.of dY ^ n).asHom).trans (Over.w (𝟙 Y)).symm) w.left
    exact congrArg Over.Hom.left (he.trans (Category.comp_id w).symm)
  exact hfaith n hn (End.ext hy)

end HodgeLean.Foundations.Program
