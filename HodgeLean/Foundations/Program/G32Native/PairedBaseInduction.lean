import HodgeLean.Foundations.Program.SchoenTowerConormalDefs
import HodgeLean.Foundations.Program.SchoenTowerL1bBlowupComparison

/-! Retained paired bases: induction and comparison over the fixed base. -/
noncomputable section
set_option maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- Induct on smoothness, projectivity and integrality in the retained finite family. -/
theorem g32t6_base_induction {r : ℕ}
    (B : Fin (r + 1) → Over (Spec ↧ℂ))
    (hzero : Smooth (B 0).hom ∧ IsProjective (B 0).hom ∧ IsIntegral (B 0).left)
    (hsmooth : ∀ i : Fin r, Smooth (B i.castSucc).hom → Smooth (B i.succ).hom)
    (hprojective : ∀ i : Fin r, IsProjective (B i.castSucc).hom →
      IsProjective (B i.succ).hom)
    (hintegral : ∀ i : Fin r, IsIntegral (B i.castSucc).left → IsIntegral (B i.succ).left) :
    ∀ i, Smooth (B i).hom ∧ IsProjective (B i).hom ∧ IsIntegral (B i).left := by
  intro i
  induction i using Fin.induction with
  | zero => exact hzero
  | succ i ih =>
    exact ⟨hsmooth i ih.1, hprojective i ih.2.1, hintegral i ih.2.2⟩

#print axioms g32t6_base_induction
end HodgeLean.Foundations.Program
