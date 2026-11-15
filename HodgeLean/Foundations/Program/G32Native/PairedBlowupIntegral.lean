import HodgeLean.Foundations.Program.G32Native.BlowupIntegral
import HodgeLean.Foundations.Program.G32Native.ConormalNonzeroIdeal
import HodgeLean.Ported.Hironaka.Scheme.IdealSheaf.Order.Semicontinuity

/-! Integrality of the paired blow-up from its branch conormal frame. -/
noncomputable section
set_option maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- One branch's rank-one conormal frames suffice for integrality of the paired blow-up. -/
theorem g32l4_paired_blowup_integral
    (B : Over (Spec ↧ℂ)) [Smooth B.hom] [IsIntegral B.left]
    (D E : B.left.IdealSheafData)
    (hframe : ∀ x : (s2c_subscheme B D).left,
      ∃ U : (s2c_subscheme B D).left.Opens, x ∈ U ∧
        Nonempty (Scheme.Modules.restrict
          (s2c_conormal (s2c_subschemeι B D).left) U.ι ≅
          (SheafOfModules.free (R := U.toScheme.ringCatSheaf) (Fin 1) :
            U.toScheme.Modules))) : IsIntegral (D ⊔ E).blowUp := by
  have hD := g32l4_nonzero_of_positive_conormal_rank B D 1 (by omega) hframe
  have hDE : D ⊔ E ≠ ⊥ := by
    intro h
    exact hD (le_bot_iff.mp (le_sup_left.trans h.le))
  letI : IsLocallyNoetherian B.left := B.hom.isLocallyNoetherian_of_field
  exact g32l4_blowUp_isIntegral (D ⊔ E) hDE

end HodgeLean.Foundations.Program
