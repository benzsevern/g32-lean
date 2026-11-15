import HodgeLean.Foundations.Program.SchoenTowerGeometryDefs
import HodgeLean.Ported.Hironaka.Scheme.BlowUpSequence.RestrictDivisors

/-! Smoothness of the actual paired blow-up from smooth branch intersections. -/
noncomputable section
set_option maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- The native blow-up of a pair is smooth when all branch intersections are smooth. -/
theorem g32l4_paired_blowup_smooth
    {ι : Type} [DecidableEq ι] (B : Over (Spec ↧ℂ)) [Smooth B.hom]
    (D : ι → B.left.IdealSheafData) (u v : ι)
    (h : ∀ J : Finset ι, Smooth (s2c_subscheme B (J.sup D)).hom) :
    Smooth ((D u ⊔ D v).blowUpπ ≫ B.hom) := by
  have hK := h {u, v}
  rw [Finset.sup_insert, Finset.sup_singleton] at hK
  letI : Smooth ((D u ⊔ D v).subschemeι ≫ B.hom) := hK
  exact smooth_blowUpπ_comp_of_smooth' B.hom (D u ⊔ D v)

end HodgeLean.Foundations.Program
