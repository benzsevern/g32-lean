import HodgeLean.Foundations.Analytic.AnalytificationChowProjective
import HodgeLean.Ported.Hironaka.Scheme.BlowUp.ClosedImmersionLift

/-! Descend native blow-up projectivity along a closed immersion of bases. -/
noncomputable section
set_option maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- An embedding in a base with projective extended-centre blow-up gives native projectivity. -/
theorem g32l4_blowUp_projective_of_closed_base
    {X Y S : Scheme.{0}} (j : X ⟶ Y) [IsClosedImmersion j]
    (s : X ⟶ S) (t : Y ⟶ S) (hj : j ≫ t = s) (I : X.IdealSheafData)
    [IsProjective ((I.map j).blowUpπ ≫ t)] : IsProjective (I.blowUpπ ≫ s) := by
  let k := Scheme.Hom.pushforwardBlowUp j I
  have hk : k ≫ (I.map j).blowUpπ = I.blowUpπ ≫ j := by
    dsimp only [k, Scheme.Hom.pushforwardBlowUp]
    rw [Category.assoc, blowUpMap_π, ← Category.assoc,
      eqToHom_comp_blowUpπ (comap_map_of_isClosedImmersion j I).symm]
  have hcomp : k ≫ ((I.map j).blowUpπ ≫ t) = I.blowUpπ ≫ s := by
    rw [← Category.assoc, hk, Category.assoc, hj]
  have h := HodgeLean.Foundations.Analytic.AnalytificationChow_isProjective_comp_of_isClosedImmersion
    k ((I.map j).blowUpπ ≫ t)
  rwa [hcomp] at h

end HodgeLean.Foundations.Program
