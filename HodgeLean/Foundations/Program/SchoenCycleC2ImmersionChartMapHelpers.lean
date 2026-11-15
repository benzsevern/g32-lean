import HodgeLean.Foundations.Program.SchoenCycleC2SmoothImmersionChartsHelpers

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry Opposite
namespace HodgeLean.Foundations.Program

/-- The canonical two affine-chart isomorphisms identify the actual
restricted immersion with the spectrum of its actual section map. -/
theorem s2e_closedImmersion_affine_chart_map
    {Q W : Scheme.{0}} (ι : Q ⟶ W) [IsClosedImmersion ι]
    (V : W.Opens) (hV : IsAffineOpen V) :
    let hP := hV.preimage ι
    hP.isoSpec.inv ≫ (ι ∣_ V) ≫ hV.isoSpec.hom = Spec.map (ι.app V) := by
  let hP := hV.preimage ι
  apply (cancel_mono hV.fromSpec).mp
  rw [Category.assoc, Category.assoc, hV.isoSpec_hom_fromSpec, morphismRestrict_ι]
  have h := hV.SpecMap_appLE_fromSpec ι hP le_rfl
  have happ : ι.appLE V (ι ⁻¹ᵁ V) le_rfl = ι.app V := by
    simp only [Scheme.Hom.appLE, homOfLE_refl, op_id]
    rw [Q.presheaf.map_id, Category.comp_id]
  rw [happ] at h
  simpa only [IsAffineOpen.fromSpec, Category.assoc] using h.symm

end HodgeLean.Foundations.Program
