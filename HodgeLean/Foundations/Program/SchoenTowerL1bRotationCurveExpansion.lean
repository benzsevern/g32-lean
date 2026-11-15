import HodgeLean.Foundations.Program.SchoenTowerL1bRotationExpansion
import HodgeLean.Foundations.Program.SchoenCycleFixedStalkScalars
import Mathlib.RingTheory.PowerSeries.Basic

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
open HodgeLean.Adapters
open scoped MonoidalCategory
namespace HodgeLean.Foundations.Program

/-- Each actual smooth curve stalk has an injective scalar-preserving expansion
containing the one-variable series parameter. -/
theorem s2v_l1b_rotation_curve_expansion
    (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom]
    [SmoothOfRelativeDimension 1 X.hom] [IsProjective X.hom]
    (p : ComplexPoint X) :
    ∃ ι : X.left.presheaf.stalk p.underlying →+* PowerSeries ℂ,
      Function.Injective ι ∧
      (∃ u, ι u = PowerSeries.X) ∧
      (∀ c : ℂ, ι (HodgeLean.Foundations.Curves.stalkC p.underlying c) = PowerSeries.C c) := by
  let e : g3_power X 1 ≅ X := ρ_ X
  obtain ⟨x, rfl⟩ : ∃ x : ComplexPoint (g3_power X 1), Point.map e.hom x = p := by
    refine ⟨Point.map e.inv p, ?_⟩
    rw [← Point.map_comp_apply, e.inv_hom_id, Point.map_id]
  obtain ⟨ι, hι, hc, hu⟩ := s2v_l1b_rotation_curve_power_expansion X 1 x
  let f := e.hom.left.stalkMap x.underlying
  have hf : Function.Bijective f.hom :=
    (asIso f).commRingCatIsoToRingEquiv.bijective
  let E : MvPowerSeries (Fin 1) ℂ ≃ₐ[ℂ] PowerSeries ℂ :=
    MvPowerSeries.renameEquiv ℂ finOneEquiv
  refine ⟨E.toRingHom.comp (ι.comp f.hom), E.injective.comp (hι.comp hf.1), ?_, ?_⟩
  · obtain ⟨u, hu'⟩ := hf.2 (s2e_curvePowerParameter X 1 x 0)
    refine ⟨u, ?_⟩
    change E (ι (f.hom u)) = PowerSeries.X
    rw [hu', hu]
    exact MvPowerSeries.rename_X finOneEquiv 0
  · intro c
    change E (ι (f.hom (HodgeLean.Foundations.Curves.stalkC _ c))) = PowerSeries.C c
    rw [s2e_stalkMap_complex_scalars (g3_power X 1) X e.hom x.underlying c, hc]
    exact MvPowerSeries.rename_C finOneEquiv c

end HodgeLean.Foundations.Program
