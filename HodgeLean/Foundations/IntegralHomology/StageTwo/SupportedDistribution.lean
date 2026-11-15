import HodgeLean.Foundations.IntegralHomology.StageTwo.BarycentricPoint

/-! Restricting finite barycentric distributions to their supporting faces.
HC no distance; AV milestone no distance. -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
open Convexity
namespace HodgeLean.Foundations.IntegralHomology.StageTwo

theorem supported_distribution {I E : Type} [DecidableEq I] [DecidableEq E]
    [AddCommGroup E] [Module ℝ E] (v : I → E) (p : StdSimplex ℝ I)
    (s : Finset I) (hp : ∀ a, a ∉ s → p.weights a = 0) :
    ∃ u : StdSimplex ℝ (s.image v),
      u.map (fun a => a.val) = p.map v ∧
      barycentricPoint (fun a : s.image v => a.val) u = barycentricPoint v p := by
  have hps : ∀ a, a ∉ Set.range (fun i : s => i.val) → p.weights a = 0 := by
    intro a ha
    exact hp a (fun h => ha ⟨⟨a, h⟩, rfl⟩)
  obtain ⟨w, hw⟩ := (StdSimplex.mem_range_map_iff (fun i : s => i.val) p).mpr hps
  let f : s → s.image v := fun i => ⟨v i.val, Finset.mem_image.mpr ⟨i.val, i.property, rfl⟩⟩
  let u := w.map f
  have hu : u.map (fun a => a.val) = p.map v := by
    change (w.map f).map (fun a => a.val) = p.map v
    rw [← hw, StdSimplex.map_map, StdSimplex.map_map]
  refine ⟨u, hu, ?_⟩
  have h := congrArg (barycentricPoint (fun a : E => a)) hu
  simpa only [u, barycentricPoint_map] using h

end HodgeLean.Foundations.IntegralHomology.StageTwo
