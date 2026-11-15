import HodgeLean.Foundations.AnalyticGermRemmertStein

/-! # Continuous extension across analytic hypersurfaces

Route: continuity bounds the function on a small neighborhood. Apply bounded
analytic extension there; uniqueness identifies the extension with the
original continuous function.
-/
noncomputable section
namespace HodgeLean.Adapters
open Set Filter Topology
open HodgeLean.Foundations

/-- A continuous function analytic off a nowhere locally zero analytic
hypersurface is analytic throughout its open domain. -/
theorem a3b4a_classAnalytic_extend_continuous
    (d : ℕ) (V : Set (Fin (d+1) → ℂ)) (hV : IsOpen V)
    (δ f : (Fin (d+1) → ℂ) → ℂ) (hδ : AnalyticOnNhd ℂ δ V)
    (hnz : ∀ x ∈ V, ¬ (δ =ᶠ[𝓝 x] fun _ => 0))
    (hf : AnalyticOnNhd ℂ f (V \ {x | δ x = 0})) (hcont : ContinuousOn f V) :
    AnalyticOnNhd ℂ f V := by
  intro x hx
  have hc : ContinuousAt f x := (hcont x hx).continuousAt (hV.mem_nhds hx)
  have hb : ∀ᶠ y in 𝓝 x, ‖f y‖ < ‖f x‖ + 1 :=
    hc.norm.eventually (gt_mem_nhds (by linarith : ‖f x‖ < ‖f x‖ + 1))
  obtain ⟨W, hWsub, hWo, hxW⟩ := mem_nhds_iff.mp (inter_mem (hV.mem_nhds hx) hb)
  have hWV : W ⊆ V := fun y hy => (hWsub hy).1
  obtain ⟨F, hF, hFf, hFb, huniq⟩ := adim8_hypersurface_extension d W hWo δ f
    (hδ.mono hWV) (fun y hy => hnz y (hWV hy))
    (hf.mono (fun y hy => ⟨hWV hy.1, hy.2⟩)) (‖f x‖ + 1)
    (fun y hy => (hWsub hy.1).2.le)
  have hEq : EqOn f F W := huniq f (hcont.mono hWV) (fun _ _ => rfl)
  apply (hF x hxW).congr
  filter_upwards [hWo.mem_nhds hxW] with y hy
  exact (hEq hy).symm

end HodgeLean.Adapters
