import Mathlib.Analysis.Normed.Operator.Prod

/-! Invertibility of an actual tangential change retaining all normal coordinates. -/
noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
namespace HodgeLean.Foundations.Program

/-- A tangential derivative that is invertible along the zero-normal plane
makes the full derivative invertible when the normal coordinates are retained. -/
theorem s4_q3_triangular_derivative_bijective
    {𝕜 E F : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedAddCommGroup F]
    [NormedSpace 𝕜 E] [NormedSpace 𝕜 F]
    (L : (E × F) →L[𝕜] E)
    (h : Function.Bijective (L.comp (ContinuousLinearMap.inl 𝕜 E F))) :
    Function.Bijective (L.prod (ContinuousLinearMap.snd 𝕜 E F)) := by
  have hsum (z : E × F) : L z = L (z.1, 0) + L (0, z.2) := by
    simpa only [Prod.mk_add_mk, add_zero, zero_add] using map_add L (z.1, 0) (0, z.2)
  constructor
  · intro u v huv
    change (L u, u.2) = (L v, v.2) at huv
    have hv := congrArg (fun z : E × F => z.2) huv
    have hu := congrArg (fun z : E × F => z.1) huv
    change u.2 = v.2 at hv
    change L u = L v at hu
    apply Prod.ext ?_ hv
    apply h.1
    change L (u.1, 0) = L (v.1, 0)
    rw [hsum u, hsum v, hv] at hu
    exact add_right_cancel hu
  · rintro ⟨u, v⟩
    obtain ⟨w, hw⟩ := h.2 (u - L (0, v))
    change L (w, 0) = u - L (0, v) at hw
    refine ⟨(w, v), Prod.ext ?_ rfl⟩
    change L (w, v) = u
    rw [hsum, hw, sub_add_cancel]

end HodgeLean.Foundations.Program
