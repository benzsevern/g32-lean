import HodgeLean.Foundations.Program.SchoenTransferQ3TriangularDerivative
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Analytic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-! Analytic changes of the tangential coordinates retaining the exact normal coordinates. -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
namespace HodgeLean.Foundations.Program

/-- An analytic tangential change invertible on the zero-normal plane is
an analytic coordinate change preserving every original normal coordinate. -/
theorem s4_q3_analytic_tangential_change_preserving_normals
    {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]
    [NormedSpace ℂ E] [NormedSpace ℂ F]
    [FiniteDimensional ℂ E] [FiniteDimensional ℂ F]
    (G : E × F → E) (a : E) (hG : AnalyticAt ℂ G (a, 0))
    (hbij : Function.Bijective (fderiv ℂ (fun u => G (u, 0)) a)) :
    ∃ e : OpenPartialHomeomorph (E × F) (E × F),
      (a, 0) ∈ e.source ∧ (∀ v, e v = (G v, v.2)) ∧
        AnalyticAt ℂ e (a, 0) ∧ AnalyticAt ℂ e.symm (e (a, 0)) := by
  letI : CompleteSpace E := FiniteDimensional.complete ℂ E
  letI : CompleteSpace F := FiniteDimensional.complete ℂ F
  have hrestrict : fderiv ℂ (fun u => G (u, 0)) a =
      (fderiv ℂ G (a, 0)).comp (ContinuousLinearMap.inl ℂ E F) :=
    (hG.hasStrictFDerivAt.comp a (ContinuousLinearMap.inl ℂ E F).hasStrictFDerivAt).hasFDerivAt.fderiv
  rw [hrestrict] at hbij
  let A := (fderiv ℂ G (a, 0)).prod (ContinuousLinearMap.snd ℂ E F)
  have hA : Function.Bijective A := s4_q3_triangular_derivative_bijective _ hbij
  let L := ContinuousLinearEquiv.ofBijective A
    (LinearMap.ker_eq_bot.mpr hA.1) (LinearMap.range_eq_top.mpr hA.2)
  have hL : (L : (E × F) →L[ℂ] (E × F)) = A := ContinuousLinearEquiv.coe_ofBijective _ _ _
  have hd : HasStrictFDerivAt (fun v : E × F => (G v, v.2))
      (L : (E × F) →L[ℂ] (E × F)) (a, 0) := by
    rw [hL]
    exact hG.hasStrictFDerivAt.prodMk (ContinuousLinearMap.snd ℂ E F).hasStrictFDerivAt
  let e := hd.toOpenPartialHomeomorph (fun v : E × F => (G v, v.2))
  have ha : (a, 0) ∈ e.source := hd.mem_toOpenPartialHomeomorph_source
  have he : AnalyticAt ℂ e (a, 0) := hG.prod analyticAt_snd
  exact ⟨e, ha, fun _ => rfl, he,
    e.analyticAt_symm' ha he hd.hasFDerivAt.fderiv⟩

end HodgeLean.Foundations.Program
