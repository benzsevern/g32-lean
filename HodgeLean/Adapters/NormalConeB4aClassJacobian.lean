import HodgeLean.Adapters.NormalConeB4aClassInverseDense
import HodgeConjecture.Lemmas.AlgebraicTopology.LocalHomology.ChartFundamentalClassInvariance

/-! # Analytic Jacobians on chart domains

Route: the derivative of an analytic map is analytic. The determinant is a
finite sum of products of its matrix entries in the standard complex basis.
-/
noncomputable section
namespace HodgeLean.Adapters
open Set Filter Topology AlgebraicTopology.Singular

set_option backward.isDefEq.respectTransparency false in
/-- The determinant of the derivative is analytic on an analytic map's open
domain. -/
theorem a3b4a_classJacobian_analytic
    {n : ℕ} (f : (Fin n → ℂ) → (Fin n → ℂ))
    (U : Set (Fin n → ℂ)) (hU : IsOpen U) (hf : AnalyticOnNhd ℂ f U) :
    AnalyticOnNhd ℂ (fun x => (complexMatrixOfContinuousLinearMap n (fderiv ℂ f x)).det) U := by
  intro x hx
  have hd : AnalyticAt ℂ (fderiv ℂ f) x := hf.fderiv_of_isOpen hU x hx
  simp only [Matrix.det_apply', complexMatrixOfContinuousLinearMap, LinearMap.toMatrix'_apply,
    ContinuousLinearMap.coe_coe]
  apply Finset.analyticAt_fun_sum
  intro σ hσ
  apply analyticAt_const.mul
  apply Finset.analyticAt_fun_prod
  intro i hi
  change AnalyticAt ℂ (fun z => fderiv ℂ f z (Pi.single i 1) (σ i)) x
  let ev : ((Fin n → ℂ) →L[ℂ] (Fin n → ℂ)) →L[ℂ] (Fin n → ℂ) :=
    ContinuousLinearMap.apply ℂ (Fin n → ℂ) (Pi.single i 1)
  have heval : AnalyticAt ℂ (fun z => fderiv ℂ f z (Pi.single i 1)) x :=
    (ev.analyticAt (fderiv ℂ f x)).comp hd
  exact ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin n => ℂ) (σ i)).analyticAt _).comp
    heval

end HodgeLean.Adapters
