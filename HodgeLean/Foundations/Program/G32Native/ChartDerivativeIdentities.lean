import HodgeLean.Foundations.Program.G32Native.FixedChartRegularDerivatives

/-! # Inverse identities for derivatives of the actual ambient charts -/
noncomputable section
set_option maxHeartbeats 200000
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint Filter Topology
open scoped Manifold ContDiff
namespace HodgeLean.Foundations.Program.G32Native

/-- The two actual chart transitions have inverse derivatives at every point
of their overlap. -/
theorem localChart_transition_fderiv_comp
    (W : Over (Spec ↧ℂ)) (d : ℕ) [SmoothOfRelativeDimension d W.hom]
    (p q w : ComplexPoint W)
    (hp : w ∈ (localChart W d p).source) (hq : w ∈ (localChart W d q).source) :
    (fderiv ℂ (fun u => localChart W d q ((localChart W d p).symm u))
      (localChart W d p w)).comp
      (fderiv ℂ (fun u => localChart W d p ((localChart W d q).symm u))
        (localChart W d q w)) = ContinuousLinearMap.id ℂ (Fin d → ℂ) := by
  let ep := localChart W d p
  let eq := localChart W d q
  let T := fun u => ep (eq.symm u)
  let S := fun u => eq (ep.symm u)
  have ht : T (eq w) = ep w := by
    change ep (eq.symm (eq w)) = ep w
    rw [eq.left_inv hq]
  have hT : AnalyticAt ℂ T (eq w) := by
    apply analyticAt_localChart_transition W d q p
    change eq w ∈ eq.target ∧ eq.symm (eq w) ∈ ep.source
    exact ⟨eq.map_source hq, by simpa only [eq.left_inv hq] using hp⟩
  have hS : AnalyticAt ℂ S (ep w) := by
    apply analyticAt_localChart_transition W d p q
    change ep w ∈ ep.target ∧ ep.symm (ep w) ∈ eq.source
    exact ⟨ep.map_source hp, by simpa only [ep.left_inv hp] using hq⟩
  have hc : Tendsto eq.symm (𝓝 (eq w)) (𝓝 w) := by
    simpa only [ContinuousAt, eq.left_inv hq] using eq.continuousAt_symm (eq.map_source hq)
  have hnear : ∀ᶠ u in 𝓝 (eq w), eq.symm u ∈ ep.source :=
    hc (ep.open_source.mem_nhds hp)
  have heq : S ∘ T =ᶠ[𝓝 (eq w)] id := by
    filter_upwards [hnear, eq.open_target.mem_nhds (eq.map_source hq)] with u hu hut
    change eq (ep.symm (ep (eq.symm u))) = u
    rw [ep.left_inv hu, eq.right_inv hut]
  have hSd : DifferentiableAt ℂ S (T (eq w)) := by rw [ht]; exact hS.differentiableAt
  have hd : fderiv ℂ (S ∘ T) (eq w) = fderiv ℂ id (eq w) := heq.fderiv_eq
  rw [fderiv_comp (eq w) hSd hT.differentiableAt, fderiv_id] at hd
  change (fderiv ℂ S (ep w)).comp (fderiv ℂ T (eq w)) = _
  simpa only [ht] using hd

#print axioms localChart_transition_fderiv_comp
end HodgeLean.Foundations.Program.G32Native
