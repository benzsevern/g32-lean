import HodgeLean.Foundations.Program.G32Native.CanonicalAbelFibreConstancy
import HodgeLean.Foundations.Program.G32Native.CanonicalAbelLiftDerivative
import HodgeLean.Foundations.Program.G32Native.LocalLiftConstancy

/-! # Vanishing on the actual immersion tangent -/
noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint Filter
open HodgeLean.Adapters HodgeLean.Foundations.Curves.AbelAdapter
open scoped BigOperators Topology
namespace HodgeLean.Foundations.Program.G32Native

/-- The actual Abel differential vanishes on the specified immersion tangent. -/
theorem canonical_abel_tangent_vanishes (G : CanonicalAbelGeometry) (p : ComplexPoint G.Z)
    (F : ComplexPoint G.Q → (Fin (G.k + G.k) → ℂ) → (Fin (G.k + 1) → ℂ))
    (x : ComplexPoint G.Q)
    (hFa : AnalyticAt ℂ (F x)
      (localChart G.W (G.k + G.k) (Point.map G.ι x) (Point.map G.ι x)))
    (hFe : ∀ᶠ w in 𝓝 (Point.map G.ι x), ∀ z : Fin (2 * G.k) → ComplexPoint G.Z,
      Point.map G.γ (s2_lift (2 * G.k) z) = Point.map G.β w →
      canonicalPeriodQuotient G (F x (localChart G.W (G.k + G.k) (Point.map G.ι x) w)) =
        ∑ i, analyticAbel (Module.finrank_fin_fun (n := 1) ℂ) p (z i)) :
    ∀ v, canonicalAbelDifferential G F x
      ((fderiv ℂ (inclusionInComplexCharts G.W G.Q G.ι G.k (G.k + G.k) x)
        (localChart G.Q G.k x x)).toLinearMap v) = 0 := by
  let C := localChart G.Q G.k x
  let u₀ := C x
  let e := inclusionInComplexCharts G.W G.Q G.ι G.k (G.k + G.k) x
  have hs : x ∈ C.source := mem_localChart_source _ _ _
  have hi := analyticAt_inclusionInComplexCharts G.W G.Q G.ι G.k (G.k + G.k) x
  have he₀ : e u₀ = localChart G.W (G.k + G.k) (Point.map G.ι x) (Point.map G.ι x) :=
    inclusionInComplexCharts_at_center _ _ _ _ _ _
  have hFa' : DifferentiableAt ℂ (F x) (e u₀) := by rw [he₀]; exact hFa.differentiableAt
  have hd : DifferentiableAt ℂ (fun u => F x (e u)) u₀ := hFa'.comp u₀ hi.differentiableAt
  have ht : Tendsto (fun u => Point.map G.ι (C.symm u)) (𝓝 u₀) (𝓝 (Point.map G.ι x)) := by
    have hh := (Point.continuous_map G.ι).continuousAt.comp
      (C.continuousAt_symm (C.map_source hs))
    have hht := hh.tendsto
    change Tendsto (fun u => Point.map G.ι (C.symm u)) (𝓝 u₀)
      (𝓝 (Point.map G.ι (C.symm (C x)))) at hht
    rw [C.left_inv hs] at hht
    exact hht
  have hvalue : ∀ᶠ u in 𝓝 u₀, canonicalPeriodQuotient G (F x (e u)) =
      canonicalSymmetricAbel G p (Point.map G.β (Point.map G.ι x)) := by
    filter_upwards [ht.eventually (canonical_lift_quotient_germ G p x (F x) hFe)] with u hu
    exact hu.trans (canonicalSymmetricAbel_component_constant G p (C.symm u) x)
  have hconstant := local_homeomorph_lift_eventually_constant (canonicalPeriodQuotient G)
    (canonicalPeriodQuotient_isLocalHomeomorph G) hd.continuousAt
    (hvalue.mono (fun _ hu => hu.trans hvalue.self_of_nhds.symm))
  have hconstantEq : (fun u => F x (e u)) =ᶠ[𝓝 u₀] (fun _ => F x (e u₀)) := hconstant
  have hzero : fderiv ℂ (fun u => F x (e u)) u₀ = 0 := by
    rw [hconstantEq.fderiv_eq]
    exact fderiv_const_apply (𝕜 := ℂ) (x := u₀) (F x (e u₀))
  have hchain := fderiv_comp u₀ hFa' hi.differentiableAt
  rw [he₀] at hchain
  intro v
  have hv := congrArg (fun L : (Fin G.k → ℂ) →L[ℂ] (Fin (G.k + 1) → ℂ) => L v)
    (hchain.symm.trans hzero)
  change fderiv ℂ (F x)
    (localChart G.W (G.k + G.k) (Point.map G.ι x) (Point.map G.ι x))
    (fderiv ℂ e u₀ v) = 0 at hv
  change coefficientDual G.k (fderiv ℂ (F x)
    (localChart G.W (G.k + G.k) (Point.map G.ι x) (Point.map G.ι x))
    (fderiv ℂ e u₀ v)) = 0
  rw [hv, map_zero]

#print axioms canonical_abel_tangent_vanishes
end HodgeLean.Foundations.Program.G32Native
