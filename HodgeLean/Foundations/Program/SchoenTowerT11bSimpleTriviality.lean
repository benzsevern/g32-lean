import HodgeLean.Foundations.Program.SchoenTowerT11bFiniteGraphs

/-! Actual-fiber local trivializations of monic families with simple real roots.
HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

/-- Near a simple real fiber, the entire monic polynomial zero set has actual-fiber product coordinates.
Source: Coste, Real Algebraic Sets (2005), Theorem 1.3, local root-section assembly step. -/
theorem s2v_t11b_monic_simple_fiber_triviality
    (P : Polynomial (Polynomial ℝ)) (hP : P.Monic) (a : ℝ)
    (hsimple : ∀ x : ℝ, P.eval₂ (Polynomial.evalRingHom a) x = 0 →
      (P.map (Polynomial.evalRingHom a)).derivative.eval x ≠ 0) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ e :
      ({x : ℝ | P.eval₂ (Polynomial.evalRingHom a) x = 0} × Metric.ball a ε) ≃ₜ
      {z : Metric.ball a ε × ℝ | P.eval₂ (Polynomial.evalRingHom z.1.val) z.2 = 0},
      ∀ y, (e y).val.1 = y.2 := by
  classical
  obtain ⟨m, ε, d, ψ, hε, _, hψ, hinj, hroots⟩ :=
    s2v_t11b_monic_simple_fiber_sections P hP a hsimple
  let B := Metric.ball a ε
  let R := {x : ℝ | P.eval₂ (Polynomial.evalRingHom a) x = 0}
  have ha : a ∈ Metric.ball a ε := Metric.mem_ball_self hε
  let idx : Fin m → R := fun i => ⟨ψ i a, (hroots a ha (ψ i a)).mpr ⟨i, rfl⟩⟩
  have hidx : Function.Bijective idx := by
    constructor
    · intro i j hij
      exact hinj a ha (congrArg Subtype.val hij)
    · intro x
      obtain ⟨i, hi⟩ := (hroots a ha x.val).mp x.property
      exact ⟨i, Subtype.ext hi.symm⟩
  let rootEquiv : Fin m ≃ₜ R := (Equiv.ofBijective idx hidx).toHomeomorphOfContinuousClosed
    continuous_of_discreteTopology (fun A _ => ((Set.toFinite A).image idx).isClosed)
  have hc : ∀ i : Fin m, Continuous (fun t : B => ψ i t.val) := fun i =>
    continuousOn_iff_continuous_domRestrict.mp (hψ i).2.continuousOn
  let e₀ := s2v_t11b_finite_graph_homeomorph (fun i (t : B) => ψ i t.val) hc
    (fun t => hinj t.val t.property)
  have hsets : {z : B × ℝ | ∃ i, z.2 = ψ i z.1.val} =
      {z : B × ℝ | P.eval₂ (Polynomial.evalRingHom z.1.val) z.2 = 0} := by
    ext z
    exact (hroots z.1.val z.1.property z.2).symm
  let e := ((rootEquiv.symm.prodCongr (Homeomorph.refl B)).trans e₀).trans
    (Homeomorph.setCongr hsets)
  refine ⟨ε, hε, e, ?_⟩
  intro y
  exact congrArg Prod.fst
    (s2v_t11b_finite_graph_homeomorph_apply (fun i (t : B) => ψ i t.val) hc
      (fun t => hinj t.val t.property) (rootEquiv.symm y.1) y.2)

end HodgeLean.Foundations.Program
