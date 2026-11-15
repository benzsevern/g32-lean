import HodgeLean.Foundations.Program.SchoenTowerT11bDegreeStableRoots
import HodgeLean.Foundations.Program.SchoenTowerT11bConnectedFibers

/-! Product coordinates without monicity on the parameter region.
HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

/-- Increasing real root sections give product coordinates over a connected parameter set.
Source: Coste, Real Algebraic Sets (2005), Theorem 1.3, ordered-section assembly step. -/
theorem s2v_t11b_simple_connected_triviality_of_leadingCoeff
    (P : Polynomial (Polynomial ℝ))
    (K : Set ℝ) (hK : IsPreconnected K) (a : K)
    (hlead : ∀ t ∈ K, P.leadingCoeff.eval t ≠ 0)
    (hsimple : ∀ t ∈ K, ∀ x : ℝ, P.eval₂ (Polynomial.evalRingHom t) x = 0 →
      (P.map (Polynomial.evalRingHom t)).derivative.eval x ≠ 0) :
    ∃ e : ({x : ℝ | P.eval₂ (Polynomial.evalRingHom a.val) x = 0} × K) ≃ₜ
      {z : K × ℝ | P.eval₂ (Polynomial.evalRingHom z.1.val) z.2 = 0},
      ∀ y, (e y).val.1 = y.2 := by
  classical
  obtain ⟨m, ψ, hc, hmono, hroots⟩ :=
    s2v_t11b_ordered_sections_on_preconnected_of_leadingCoeff P K hK a hlead hsimple
  let R := {x : ℝ | P.eval₂ (Polynomial.evalRingHom a.val) x = 0}
  let idx : Fin m → R := fun i => ⟨ψ i a, (hroots a _).mpr ⟨i, rfl⟩⟩
  have hidx : Function.Bijective idx := by
    constructor
    · intro i j hij
      exact (hmono a).injective (congrArg Subtype.val hij)
    · intro x
      obtain ⟨i, hi⟩ := (hroots a x.val).mp x.property
      exact ⟨i, Subtype.ext hi.symm⟩
  let rootEquiv : Fin m ≃ₜ R := (Equiv.ofBijective idx hidx).toHomeomorphOfContinuousClosed
    continuous_of_discreteTopology (fun A _ => ((Set.toFinite A).image idx).isClosed)
  let e₀ := s2v_t11b_finite_graph_homeomorph ψ hc (fun t => (hmono t).injective)
  have hsets : {z : K × ℝ | ∃ i, z.2 = ψ i z.1} =
      {z : K × ℝ | P.eval₂ (Polynomial.evalRingHom z.1.val) z.2 = 0} := by
    ext z
    exact (hroots z.1 z.2).symm
  let e := ((rootEquiv.symm.prodCongr (Homeomorph.refl K)).trans e₀).trans
    (Homeomorph.setCongr hsets)
  refine ⟨e, ?_⟩
  intro y
  exact congrArg Prod.fst
    (s2v_t11b_finite_graph_homeomorph_apply ψ hc (fun t => (hmono t).injective)
      (rootEquiv.symm y.1) y.2)

end HodgeLean.Foundations.Program
