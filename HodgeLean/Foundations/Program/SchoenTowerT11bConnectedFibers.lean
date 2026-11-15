import HodgeLean.Foundations.Program.SchoenTowerT11bOrderedRoots

/-! Actual-fiber coordinates over connected sets of simple monic fibers.
HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

/-- Increasing real root sections give product coordinates over a connected parameter set.
Source: Coste, Real Algebraic Sets (2005), Theorem 1.3, ordered-section assembly step. -/
theorem s2v_t11b_monic_simple_connected_triviality
    (P : Polynomial (Polynomial ℝ)) (hP : P.Monic)
    (K : Set ℝ) (hK : IsPreconnected K) (a : K)
    (hsimple : ∀ t ∈ K, ∀ x : ℝ, P.eval₂ (Polynomial.evalRingHom t) x = 0 →
      (P.map (Polynomial.evalRingHom t)).derivative.eval x ≠ 0) :
    ∃ e : ({x : ℝ | P.eval₂ (Polynomial.evalRingHom a.val) x = 0} × K) ≃ₜ
      {z : K × ℝ | P.eval₂ (Polynomial.evalRingHom z.1.val) z.2 = 0},
      ∀ y, (e y).val.1 = y.2 := by
  classical
  obtain ⟨m, ψ, hc, hmono, hroots⟩ :=
    s2v_t11b_monic_ordered_sections_on_preconnected P hP K hK a hsimple
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

/-- A family over a singleton base has its actual fiber as constant product model.
Source: Coste, Real Algebraic Sets (2005), Theorem 1.17, point-piece step. -/
def s2v_t11b_singleton_family_chart (F : ℝ → ℝ → ℝ) (K : Set ℝ) (a : ℝ)
    (hK : ∀ t ∈ K, t = a) :
    ({x : ℝ | F a x = 0} × K) ≃ₜ {z : K × ℝ | F z.1.val z.2 = 0} where
  toFun y := ⟨(y.2, y.1.val), by
    change F y.2.val y.1.val = 0
    rw [hK y.2.val y.2.property]
    exact y.1.property⟩
  invFun z := (⟨z.val.2, by rw [← hK z.val.1.val z.val.1.property]; exact z.property⟩,
    z.val.1)
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := (continuous_snd.prodMk
    (continuous_subtype_val.comp continuous_fst)).subtype_mk _
  continuous_invFun := ((continuous_snd.comp continuous_subtype_val).subtype_mk _).prodMk
    (continuous_fst.comp continuous_subtype_val)

end HodgeLean.Foundations.Program
