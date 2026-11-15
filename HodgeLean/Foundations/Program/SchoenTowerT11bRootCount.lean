import HodgeLean.Foundations.Program.SchoenTowerT11bRootResultant
import Mathlib.Topology.LocallyConstant.Basic

/-! Constancy of the number of real roots away from multiple fibers.
HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace HodgeLean.Foundations.Program
open Filter
open scoped Topology

/-- The number of real roots is constant near a simple fiber of a monic family.
Source: Coste, Real Algebraic Sets (2005), Theorem 1.3, root-section continuation step. -/
theorem s2v_t11b_monic_simple_fiber_root_count
    (P : Polynomial (Polynomial ℝ)) (hP : P.Monic) (a : ℝ)
    (hsimple : ∀ x : ℝ, P.eval₂ (Polynomial.evalRingHom a) x = 0 →
      (P.map (Polynomial.evalRingHom a)).derivative.eval x ≠ 0) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ t ∈ Metric.ball a ε,
      (P.map (Polynomial.evalRingHom t)).roots.toFinset.card =
        (P.map (Polynomial.evalRingHom a)).roots.toFinset.card := by
  classical
  obtain ⟨m, ε, _, ψ, hε, _, _, hinj, hroots⟩ :=
    s2v_t11b_monic_simple_fiber_sections P hP a hsimple
  have hcard : ∀ t ∈ Metric.ball a ε,
      (P.map (Polynomial.evalRingHom t)).roots.toFinset.card = m := by
    intro t ht
    let q := P.map (Polynomial.evalRingHom t)
    let S := q.roots.toFinset
    have hq : q ≠ 0 := (hP.map (Polynomial.evalRingHom t)).ne_zero
    have hmem : ∀ x : ℝ, x ∈ S ↔ P.eval₂ (Polynomial.evalRingHom t) x = 0 := by
      intro x
      simpa only [S, Multiset.mem_toFinset, Polynomial.mem_roots hq,
        Polynomial.IsRoot.def, q, ← Polynomial.eval₂_eq_eval_map]
    let f : Fin m → S := fun i => ⟨ψ i t, (hmem _).mpr ((hroots t ht _).mpr ⟨i, rfl⟩)⟩
    have hf : Function.Bijective f := by
      constructor
      · intro i j hij
        exact hinj t ht (congrArg Subtype.val hij)
      · intro x
        obtain ⟨i, hi⟩ := (hroots t ht x.val).mp ((hmem x.val).mp x.property)
        exact ⟨i, Subtype.ext hi.symm⟩
    simpa only [Fintype.card_fin, Fintype.card_coe] using
      (Fintype.card_congr (Equiv.ofBijective f hf)).symm
  exact ⟨ε, hε, fun t ht => (hcard t ht).trans (hcard a (Metric.mem_ball_self hε)).symm⟩

/-- The real root count is constant on every connected parameter set of simple monic fibers.
Source: Coste, Real Algebraic Sets (2005), Theorem 1.3, root-section continuation step. -/
theorem s2v_t11b_monic_root_count_on_preconnected
    (P : Polynomial (Polynomial ℝ)) (hP : P.Monic)
    (K : Set ℝ) (hK : IsPreconnected K)
    (hsimple : ∀ t ∈ K, ∀ x : ℝ, P.eval₂ (Polynomial.evalRingHom t) x = 0 →
      (P.map (Polynomial.evalRingHom t)).derivative.eval x ≠ 0)
    (a b : ℝ) (ha : a ∈ K) (hb : b ∈ K) :
    (P.map (Polynomial.evalRingHom a)).roots.toFinset.card =
      (P.map (Polynomial.evalRingHom b)).roots.toFinset.card := by
  haveI : PreconnectedSpace K := isPreconnected_iff_preconnectedSpace.mp hK
  have hlc : IsLocallyConstant
      (fun t : K => (P.map (Polynomial.evalRingHom t.val)).roots.toFinset.card) := by
    apply (IsLocallyConstant.iff_eventually_eq _).mpr
    intro t
    obtain ⟨ε, hε, hcount⟩ := s2v_t11b_monic_simple_fiber_root_count P hP t.val
      (hsimple t.val t.property)
    have ht : Tendsto (fun u : K => u.val) (𝓝 t) (𝓝 t.val) :=
      continuous_subtype_val.continuousAt
    filter_upwards [ht.eventually (Metric.ball_mem_nhds t.val hε)] with u hu
    exact hcount u.val hu
  exact hlc.apply_eq_of_preconnectedSpace ⟨a, ha⟩ ⟨b, hb⟩

end HodgeLean.Foundations.Program
