import HodgeLean.Foundations.Program.SchoenTowerT11bDegreeStableSections
import HodgeLean.Foundations.Program.SchoenTowerT11bOrderedRoots

/-! Root continuation for nonmonic families without degree drops.
HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace HodgeLean.Foundations.Program
open Filter
open scoped Topology

/-- A nonzero specialized leading coefficient prevents the specialized polynomial from vanishing.
Source: Coste, Real Algebraic Sets (2005), Theorem 1.3, projection-polynomial step. -/
theorem s2v_t11b_specialization_ne_zero (P : Polynomial (Polynomial ℝ)) (t : ℝ)
    (hlead : P.leadingCoeff.eval t ≠ 0) : P.map (Polynomial.evalRingHom t) ≠ 0 := by
  apply Polynomial.leadingCoeff_ne_zero.mp
  rw [P.leadingCoeff_map_of_leadingCoeff_ne_zero (Polynomial.evalRingHom t) hlead]
  exact hlead

/-- A finite enumeration of all real roots excludes the zero polynomial.
Source: Coste, Real Algebraic Sets (2005), Theorem 1.3, root-enumeration step. -/
theorem s2v_t11b_finite_root_enumeration_ne_zero (q : Polynomial ℝ) {m : ℕ}
    (d : Fin m → ℝ) (hroots : ∀ x, q.eval x = 0 ↔ ∃ i, x = d i) : q ≠ 0 := by
  intro hq
  obtain ⟨x, hx⟩ := (Set.finite_range d).exists_notMem
  obtain ⟨i, hi⟩ := (hroots x).mp (by rw [hq, Polynomial.eval_zero])
  exact hx ⟨i, hi.symm⟩

/-- The number of real roots is constant near a simple fiber without a degree drop.
Source: Coste, Real Algebraic Sets (2005), Theorem 1.3, root-section continuation step. -/
theorem s2v_t11b_simple_fiber_root_count_of_leadingCoeff
    (P : Polynomial (Polynomial ℝ)) (a : ℝ) (hlead : P.leadingCoeff.eval a ≠ 0)
    (hsimple : ∀ x : ℝ, P.eval₂ (Polynomial.evalRingHom a) x = 0 →
      (P.map (Polynomial.evalRingHom a)).derivative.eval x ≠ 0) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ t ∈ Metric.ball a ε,
      (P.map (Polynomial.evalRingHom t)).roots.toFinset.card =
        (P.map (Polynomial.evalRingHom a)).roots.toFinset.card := by
  classical
  obtain ⟨m, ε, _, ψ, hε, _, _, hinj, hroots⟩ :=
    s2v_t11b_simple_fiber_sections_of_leadingCoeff P a hlead hsimple
  have hcard : ∀ t ∈ Metric.ball a ε,
      (P.map (Polynomial.evalRingHom t)).roots.toFinset.card = m := by
    intro t ht
    let q := P.map (Polynomial.evalRingHom t)
    let S := q.roots.toFinset
    have hq : q ≠ 0 := s2v_t11b_finite_root_enumeration_ne_zero q (fun i => ψ i t) (by
      simpa only [q, ← Polynomial.eval₂_eq_eval_map] using hroots t ht)
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

/-- The real root count is constant on every connected parameter set of simple fibers without degree drops.
Source: Coste, Real Algebraic Sets (2005), Theorem 1.3, root-section continuation step. -/
theorem s2v_t11b_root_count_on_preconnected_of_leadingCoeff
    (P : Polynomial (Polynomial ℝ))
    (K : Set ℝ) (hK : IsPreconnected K)
    (hlead : ∀ t ∈ K, P.leadingCoeff.eval t ≠ 0)
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
    obtain ⟨ε, hε, hcount⟩ := s2v_t11b_simple_fiber_root_count_of_leadingCoeff P t.val (hlead t.val t.property)
      (hsimple t.val t.property)
    have ht : Tendsto (fun u : K => u.val) (𝓝 t) (𝓝 t.val) :=
      continuous_subtype_val.continuousAt
    filter_upwards [ht.eventually (Metric.ball_mem_nhds t.val hε)] with u hu
    exact hcount u.val hu
  exact hlc.apply_eq_of_preconnectedSpace ⟨a, ha⟩ ⟨b, hb⟩


/-- On a connected parameter set of simple fibers without degree drops, increasing real roots are continuous globally.
Source: Coste, Real Algebraic Sets (2005), Theorem 1.3, ordered-section continuation step. -/
theorem s2v_t11b_ordered_sections_on_preconnected_of_leadingCoeff
    (P : Polynomial (Polynomial ℝ))
    (K : Set ℝ) (hK : IsPreconnected K) (a : K)
    (hlead : ∀ t ∈ K, P.leadingCoeff.eval t ≠ 0)
    (hsimple : ∀ t ∈ K, ∀ x : ℝ, P.eval₂ (Polynomial.evalRingHom t) x = 0 →
      (P.map (Polynomial.evalRingHom t)).derivative.eval x ≠ 0) :
    ∃ m : ℕ, ∃ ψ : Fin m → K → ℝ,
      (∀ i, Continuous (ψ i)) ∧ (∀ t, StrictMono (fun i => ψ i t)) ∧
      ∀ t : K, ∀ x : ℝ,
        P.eval₂ (Polynomial.evalRingHom t.val) x = 0 ↔ ∃ i, x = ψ i t := by
  classical
  let S := fun t : K => (P.map (Polynomial.evalRingHom t.val)).roots.toFinset
  let m := (S a).card
  have hcount : ∀ t : K, (S t).card = m := fun t =>
    s2v_t11b_root_count_on_preconnected_of_leadingCoeff P K hK hlead hsimple t.val a.val
      t.property a.property
  let ψ : Fin m → K → ℝ := fun i t => (S t).orderEmbOfFin (hcount t) i
  have hmem : ∀ (t : K) (x : ℝ), x ∈ S t ↔
      P.eval₂ (Polynomial.evalRingHom t.val) x = 0 := by
    intro t x
    simpa only [S, Multiset.mem_toFinset, Polynomial.mem_roots
      (s2v_t11b_specialization_ne_zero P t.val (hlead t.val t.property)), Polynomial.IsRoot.def,
      Polynomial.eval₂_eq_eval_map]
  refine ⟨m, ψ, ?_, fun t => ((S t).orderEmbOfFin (hcount t)).strictMono, ?_⟩
  · intro i
    apply continuous_iff_continuousAt.mpr
    intro t
    obtain ⟨k, ε, d, φ, hε, _, hφ, hinj, hroots⟩ :=
      s2v_t11b_simple_fiber_sections_of_leadingCoeff P t.val (hlead t.val t.property) (hsimple t.val t.property)
    have htball : t.val ∈ Metric.ball t.val ε := Metric.mem_ball_self hε
    have hkm : k = m := by
      have hk := s2v_t11b_root_enumeration_card
        (P.map (Polynomial.evalRingHom t.val))
        (s2v_t11b_specialization_ne_zero P t.val (hlead t.val t.property))
        (fun j => φ j t.val) (hinj t.val htball) (by
          simpa only [← Polynomial.eval₂_eq_eval_map] using hroots t.val htball)
      exact hk.symm.trans (hcount t)
    subst k
    have hcont : ∀ j, ContinuousAt (φ j) t.val := fun j =>
      ((hφ j).2.continuousOn t.val htball).continuousAt
        (Metric.isOpen_ball.mem_nhds htball)
    obtain ⟨E, hE⟩ := s2v_t11b_sections_eventually_ordered φ t.val hcont (hinj t.val htball)
    have hlocal : ∀ᶠ u : K in 𝓝 t, ψ i u = φ (E i) u.val := by
      have ht : Tendsto (fun u : K => u.val) (𝓝 t) (𝓝 t.val) :=
        continuous_subtype_val.continuousAt
      filter_upwards [ht.eventually hE,
        ht.eventually (Metric.ball_mem_nhds t.val hε)] with u hu huε
      have heq : (fun j => φ (E j) u.val) = (S u).orderEmbOfFin (hcount u) :=
        Finset.orderEmbOfFin_unique (hcount u)
          (fun j => (hmem u _).mpr ((hroots u.val huε _).mpr ⟨E j, rfl⟩)) hu
      exact (congrFun heq i).symm
    exact ((hcont (E i)).comp continuous_subtype_val.continuousAt).congr_of_eventuallyEq
      hlocal
  · intro t x
    rw [← hmem]
    change x ∈ (↑(S t) : Set ℝ) ↔ ∃ i, x = (S t).orderEmbOfFin (hcount t) i
    rw [← Finset.range_orderEmbOfFin (S t) (hcount t)]
    exact ⟨fun ⟨i, hi⟩ => ⟨i, hi.symm⟩, fun ⟨i, hi⟩ => ⟨i, hi.symm⟩⟩

end HodgeLean.Foundations.Program
