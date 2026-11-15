import HodgeLean.Foundations.Program.SchoenTowerT11bCoefficientSections
import HodgeLean.Foundations.Program.SchoenTowerT11bDegreeStableRoots

/-! Ordered root continuation over Banach parameter spaces.
HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace HodgeLean.Foundations.Program
open Filter
open scoped Topology

/-- Distinct continuous sections can be indexed in increasing order on a neighborhood.
Source: Coste, Real Algebraic Sets (2005), Theorem 1.3, ordered-section step. -/
theorem s2v_t11b_continuous_sections_eventually_ordered {X : Type*} [TopologicalSpace X]
    {m : ℕ} (ψ : Fin m → X → ℝ) (a : X) (hc : ∀ i, ContinuousAt (ψ i) a)
    (hinj : Function.Injective (fun i => ψ i a)) :
    ∃ E : Fin m ≃ Fin m, ∀ᶠ t in 𝓝 a, StrictMono (fun i => ψ (E i) t) := by
  classical
  let S := Finset.univ.image (fun i => ψ i a)
  have hS : S.card = m := by
    rw [Finset.card_image_of_injective _ hinj, Finset.card_fin]
  let F : Fin m ≃ S := Equiv.ofBijective (fun i => ⟨ψ i a,
    Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩⟩) (by
      constructor
      · intro i j h
        exact hinj (congrArg Subtype.val h)
      · intro x
        obtain ⟨i, _, hi⟩ := Finset.mem_image.mp x.property
        exact ⟨i, Subtype.ext hi⟩)
  let E := (S.orderIsoOfFin hS).toEquiv.trans F.symm
  have heq : ∀ i, ψ (E i) a = S.orderEmbOfFin hS i := by
    intro i
    exact congrArg Subtype.val (F.apply_symm_apply (S.orderIsoOfFin hS i))
  have hmono : StrictMono (fun i => ψ (E i) a) := by
    simpa only [heq] using (S.orderEmbOfFin hS).strictMono
  refine ⟨E, ?_⟩
  have hpair : ∀ i j, ∀ᶠ t in 𝓝 a, i < j → ψ (E i) t < ψ (E j) t := by
    intro i j
    by_cases hij : i < j
    · exact ((hc (E i)).eventually_lt (hc (E j)) (hmono hij)).mono (fun _ h _ => h)
    · exact Filter.Eventually.of_forall (fun _ h => (hij h).elim)
  filter_upwards [eventually_all.mpr (fun i => eventually_all.mpr (hpair i))] with t ht
  exact fun i j hij => ht i j hij

/-- The distinct real root count is constant near a simple degree-preserving fiber over a Banach parameter space.
Source: Coste, Real Algebraic Sets (2005), Theorem 1.3, higher-dimensional root-count step. -/
theorem s2v_t11b_smooth_coefficient_local_root_count {V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
    (P : Polynomial (V → ℝ)) (hP : ∀ i, ContDiff ℝ (⊤ : WithTop ℕ∞) (P.coeff i))
    (a : V) (hlead : P.leadingCoeff a ≠ 0)
    (hsimple : ∀ x : ℝ, P.eval₂ (Pi.evalRingHom (fun _ : V => ℝ) a) x = 0 →
      (P.map (Pi.evalRingHom (fun _ : V => ℝ) a)).derivative.eval x ≠ 0) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ t ∈ Metric.ball a ε,
      (P.map (Pi.evalRingHom (fun _ : V => ℝ) t)).roots.toFinset.card =
        (P.map (Pi.evalRingHom (fun _ : V => ℝ) a)).roots.toFinset.card := by
  classical
  obtain ⟨m, ε, _, ψ, hε, _, _, hinj, hroots⟩ :=
    s2v_t11b_smooth_coefficient_simple_fiber_sections P hP a hlead hsimple
  have hcard : ∀ t ∈ Metric.ball a ε,
      (P.map (Pi.evalRingHom (fun _ : V => ℝ) t)).roots.toFinset.card = m := by
    intro t ht
    let q := P.map (Pi.evalRingHom (fun _ : V => ℝ) t)
    have hr : ∀ x, q.eval x = 0 ↔ ∃ i, x = ψ i t := by
      simpa only [q, ← Polynomial.eval₂_eq_eval_map] using hroots t ht
    exact s2v_t11b_root_enumeration_card q
      (s2v_t11b_finite_root_enumeration_ne_zero q (fun i => ψ i t) hr)
      (fun i => ψ i t) (hinj t ht) hr
  exact ⟨ε, hε, fun t ht => (hcard t ht).trans (hcard a (Metric.mem_ball_self hε)).symm⟩

/-- The real root count is constant on every connected parameter set of simple fibers without degree drops.
Source: Coste, Real Algebraic Sets (2005), Theorem 1.3, root-section continuation step. -/
theorem s2v_t11b_smooth_coefficient_root_count_on_preconnected {V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
    (P : Polynomial (V → ℝ)) (hP : ∀ i, ContDiff ℝ (⊤ : WithTop ℕ∞) (P.coeff i))
    (K : Set V) (hK : IsPreconnected K)
    (hlead : ∀ t ∈ K, P.leadingCoeff t ≠ 0)
    (hsimple : ∀ t ∈ K, ∀ x : ℝ, P.eval₂ (Pi.evalRingHom (fun _ : V => ℝ) t) x = 0 →
      (P.map (Pi.evalRingHom (fun _ : V => ℝ) t)).derivative.eval x ≠ 0)
    (a b : V) (ha : a ∈ K) (hb : b ∈ K) :
    (P.map (Pi.evalRingHom (fun _ : V => ℝ) a)).roots.toFinset.card =
      (P.map (Pi.evalRingHom (fun _ : V => ℝ) b)).roots.toFinset.card := by
  haveI : PreconnectedSpace K := isPreconnected_iff_preconnectedSpace.mp hK
  have hlc : IsLocallyConstant
      (fun t : K => (P.map (Pi.evalRingHom (fun _ : V => ℝ) t.val)).roots.toFinset.card) := by
    apply (IsLocallyConstant.iff_eventually_eq _).mpr
    intro t
    obtain ⟨ε, hε, hcount⟩ := s2v_t11b_smooth_coefficient_local_root_count P hP t.val (hlead t.val t.property)
      (hsimple t.val t.property)
    have ht : Tendsto (fun u : K => u.val) (𝓝 t) (𝓝 t.val) :=
      continuous_subtype_val.continuousAt
    filter_upwards [ht.eventually (Metric.ball_mem_nhds t.val hε)] with u hu
    exact hcount u.val hu
  exact hlc.apply_eq_of_preconnectedSpace ⟨a, ha⟩ ⟨b, hb⟩


/-- On a connected parameter set of simple fibers without degree drops, increasing real roots are continuous globally.
Source: Coste, Real Algebraic Sets (2005), Theorem 1.3, ordered-section continuation step. -/
theorem s2v_t11b_smooth_coefficient_ordered_sections {V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
    (P : Polynomial (V → ℝ)) (hP : ∀ i, ContDiff ℝ (⊤ : WithTop ℕ∞) (P.coeff i))
    (K : Set V) (hK : IsPreconnected K) (a : K)
    (hlead : ∀ t ∈ K, P.leadingCoeff t ≠ 0)
    (hsimple : ∀ t ∈ K, ∀ x : ℝ, P.eval₂ (Pi.evalRingHom (fun _ : V => ℝ) t) x = 0 →
      (P.map (Pi.evalRingHom (fun _ : V => ℝ) t)).derivative.eval x ≠ 0) :
    ∃ m : ℕ, ∃ ψ : Fin m → K → ℝ,
      (∀ i, Continuous (ψ i)) ∧ (∀ t, StrictMono (fun i => ψ i t)) ∧
      ∀ t : K, ∀ x : ℝ,
        P.eval₂ (Pi.evalRingHom (fun _ : V => ℝ) t.val) x = 0 ↔ ∃ i, x = ψ i t := by
  classical
  let S := fun t : K => (P.map (Pi.evalRingHom (fun _ : V => ℝ) t.val)).roots.toFinset
  let m := (S a).card
  have hcount : ∀ t : K, (S t).card = m := fun t =>
    s2v_t11b_smooth_coefficient_root_count_on_preconnected P hP K hK hlead hsimple t.val a.val
      t.property a.property
  let ψ : Fin m → K → ℝ := fun i t => (S t).orderEmbOfFin (hcount t) i
  have hmem : ∀ (t : K) (x : ℝ), x ∈ S t ↔
      P.eval₂ (Pi.evalRingHom (fun _ : V => ℝ) t.val) x = 0 := by
    intro t x
    simpa only [S, Multiset.mem_toFinset, Polynomial.mem_roots
      (s2v_t11b_coefficient_specialization_ne_zero P t.val (hlead t.val t.property)), Polynomial.IsRoot.def,
      Polynomial.eval₂_eq_eval_map]
  refine ⟨m, ψ, ?_, fun t => ((S t).orderEmbOfFin (hcount t)).strictMono, ?_⟩
  · intro i
    apply continuous_iff_continuousAt.mpr
    intro t
    obtain ⟨k, ε, d, φ, hε, _, hφ, hinj, hroots⟩ :=
      s2v_t11b_smooth_coefficient_simple_fiber_sections P hP t.val (hlead t.val t.property) (hsimple t.val t.property)
    have htball : t.val ∈ Metric.ball t.val ε := Metric.mem_ball_self hε
    have hkm : k = m := by
      have hk := s2v_t11b_root_enumeration_card
        (P.map (Pi.evalRingHom (fun _ : V => ℝ) t.val))
        (s2v_t11b_coefficient_specialization_ne_zero P t.val (hlead t.val t.property))
        (fun j => φ j t.val) (hinj t.val htball) (by
          simpa only [← Polynomial.eval₂_eq_eval_map] using hroots t.val htball)
      exact hk.symm.trans (hcount t)
    subst k
    have hcont : ∀ j, ContinuousAt (φ j) t.val := fun j =>
      ((hφ j).2.continuousOn t.val htball).continuousAt
        (Metric.isOpen_ball.mem_nhds htball)
    obtain ⟨E, hE⟩ := s2v_t11b_continuous_sections_eventually_ordered φ t.val hcont (hinj t.val htball)
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
