import HodgeLean.Foundations.Program.SchoenTowerT11bRootCount
import Mathlib.Data.Finset.Sort

/-! Ordered real sections of monic polynomial families.
HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace HodgeLean.Foundations.Program
open Filter
open scoped Topology

/-- An injective enumeration of all real roots determines the distinct-root count.
Source: Coste, Real Algebraic Sets (2005), Theorem 1.3, root-enumeration step. -/
theorem s2v_t11b_root_enumeration_card (q : Polynomial ℝ) (hq : q ≠ 0)
    {m : ℕ} (d : Fin m → ℝ) (hd : Function.Injective d)
    (hroots : ∀ x, q.eval x = 0 ↔ ∃ i, x = d i) :
    q.roots.toFinset.card = m := by
  classical
  let E : Fin m → q.roots.toFinset := fun i =>
    ⟨d i, Multiset.mem_toFinset.mpr ((Polynomial.mem_roots hq).mpr
      ((hroots (d i)).mpr ⟨i, rfl⟩))⟩
  have hE : Function.Bijective E := by
    constructor
    · intro i j h
      exact hd (congrArg Subtype.val h)
    · intro x
      obtain ⟨i, hi⟩ := (hroots x.val).mp
        ((Polynomial.mem_roots hq).mp (Multiset.mem_toFinset.mp x.property))
      exact ⟨i, Subtype.ext hi.symm⟩
  simpa only [Fintype.card_fin, Fintype.card_coe] using
    (Fintype.card_congr (Equiv.ofBijective E hE)).symm

/-- Distinct continuous sections can be indexed in increasing order on a neighborhood.
Source: Coste, Real Algebraic Sets (2005), Theorem 1.3, ordered-section step. -/
theorem s2v_t11b_sections_eventually_ordered {m : ℕ} (ψ : Fin m → ℝ → ℝ)
    (a : ℝ) (hc : ∀ i, ContinuousAt (ψ i) a)
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

/-- On a connected parameter set of simple monic fibers, increasing real roots are continuous globally.
Source: Coste, Real Algebraic Sets (2005), Theorem 1.3, ordered-section continuation step. -/
theorem s2v_t11b_monic_ordered_sections_on_preconnected
    (P : Polynomial (Polynomial ℝ)) (hP : P.Monic)
    (K : Set ℝ) (hK : IsPreconnected K) (a : K)
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
    s2v_t11b_monic_root_count_on_preconnected P hP K hK hsimple t.val a.val
      t.property a.property
  let ψ : Fin m → K → ℝ := fun i t => (S t).orderEmbOfFin (hcount t) i
  have hmem : ∀ (t : K) (x : ℝ), x ∈ S t ↔
      P.eval₂ (Polynomial.evalRingHom t.val) x = 0 := by
    intro t x
    simpa only [S, Multiset.mem_toFinset, Polynomial.mem_roots
      (hP.map (Polynomial.evalRingHom t.val)).ne_zero, Polynomial.IsRoot.def,
      Polynomial.eval₂_eq_eval_map]
  refine ⟨m, ψ, ?_, fun t => ((S t).orderEmbOfFin (hcount t)).strictMono, ?_⟩
  · intro i
    apply continuous_iff_continuousAt.mpr
    intro t
    obtain ⟨k, ε, d, φ, hε, _, hφ, hinj, hroots⟩ :=
      s2v_t11b_monic_simple_fiber_sections P hP t.val (hsimple t.val t.property)
    have htball : t.val ∈ Metric.ball t.val ε := Metric.mem_ball_self hε
    have hkm : k = m := by
      have hk := s2v_t11b_root_enumeration_card
        (P.map (Polynomial.evalRingHom t.val))
        (hP.map (Polynomial.evalRingHom t.val)).ne_zero
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
