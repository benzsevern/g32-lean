import HodgeLean.Foundations.Program.SchoenTowerT11bPlaneSectionMembership
import Mathlib.Topology.Connected.Clopen

/-! Continuation of polynomial factors along simple real root sections.
HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace HodgeLean.Foundations.Program
open Filter
open scoped Topology

/-- A divisor vanishing once on a connected simple-root section vanishes along the whole section.
Source: Coste, Real Algebraic Sets (2005), Theorem 1.3, factor-continuation step. -/
theorem s2v_t11b_divisor_root_section_continuation
    (P D : Polynomial (Polynomial ℝ)) (hdiv : D ∣ P)
    (K : Set ℝ) (hK : IsPreconnected K) (ψ : K → ℝ) (hψ : Continuous ψ)
    (hroot : ∀ t : K, P.eval₂ (Polynomial.evalRingHom t.val) (ψ t) = 0)
    (hsimple : ∀ t : K,
      (P.map (Polynomial.evalRingHom t.val)).derivative.eval (ψ t) ≠ 0)
    (a : K) (ha : D.eval₂ (Polynomial.evalRingHom a.val) (ψ a) = 0) :
    ∀ t : K, D.eval₂ (Polynomial.evalRingHom t.val) (ψ t) = 0 := by
  obtain ⟨G, hPG⟩ := hdiv
  haveI : PreconnectedSpace K := isPreconnected_iff_preconnectedSpace.mp hK
  let d : K → ℝ := fun t => D.eval₂ (Polynomial.evalRingHom t.val) (ψ t)
  let e : K → ℝ := fun t => G.eval₂ (Polynomial.evalRingHom t.val) (ψ t)
  have hd : Continuous d := (s2v_t11b_polynomial_family_contDiff D).continuous.comp
    (continuous_subtype_val.prodMk hψ)
  have he : Continuous e := (s2v_t11b_polynomial_family_contDiff G).continuous.comp
    (continuous_subtype_val.prodMk hψ)
  have hcofactor : ∀ t : K, d t = 0 → e t ≠ 0 := by
    intro t ht hez
    apply hsimple t
    have hz : P.derivative.eval₂ (Polynomial.evalRingHom t.val) (ψ t) = 0 := by
      rw [hPG, Polynomial.derivative_mul, Polynomial.eval₂_add,
        Polynomial.eval₂_mul, Polynomial.eval₂_mul]
      change _ * e t + d t * _ = 0
      rw [ht, hez, mul_zero, zero_mul, zero_add]
    simpa only [Polynomial.eval₂_eq_eval_map, Polynomial.derivative_map] using hz
  let L : Set K := {t | d t = 0}
  have hclosed : IsClosed L := isClosed_eq hd continuous_const
  have hopen : IsOpen L := by
    apply isOpen_iff_mem_nhds.mpr
    intro t ht
    have hn : ∀ᶠ u in 𝓝 t, e u ≠ 0 :=
      (he.continuousAt.ne_iff_eventually_ne continuousAt_const).mp (hcofactor t ht)
    filter_upwards [hn] with u hu
    have hz : d u * e u = 0 := by
      simpa only [hPG, Polynomial.eval₂_mul] using hroot u
    exact (mul_eq_zero.mp hz).resolve_right hu
  have hL : L = Set.univ := (show IsClopen L from ⟨hclosed, hopen⟩).eq_univ ⟨a, ha⟩
  intro t
  change t ∈ L
  rw [hL]
  exact Set.mem_univ t

/-- A divisor vanishing at a simple real root must have positive spatial degree.
Source: Coste, Real Algebraic Sets (2005), Theorem 1.3, vertical-factor exclusion step. -/
theorem s2v_t11b_divisor_root_positive_degree
    (P D : Polynomial (Polynomial ℝ)) (hdiv : D ∣ P) (t x : ℝ)
    (hD : D.eval₂ (Polynomial.evalRingHom t) x = 0)
    (hsimple : (P.map (Polynomial.evalRingHom t)).derivative.eval x ≠ 0) :
    D.natDegree ≠ 0 := by
  intro hd
  obtain ⟨G, hPG⟩ := hdiv
  apply hsimple
  have hz : P.derivative.eval₂ (Polynomial.evalRingHom t) x = 0 := by
    rw [hPG, Polynomial.derivative_mul, Polynomial.derivative_eq_zero.mpr hd,
      zero_mul, zero_add, Polynomial.eval₂_mul, hD, zero_mul]
  simpa only [Polynomial.eval₂_eq_eval_map, Polynomial.derivative_map] using hz

end HodgeLean.Foundations.Program
