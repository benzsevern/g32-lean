import HodgeLean.Foundations.Program.SchoenTowerT11bDegreeStableTriviality
import HodgeLean.Foundations.Program.SchoenTowerT11bIntervals

/-! Polynomial sign compatibility along ordered real root sections.
HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

/-- A polynomial test has constant sign along a root section away from common-root values.
Source: Coste, Real Algebraic Sets (2005), Theorem 1.3, sign-invariant root-section step. -/
theorem s2v_t11b_root_section_sign (P Q : Polynomial (Polynomial ℝ))
    (hdegree : P.natDegree ≠ 0) (K : Set ℝ) (hK : IsPreconnected K)
    (ψ : K → ℝ) (hψ : Continuous ψ)
    (hroot : ∀ t : K, P.eval₂ (Polynomial.evalRingHom t.val) (ψ t) = 0)
    (hres : ∀ t ∈ K, (P.resultant Q).eval t ≠ 0) (a b : K) :
    0 ≤ Q.eval₂ (Polynomial.evalRingHom a.val) (ψ a) ↔
      0 ≤ Q.eval₂ (Polynomial.evalRingHom b.val) (ψ b) := by
  haveI : PreconnectedSpace K := isPreconnected_iff_preconnectedSpace.mp hK
  let g : K → ℝ := fun t => Q.eval₂ (Polynomial.evalRingHom t.val) (ψ t)
  have hg : Continuous g := (s2v_t11b_polynomial_family_contDiff Q).continuous.comp
    (continuous_subtype_val.prodMk hψ)
  apply s2v_t11b_nonzero_sign Set.univ isPreconnected_univ g hg.continuousOn ?_
    a b (Set.mem_univ a) (Set.mem_univ b)
  intro t _ ht
  exact hres t.val t.property (s2v_t11b_family_common_root_resultant P Q
    (Or.inl hdegree) t.val (ψ t) (hroot t) ht)

/-- An inequality on a simple real curve retains actual-fiber coordinates on a connected base.
Source: Coste, Real Algebraic Sets (2005), Theorem 1.3, sign-invariant root-section assembly step. -/
theorem s2v_t11b_simple_curve_nonneg_triviality
    (P Q : Polynomial (Polynomial ℝ)) (hdegree : P.natDegree ≠ 0)
    (K : Set ℝ) (hK : IsPreconnected K) (a : K)
    (hlead : ∀ t ∈ K, P.leadingCoeff.eval t ≠ 0)
    (hsimple : ∀ t ∈ K, ∀ x : ℝ, P.eval₂ (Polynomial.evalRingHom t) x = 0 →
      (P.map (Polynomial.evalRingHom t)).derivative.eval x ≠ 0)
    (hres : ∀ t ∈ K, (P.resultant Q).eval t ≠ 0) :
    ∃ e : ({x : ℝ | P.eval₂ (Polynomial.evalRingHom a.val) x = 0 ∧
        0 ≤ Q.eval₂ (Polynomial.evalRingHom a.val) x} × K) ≃ₜ
      {z : K × ℝ | P.eval₂ (Polynomial.evalRingHom z.1.val) z.2 = 0 ∧
        0 ≤ Q.eval₂ (Polynomial.evalRingHom z.1.val) z.2},
      ∀ y, (e y).val.1 = y.2 := by
  classical
  obtain ⟨m, ψ, hc, hmono, hroots⟩ :=
    s2v_t11b_ordered_sections_on_preconnected_of_leadingCoeff P K hK a hlead hsimple
  have hsign : ∀ i (t : K),
      0 ≤ Q.eval₂ (Polynomial.evalRingHom t.val) (ψ i t) ↔
        0 ≤ Q.eval₂ (Polynomial.evalRingHom a.val) (ψ i a) := fun i t =>
    s2v_t11b_root_section_sign P Q hdegree K hK (ψ i) (hc i)
      (fun u => (hroots u _).mpr ⟨i, rfl⟩) hres t a
  let J := {i : Fin m // 0 ≤ Q.eval₂ (Polynomial.evalRingHom a.val) (ψ i a)}
  let E : Fin (Fintype.card J) ≃ J := (Fintype.equivFin J).symm
  let θ : Fin (Fintype.card J) → K → ℝ := fun i => ψ (E i).val
  have hθ : ∀ i, Continuous (θ i) := fun i => hc (E i).val
  have hinj : ∀ t, Function.Injective (fun i => θ i t) := by
    intro t i j hij
    exact E.injective (Subtype.ext ((hmono t).injective hij))
  have hcover : ∀ t : K, ∀ x : ℝ,
      (P.eval₂ (Polynomial.evalRingHom t.val) x = 0 ∧
        0 ≤ Q.eval₂ (Polynomial.evalRingHom t.val) x) ↔ ∃ i, x = θ i t := by
    intro t x
    constructor
    · rintro ⟨hp, hq⟩
      obtain ⟨i, hi⟩ := (hroots t x).mp hp
      have hqi : 0 ≤ Q.eval₂ (Polynomial.evalRingHom a.val) (ψ i a) :=
        (hsign i t).mp (hi ▸ hq)
      let j : J := ⟨i, hqi⟩
      refine ⟨E.symm j, ?_⟩
      simpa only [θ, E.apply_symm_apply] using hi
    · rintro ⟨i, rfl⟩
      exact ⟨(hroots t _).mpr ⟨(E i).val, rfl⟩, (hsign (E i).val t).mpr (E i).property⟩
  let R := {x : ℝ | P.eval₂ (Polynomial.evalRingHom a.val) x = 0 ∧
    0 ≤ Q.eval₂ (Polynomial.evalRingHom a.val) x}
  let idx : Fin (Fintype.card J) → R := fun i => ⟨θ i a, (hcover a _).mpr ⟨i, rfl⟩⟩
  have hidx : Function.Bijective idx := by
    constructor
    · intro i j hij
      exact hinj a (congrArg Subtype.val hij)
    · intro x
      obtain ⟨i, hi⟩ := (hcover a x.val).mp x.property
      exact ⟨i, Subtype.ext hi.symm⟩
  let rootEquiv : Fin (Fintype.card J) ≃ₜ R :=
    (Equiv.ofBijective idx hidx).toHomeomorphOfContinuousClosed
      continuous_of_discreteTopology (fun A _ => ((Set.toFinite A).image idx).isClosed)
  have hsets : {z : K × ℝ | ∃ i, z.2 = θ i z.1} =
      {z : K × ℝ | P.eval₂ (Polynomial.evalRingHom z.1.val) z.2 = 0 ∧
        0 ≤ Q.eval₂ (Polynomial.evalRingHom z.1.val) z.2} := by
    ext z
    exact (hcover z.1 z.2).symm
  let e := ((rootEquiv.symm.prodCongr (Homeomorph.refl K)).trans
    (s2v_t11b_finite_graph_homeomorph θ hθ hinj)).trans (Homeomorph.setCongr hsets)
  refine ⟨e, ?_⟩
  intro y
  exact congrArg Prod.fst
    (s2v_t11b_finite_graph_homeomorph_apply θ hθ hinj (rootEquiv.symm y.1) y.2)

end HodgeLean.Foundations.Program
