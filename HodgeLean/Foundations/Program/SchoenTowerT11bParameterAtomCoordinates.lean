import HodgeLean.Foundations.Program.SchoenTowerT11bParameterDivisorSections
import HodgeLean.Foundations.Program.SchoenTowerT11bAmbientSubsetCoordinates

/-! Atom signs on normalized sections and intervening bands over arbitrary connected bases.
HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace HodgeLean.Foundations.Program
open UniqueFactorizationMonoid

/-- A carrier divisor has constant sign at every normalized height, on root graphs and on the intervening bands.
Source: Coste, Real Algebraic Sets (2005), Theorem 1.3, parameter graph-and-band compatibility step. -/
theorem s2v_t11b_parameter_atom_sign_at_normalized_height {A X : Type*}
    [CommRing A] [IsDomain A] [NormalizationMonoid (Polynomial A)]
    [UniqueFactorizationMonoid (Polynomial A)] [TopologicalSpace X] [PreconnectedSpace X]
    (φ : X → A →+* ℝ) (hφ : ∀ c, Continuous (fun t => φ t c))
    (P Q : Polynomial A) (hP : P ≠ 0) (hQ : Q ≠ 0) (hdiv : Q ∣ P)
    {m : ℕ} (ψ : Fin m → X → ℝ)
    (hroots : ∀ t x, (radical P).eval₂ (φ t) x = 0 ↔ ∃ i, x = ψ i t)
    (hsimple : ∀ t x, (radical P).eval₂ (φ t) x = 0 →
      ((radical P).map (φ t)).derivative.eval x ≠ 0)
    (E : (X × ℝ) ≃ₜ (X × ℝ)) (hbase : ∀ z, (E z).1 = z.1)
    (hEroots : ∀ t i, E (t, ψ i t) = (t, (i.val : ℝ) + 1)) (r : ℝ) (a b : X) :
    0 ≤ Q.eval₂ (φ a) (E.symm (a, r)).2 ↔
      0 ≤ Q.eval₂ (φ b) (E.symm (b, r)).2 := by
  classical
  let χ : X → ℝ := fun t => (E.symm (t, r)).2
  have hχ : Continuous χ := (continuous_snd.comp E.symm.continuous).comp
    (continuous_id.prodMk continuous_const)
  by_cases hr : ∃ i : Fin m, r = (i.val : ℝ) + 1
  · obtain ⟨i, hi⟩ := hr
    have hsection : ∀ t, χ t = ψ i t := by
      intro t
      have h := congrArg E.symm (hEroots t i)
      rw [E.symm_apply_apply] at h
      change (E.symm (t, r)).2 = ψ i t
      rw [hi]
      exact (congrArg Prod.snd h).symm
    have hz : ∀ t, (radical P).eval₂ (φ t) (χ t) = 0 := by
      intro t
      exact (hroots t _).mpr ⟨i, hsection t⟩
    exact s2v_t11b_parameter_radical_atom_sign φ hφ P Q hP hQ hdiv χ hχ hz
      (fun t => hsimple t (χ t) (hz t)) a b
  · have hnonzero : ∀ t, P.eval₂ (φ t) (χ t) ≠ 0 := by
      intro t ht
      obtain ⟨i, hi⟩ := (hroots t (χ t)).mp
        ((s2v_t11b_radical_map_zero_iff (Polynomial.eval₂RingHom (φ t) (χ t)) P hP).mpr ht)
      have h := s2v_t11b_ambient_inverse_section E hbase t r
      change E (t, χ t) = (t, r) at h
      rw [hi, hEroots t i] at h
      exact hr ⟨i, (congrArg Prod.snd h).symm⟩
    let g : X → ℝ := fun t => Q.eval₂ (φ t) (χ t)
    have hg : Continuous g := s2v_t11b_ringHom_family_section_continuous φ hφ Q χ hχ
    apply s2v_t11b_nonzero_sign Set.univ isPreconnected_univ g hg.continuousOn ?_
      a b (Set.mem_univ a) (Set.mem_univ b)
    intro t _ ht
    apply hnonzero t
    obtain ⟨G, hPG⟩ := hdiv
    rw [hPG, Polynomial.eval₂_mul]
    change g t * _ = 0
    rw [ht, zero_mul]

end HodgeLean.Foundations.Program
