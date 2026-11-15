import HodgeLean.Foundations.Program.SchoenTowerT11bContainedSections
import HodgeLean.Foundations.Program.SchoenTowerT11bAmbientSubsetCoordinates

/-! Graph-and-band atom signs from finite continuous root arrangements.
HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

/-- Continuous contained atom-root enumerations retain signs at every normalized height, including all graph and band coordinates.
Source: Coste, Real Algebraic Sets (2005), Theorem 1.3, enumerated graph-and-band compatibility step. -/
theorem s2v_t11b_enumerated_atom_normalized_sign {X : Type*}
    [TopologicalSpace X] [PreconnectedSpace X] {m r : ℕ}
    (ψ : Fin m → X → ℝ) (hψ : ∀ i, Continuous (ψ i))
    (hinj : ∀ t, Function.Injective (fun i => ψ i t))
    (F : X → ℝ → ℝ) (hF : Continuous (fun z : X × ℝ => F z.1 z.2))
    (χ : Fin r → X → ℝ) (hχ : ∀ i, Continuous (χ i))
    (hroots : ∀ t x, F t x = 0 ↔ ∃ i, x = χ i t)
    (hcontained : ∀ t x, F t x = 0 → ∃ i, x = ψ i t)
    (E : (X × ℝ) ≃ₜ (X × ℝ)) (hbase : ∀ z, (E z).1 = z.1)
    (hEroots : ∀ t i, E (t, ψ i t) = (t, (i.val : ℝ) + 1)) (s : ℝ) (a b : X) :
    0 ≤ F a (E.symm (a, s)).2 ↔ 0 ≤ F b (E.symm (b, s)).2 := by
  let η : X → ℝ := fun t => (E.symm (t, s)).2
  have hη : Continuous η := (continuous_snd.comp E.symm.continuous).comp
    (continuous_id.prodMk continuous_const)
  by_cases hs : ∃ i : Fin m, s = (i.val : ℝ) + 1
  · obtain ⟨i, hi⟩ := hs
    have he : ∀ t, η t = ψ i t := by
      intro t
      have h := congrArg E.symm (hEroots t i)
      rw [E.symm_apply_apply] at h
      change (E.symm (t, s)).2 = ψ i t
      rw [hi]
      exact (congrArg Prod.snd h).symm
    change 0 ≤ F a (η a) ↔ 0 ≤ F b (η b)
    rw [he a, he b]
    exact s2v_t11b_enumerated_atom_sign ψ hψ hinj F hF χ hχ hroots hcontained i a b
  · have hn : ∀ t, F t (η t) ≠ 0 := by
      intro t ht
      obtain ⟨i, hi⟩ := hcontained t (η t) ht
      have h := s2v_t11b_ambient_inverse_section E hbase t s
      change E (t, η t) = (t, s) at h
      rw [hi, hEroots t i] at h
      exact hs ⟨i, (congrArg Prod.snd h).symm⟩
    exact s2v_t11b_nonzero_sign Set.univ isPreconnected_univ (fun t => F t (η t))
      (hF.comp (continuous_id.prodMk hη)).continuousOn (fun t _ => hn t)
      a b (Set.mem_univ a) (Set.mem_univ b)

end HodgeLean.Foundations.Program
