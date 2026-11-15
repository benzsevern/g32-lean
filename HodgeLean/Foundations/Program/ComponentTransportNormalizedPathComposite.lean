import HodgeLean.Foundations.Program.ComponentTransportNormalizedPathAffineIsotopy

/-! # Ambient comparison motions -/
noncomputable section
open Set Topology
namespace HodgeLean.Foundations.Program

/-- Compose a correction motion with the inverses of certified and word motions.
Source: `rtc_family_inverse`; composition of homeomorphisms. -/
theorem rtc_composite_motion
    (F H D : C(unitInterval × OnePoint ℂ, OnePoint ℂ))
    (hF : ∀ t, Function.Bijective (fun z ↦ F (t, z)))
    (hH : ∀ t, Function.Bijective (fun z ↦ H (t, z)))
    (hD : ∀ t, Function.Bijective (fun z ↦ D (t, z)))
    (hF0 : ∀ z, F (0, z) = z) (hH0 : ∀ z, H (0, z) = z)
    (hD0 : ∀ z, D (0, z) = z)
    (hFI : ∀ t, F (t, OnePoint.infty) = OnePoint.infty)
    (hHI : ∀ t, H (t, OnePoint.infty) = OnePoint.infty)
    (hDI : ∀ t, D (t, OnePoint.infty) = OnePoint.infty)
    (E W : OnePoint ℂ ≃ₜ OnePoint ℂ)
    (hFE : ∀ z, F (1, z) = E z) (hHW : ∀ z, H (1, z) = W z) :
    ∃ C : C(unitInterval × OnePoint ℂ, OnePoint ℂ),
      (∀ t, Function.Bijective (fun z ↦ C (t, z))) ∧
      (∀ z, C (0, z) = z) ∧
      (∀ t, C (t, OnePoint.infty) = OnePoint.infty) ∧
      (∀ z, C (1, z) = D (1, E.symm (W.symm z))) := by
  obtain ⟨U, hU⟩ := rtc_family_inverse F hF
  obtain ⟨V, hV⟩ := rtc_family_inverse H hH
  have hUb (t : unitInterval) : Function.Bijective (fun z ↦ U (t, z)) := by
    constructor
    · intro x y h
      simpa only [(hU t x).1, (hU t y).1] using congrArg (fun z ↦ F (t, z)) h
    · intro z
      exact ⟨F (t, z), (hU t z).2⟩
  have hVb (t : unitInterval) : Function.Bijective (fun z ↦ V (t, z)) := by
    constructor
    · intro x y h
      simpa only [(hV t x).1, (hV t y).1] using congrArg (fun z ↦ H (t, z)) h
    · intro z
      exact ⟨H (t, z), (hV t z).2⟩
  let C : C(unitInterval × OnePoint ℂ, OnePoint ℂ) :=
    ⟨fun q ↦ D (q.1, U (q.1, V q)), D.continuous.comp
      (continuous_fst.prodMk (U.continuous.comp (continuous_fst.prodMk V.continuous)))⟩
  refine ⟨C, fun t ↦ (hD t).comp ((hUb t).comp (hVb t)), ?_, ?_, ?_⟩
  · intro z
    have hu : U (0, z) = z := by simpa only [hF0] using (hU 0 z).1
    have hv : V (0, z) = z := by simpa only [hH0] using (hV 0 z).1
    change D (0, U (0, V (0, z))) = z
    rw [hv, hu, hD0]
  · intro t
    have hu : U (t, OnePoint.infty) = OnePoint.infty :=
      (hF t).1 ((hU t OnePoint.infty).1.trans (hFI t).symm)
    have hv : V (t, OnePoint.infty) = OnePoint.infty :=
      (hH t).1 ((hV t OnePoint.infty).1.trans (hHI t).symm)
    change D (t, U (t, V (t, OnePoint.infty))) = OnePoint.infty
    rw [hv, hu, hDI]
  · intro z
    have hu (w) : U (1, w) = E.symm w := by
      apply E.injective
      rw [E.apply_symm_apply, ← hFE]
      exact (hU 1 w).1
    have hv (w) : V (1, w) = W.symm w := by
      apply W.injective
      rw [W.apply_symm_apply, ← hHW]
      exact (hV 1 w).1
    change D (1, U (1, V (1, z))) = _
    rw [hv, hu]

/-- An infinity-fixing ambient motion has continuous finite ordered tracks.
Source: Mathlib `OnePoint.ne_infty_iff_exists`; its coercion is an open embedding. -/
theorem rtc_finite_ambient_tracks {n : ℕ} (q : Fin n → ℂ) (hq : Function.Injective q)
    (C : C(unitInterval × OnePoint ℂ, OnePoint ℂ))
    (hC : ∀ t, Function.Injective (fun z ↦ C (t, z)))
    (hCI : ∀ t, C (t, OnePoint.infty) = OnePoint.infty) :
    ∃ P : C(unitInterval, Fin n → ℂ), (∀ t, Function.Injective (P t)) ∧
      ∀ t k, (P t k : OnePoint ℂ) = C (t, (q k : OnePoint ℂ)) := by
  have hex (t : unitInterval) (k : Fin n) :
      ∃ z : ℂ, (z : OnePoint ℂ) = C (t, (q k : OnePoint ℂ)) := by
    apply OnePoint.ne_infty_iff_exists.mp
    intro h
    exact OnePoint.coe_ne_infty _ ((hC t) (h.trans (hCI t).symm))
  let P₀ : unitInterval → Fin n → ℂ := fun t k ↦ Classical.choose (hex t k)
  have hP (t : unitInterval) (k : Fin n) :
      (P₀ t k : OnePoint ℂ) = C (t, (q k : OnePoint ℂ)) := Classical.choose_spec (hex t k)
  have hc : Continuous P₀ := by
    apply continuous_pi
    intro k
    apply OnePoint.isOpenEmbedding_coe.isInducing.continuous_iff.mpr
    change Continuous (fun t ↦ (P₀ t k : OnePoint ℂ))
    simp_rw [hP]
    exact C.continuous.comp (continuous_id.prodMk continuous_const)
  refine ⟨⟨P₀, hc⟩, ?_, hP⟩
  intro t i j h
  apply hq
  apply OnePoint.coe_injective
  apply hC t
  change C (t, (q i : OnePoint ℂ)) = C (t, (q j : OnePoint ℂ))
  rw [← hP, ← hP]
  exact congrArg ((↑) : ℂ → OnePoint ℂ) h

end HodgeLean.Foundations.Program
