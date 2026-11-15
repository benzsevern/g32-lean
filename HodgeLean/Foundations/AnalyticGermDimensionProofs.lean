import HodgeLean.Foundations.AnalyticGermDimensionDefs

/-! # Proof obligations for the analytic germ correspondence

HC no distance; AV milestone no distance.
-/

noncomputable section
open Set Filter Topology
open HodgeLean.Foundations.AnalyticDivisorAlgebraic6
namespace HodgeLean.Foundations

/-- Source: Gunning--Rossi, III.A, vanishing ideals and zero germs. -/
theorem adim2_galois_aux (n : ℕ) (S : adim2_SetGerm n)
    (I : Ideal (AnalyticGerm n)) :
    S ≤ adim2_zeroSet n I ↔ I ≤ adim2_ideal n S := by
  have hspan : Ideal.span (adim2_generators n I : Set (AnalyticGerm n)) = I :=
    ((isNoetherianRing_iff_ideal_fg _).mp (adim_noetherian n) I).choose_spec
  constructor
  · intro h
    rw [← hspan]
    apply Ideal.span_le.mpr
    intro f hf
    exact h.trans (Finset.inf_le hf)
  · intro h
    apply Finset.le_inf
    intro f hf
    apply h
    rw [← hspan]
    exact Ideal.subset_span hf

/-- Source: Gunning--Rossi, III.A, reduced ideals of set germs. -/
theorem adim2_radical_aux (n : ℕ) (S : adim2_SetGerm n) :
    (adim2_ideal n S).radical = adim2_ideal n S := by
  rw [Ideal.radical_eq_iff]
  rintro f ⟨k, hk⟩
  obtain ⟨f, hf, ef⟩ := f.property
  change S ≤ Filter.Germ.map (· = 0) (_ ^ k) at hk
  change S ≤ Filter.Germ.map (· = 0) _
  rw [← ef] at hk ⊢
  induction S using Filter.Germ.inductionOn with | h s =>
    change ∀ᶠ z in nhds (0 : Fin n → ℂ), s z → f z ^ k = 0 at hk
    change ∀ᶠ z in nhds (0 : Fin n → ℂ), s z → f z = 0
    filter_upwards [hk] with z hz hs
    exact eq_zero_of_pow_eq_zero (hz hs)

/-- Source: Gunning--Rossi, III.A, recovery of analytic germs from their ideals. -/
theorem adim2_recovery_aux (n : ℕ) (s : Finset (AnalyticGerm n)) :
    adim2_zeroSet n (adim2_ideal n (s.inf (adim2_zero n))) =
      s.inf (adim2_zero n) := by
  apply le_antisymm
  · apply Finset.le_inf
    intro f hf
    have hself := (show adim2_zeroSet n (adim2_ideal n (s.inf (adim2_zero n))) ≤
        adim2_zeroSet n (adim2_ideal n (s.inf (adim2_zero n))) from le_rfl)
    have hideal := (adim2_galois_aux n _ _).mp hself
    apply hideal
    exact (show s.inf (adim2_zero n) ≤ adim2_zero n f from Finset.inf_le hf)
  · apply (adim2_galois_aux n _ _).mpr
    exact le_rfl

end HodgeLean.Foundations
