import HodgeLean.Foundations.AnalyticGermDimensionProofs

/-! # Analytic germ correspondence: frozen first primitives

Implication from Noetherian analytic local rings to a finite-generator zero-set
correspondence, and elementary reducedness and recovery for finite equations.
The analytic Nullstellensatz, geometric components, dimension comparison and
vertex extension are deferred. HC no distance; AV milestone no distance.
-/

noncomputable section
open Set Filter Topology
open HodgeLean.Foundations.AnalyticDivisorAlgebraic6
namespace HodgeLean.Foundations

/-- The finite-generator zero germ is right adjoint to vanishing, with reversed ideal order.
Source: Gunning--Rossi, III.A, vanishing ideals and zero germs. -/
theorem adim2_galois (n : ℕ) (S : adim2_SetGerm n)
    (I : Ideal (AnalyticGerm n)) :
    S ≤ adim2_zeroSet n I ↔ I ≤ adim2_ideal n S :=
  adim2_galois_aux n S I

/-- Vanishing ideals of arbitrary set germs are radical.
Source: Gunning--Rossi, III.A, reduced ideals of set germs. -/
theorem adim2_radical (n : ℕ) (S : adim2_SetGerm n) :
    (adim2_ideal n S).radical = adim2_ideal n S :=
  adim2_radical_aux n S

/-- A finite analytic zero germ is recovered from its vanishing ideal.
Source: Gunning--Rossi, III.A, recovery of analytic germs from their ideals. -/
theorem adim2_recovery (n : ℕ) (s : Finset (AnalyticGerm n)) :
    adim2_zeroSet n (adim2_ideal n (s.inf (adim2_zero n))) =
      s.inf (adim2_zero n) :=
  adim2_recovery_aux n s

/-- The coordinate zero germ lies in the zero germ of its squared equation.
Source: Gunning--Rossi, III.A, multiplicities do not change zero sets. -/
example : adim2_zero 1 (adim_coordinate 0) ≤
    adim2_zeroSet 1 (Ideal.span {adim_coordinate 0 ^ 2}) := by
  apply (adim2_galois 1 _ _).mpr
  apply Ideal.span_le.mpr
  intro f hf
  rcases Set.mem_singleton_iff.mp hf with rfl
  exact Ideal.pow_mem_of_mem _ (show adim_coordinate 0 ∈
    adim2_ideal 1 (adim2_zero 1 (adim_coordinate 0)) from (le_refl (adim2_zero 1 (adim_coordinate 0)))) 2 (by decide)

/-- A doubled coordinate equation still forces the coordinate itself to vanish.
Source: Gunning--Rossi, III.A, radicality of vanishing ideals. -/
example : adim_coordinate 0 ∈ adim2_ideal 1 (adim2_zero 1 (adim_coordinate 0 ^ 2)) := by
  rw [← adim2_radical]
  refine ⟨2, ?_⟩
  exact le_refl (adim2_zero 1 (adim_coordinate 0 ^ 2))

/-- Recovery for the doubled point equation constructs a nonempty proper analytic germ.
Source: Gunning--Rossi, III.A, the ideal and zero-set correspondence. -/
example : adim2_zeroSet 1 (adim2_ideal 1 (adim2_zero 1 (adim_coordinate 0 ^ 2))) =
    adim2_zero 1 (adim_coordinate 0 ^ 2) := by
  simpa using adim2_recovery 1 {adim_coordinate 0 ^ 2}

/-- An empty equation family recovers the full ambient germ, including dimension zero.
Source: Gunning--Rossi, III.A, the ideal and zero-set correspondence. -/
example : adim2_zeroSet 0 (adim2_ideal 0 ⊤) = ⊤ := by
  simpa using adim2_recovery 0 ∅

end HodgeLean.Foundations
