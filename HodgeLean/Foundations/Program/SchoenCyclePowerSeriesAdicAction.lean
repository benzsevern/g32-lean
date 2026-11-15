import HodgeLean.Foundations.Program.SchoenCycleAdicPermutation
import Mathlib.RingTheory.MvPowerSeries.Equiv
import Mathlib.RingTheory.MvPowerSeries.Rename

/-! # Formal coordinate permutations and adic coordinates -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

/-- Finite total-degree truncation commutes with permutation of coordinates.
Source: Bourbaki, Commutative Algebra, Chapter III, §2;
Mathlib, MvPowerSeries.coeff_truncTotal_eq_ite. -/
theorem s2e_powerSeries_truncTotal_rename
    {R σ : Type*} [CommRing R] [Finite σ] (e : Equiv.Perm σ)
    (p : MvPowerSeries σ R) (N : ℕ) :
    MvPowerSeries.truncTotal N (MvPowerSeries.rename e p) =
      MvPolynomial.rename e (MvPowerSeries.truncTotal N p) := by
  classical
  ext d
  obtain ⟨d, rfl⟩ := Finsupp.mapDomain_surjective e.surjective d
  rw [MvPolynomial.coeff_rename_mapDomain e e.injective,
    MvPowerSeries.coeff_truncTotal_eq_ite, Finsupp.degree_mapDomain,
    MvPowerSeries.coeff_truncTotal_eq_ite]
  congr 1
  simpa only [Finsupp.embDomain_eq_mapDomain, Equiv.coe_toEmbedding] using
    MvPowerSeries.coeff_embDomain_rename e.toEmbedding p d

#print axioms s2e_powerSeries_truncTotal_rename
/-- The canonical formal-series to adic equivalence intertwines coordinate
permutations on all series.
Source: Bourbaki, Commutative Algebra, Chapter III, §2;
Mathlib, MvPowerSeries.toAdicCompletion. -/
theorem s2e_powerSeries_toAdic_rename
    {σ : Type*} [Finite σ] (e : Equiv.Perm σ) (p : MvPowerSeries σ ℂ) :
    MvPowerSeries.toAdicCompletion σ ℂ (MvPowerSeries.rename e p) =
      s2e_polynomial_adic_rename e (MvPowerSeries.toAdicCompletion σ ℂ p) := by
  apply AdicCompletion.ext_evalₐ
  intro N
  unfold s2e_polynomial_adic_rename
  rw [s2e_adic_ring_map_eval]
  change Ideal.Quotient.mk _ (MvPowerSeries.truncTotal N (MvPowerSeries.rename e p)) =
    Ideal.Quotient.mk _ (MvPolynomial.rename e (MvPowerSeries.truncTotal N p))
  rw [s2e_powerSeries_truncTotal_rename]

#print axioms s2e_powerSeries_toAdic_rename
end HodgeLean.Foundations.Program
