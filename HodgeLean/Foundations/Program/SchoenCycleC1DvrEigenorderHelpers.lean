import HodgeLean.Foundations.Program.SchoenCycleC1LocalEigenorderHelpers
import HodgeLean.Foundations.Program.SchoenCycleC1LocalResidueHelpers
import Mathlib.RingTheory.DiscreteValuationRing.Basic

/-! # Rational eigencharacters in actual discrete valuation local rings -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

/-- A DVR automorphism and a nonzero rational eigenfunction supply their
parameter multiplier and signed order, retaining its exact residue character. -/
theorem s2e_c1_dvr_rational_eigenorder_character
    {k R K : Type*} [Field k] [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Field K] [Algebra k R] [Algebra R K] [Algebra k K] [IsScalarTower k R K]
    [IsFractionRing R K]
    (φ : R →ₐ[k] k) (τ : R ≃ₐ[k] R) (σ : K ≃ₐ[k] K)
    (hσ : ∀ r : R, σ (algebraMap R K r) = algebraMap R K (τ r))
    (t : R) (ht : Irreducible t) (z : K) (hz : z ≠ 0)
    (η : k) (heig : σ z = algebraMap k K η * z) :
    ∃ (v u : Rˣ) (n : ℤ), τ t = t * (v : R) ∧
      z = algebraMap R K (u : R) * algebraMap R K t ^ n ∧ φ (v : R) ^ n = η := by
  have hτ : Irreducible (τ t) := (MulEquiv.irreducible_iff τ.toMulEquiv).mpr ht
  obtain ⟨v, hv⟩ := IsDiscreteValuationRing.associated_of_irreducible R ht hτ
  have hτt : τ t = t * (v : R) := hv.symm
  have hex : ∃ n : ℤ, ∃ u : Rˣ,
      z = algebraMap R K (u : R) * algebraMap R K t ^ n := by
    simpa only [Units.smul_def, Algebra.smul_def] using
      IsDiscreteValuationRing.exists_units_eq_smul_zpow_of_irreducible ht hz
  obtain ⟨n, u, hu⟩ := hex
  have htK : algebraMap R K t ≠ 0 := by
    simpa only [map_zero] using (IsFractionRing.injective R K).ne ht.ne_zero
  exact ⟨v, u, n, hτt, hu,
    s2e_c1_local_rational_eigenorder_character φ τ σ hσ (s2e_c1_local_residue_fixed_by_algebraEquiv φ τ) t htK v u hτt z n hu η heig⟩

end HodgeLean.Foundations.Program
