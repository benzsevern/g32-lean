import HodgeLean.Foundations.Program.SchoenCycleS3Cartier
import HodgeLean.Foundations.Program.SchoenCycleProjectiveChartMaps

/-! # The retained residue hyperplane has proper support -/
noncomputable section
set_option maxHeartbeats 200000
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexProjectiveSpace
namespace HodgeLean.Foundations.Program.G32Native
open HodgeLean.Foundations.Program

/-- The coordinate chart where the named residue is nonzero witnesses
properness of its hyperplane support, in every projective dimension.
Source: Hartshorne, Algebraic Geometry, II.2, standard projective charts. -/
theorem paired_c3_residue_support_proper (k : ℕ) (j : Fin (k + 1)) :
    (s2e_s2b_residueIdeal k j).support ≠ ⊤ := by
  intro h
  let A := MvPolynomial {q : Fin (k + 1) // q ≠ j} ℂ
  let x : Spec (CommRingCat.of A) := Classical.choice inferInstance
  have hx : s2e_s2b_chart j x ∈ projectiveSpaceBasicOpen k (MvPolynomial.X j) := by
    change s2e_s2b_chart j x ∈ (projectiveSpaceBasicOpen k (MvPolynomial.X j) : Set _)
    rw [← s2e_chart_range]
    exact ⟨x, rfl⟩
  have hy : s2e_s2b_chart j x ∈ (s2e_s2b_residueIdeal k j).support := by
    rw [h]
    trivial
  change s2e_s2b_chart j x ∈ ((s2e_s2b_residueIdeal k j).support : Set _) at hy
  rw [s2e_s2b_residueIdeal, Scheme.IdealSheafData.coe_support_vanishingIdeal] at hy
  exact hy hx

#print axioms paired_c3_residue_support_proper
end HodgeLean.Foundations.Program.G32Native
