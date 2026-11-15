import HodgeLean.Foundations.Program.G32Native.PairedResidualAdaptedCoordinates
import HodgeLean.Foundations.Program.SchoenCycleResidueProjectivePoints

/-! # Actual residue hyperplanes and residual noncontainment -/

noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexProjectiveSpace
namespace HodgeLean.Foundations.Program.G32Native
open HodgeLean.Foundations.Program

/-- Every actual residue hyperplane misses an actual point of the fixed projective parameter scheme. -/
theorem residual_coefficient_hyperplane_proper
    (M : Type) [AddCommGroup M] [Module ℂ M] [FiniteDimensional ℂ M]
    (k r : ℕ) (hd : Module.finrank ℂ (M × (Fin r → ℂ)) = k + 1) (j : Fin r) :
    ∃ x : ProjectiveSpace (Fin (k + 1)) (Spec ↧ℂ),
      x ∉ (residualCoefficientHyperplane M k r hd j).support := by
  obtain ⟨e, ι, he⟩ := residual_coefficient_hyperplanes_adapted M k r hd
  let v : Fin (k + 1) → ℂ := Pi.single (ι j) 1
  have hi : v (ι j) ≠ 0 := by simp [v]
  have hv : v ≠ 0 := by
    intro h
    exact hi (congrFun h (ι j))
  let z : ProjectiveSpace (Fin (k + 1)) (Spec ↧ℂ) := (vectorToComplexPoint v hv).underlying
  have hz : z ∈ projectiveSpaceBasicOpen k (MvPolynomial.X (ι j)) :=
    (s2e_coordinatePoint_mem_chart v hv (ι j)).mpr hi
  have hn : z ∉ (s2e_s2b_residueIdeal k (ι j)).support := by
    change z ∉ ((s2e_s2b_residueIdeal k (ι j)).support : Set (ProjectiveSpace (Fin (k + 1)) (Spec ↧ℂ)))
    rw [s2e_s2b_residueIdeal, Scheme.IdealSheafData.coe_support_vanishingIdeal]
    exact fun h => h hz
  have hn' : z ∉ ((residualCoefficientHyperplane M k r hd j).comap e.hom.left).support := by
    rwa [he j]
  refine ⟨e.hom.left z, ?_⟩
  intro hx
  apply hn'
  rw [Scheme.IdealSheafData.support_comap]
  exact hx

/-- A proper pulled ideal prevents the image-kernel support from lying in the original ideal support. -/
theorem residual_noncontainment_of_pullback
    {P V : Scheme} (i : P ⟶ V) (J : V.IdealSheafData) (K : P.IdealSheafData)
    (h : J.comap i = K) (hproper : ∃ x : P, x ∉ K.support) :
    ¬ (i.ker.support : Set V) ⊆ J.support := by
  intro hsub
  obtain ⟨x, hx⟩ := hproper
  have hi : i x ∈ i.ker.support := i.range_subset_ker_support ⟨x, rfl⟩
  have hj := hsub hi
  apply hx
  rw [← h, Scheme.IdealSheafData.support_comap]
  exact hj

#print axioms residual_noncontainment_of_pullback
#print axioms residual_coefficient_hyperplane_proper
end HodgeLean.Foundations.Program.G32Native
