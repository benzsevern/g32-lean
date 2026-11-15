import HodgeLean.Foundations.Program.G32Native.PairedResidualNoncontainment
import HodgeLean.Foundations.Program.G32Native.PairedResidualIdealTransport

/-! # The last-pair residue cannot replace a different distinguished residue -/

noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexProjectiveSpace
namespace HodgeLean.Foundations.Program.G32Native
open HodgeLean.Foundations.Program

/-- Different coordinate hyperplanes have different scheme ideals.
Source: Hartshorne, Algebraic Geometry, II.2, standard projective coordinates. -/
theorem paired_coordinate_residue_injective (k : ℕ) :
    Function.Injective (s2e_s2b_residueIdeal k) := by
  intro j t he
  by_contra hne
  let v : Fin (k + 1) → ℂ := Pi.single j 1
  have hj : v j ≠ 0 := by simp only [v, Pi.single_eq_same, ne_eq, one_ne_zero, not_false_eq_true]
  have hv : v ≠ 0 := fun h => hj (congrFun h j)
  let z : ProjectiveSpace (Fin (k + 1)) (Spec ↧ℂ) :=
    (vectorToComplexPoint v hv).underlying
  have hzj : z ∈ projectiveSpaceBasicOpen k (MvPolynomial.X j) :=
    (s2e_coordinatePoint_mem_chart v hv j).mpr hj
  have hzt : z ∉ projectiveSpaceBasicOpen k (MvPolynomial.X t) := by
    rw [s2e_coordinatePoint_mem_chart]
    simp only [v, Pi.single_eq_of_ne (Ne.symm hne), ne_eq, not_not]
  have hjn : z ∉ (s2e_s2b_residueIdeal k j).support := by
    change z ∉ ((s2e_s2b_residueIdeal k j).support :
      Set (ProjectiveSpace (Fin (k + 1)) (Spec ↧ℂ)))
    rw [s2e_s2b_residueIdeal, Scheme.IdealSheafData.coe_support_vanishingIdeal]
    exact fun h => h hzj
  have htm : z ∈ (s2e_s2b_residueIdeal k t).support := by
    change z ∈ ((s2e_s2b_residueIdeal k t).support :
      Set (ProjectiveSpace (Fin (k + 1)) (Spec ↧ℂ)))
    rw [s2e_s2b_residueIdeal, Scheme.IdealSheafData.coe_support_vanishingIdeal]
    exact hzt
  exact hjn (he.symm ▸ htm)

/-- The actual retained coefficient hyperplanes distinguish their pair indices.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.3(iv),
in the residue-coordinate parameter space. -/
theorem paired_coefficient_residue_injective
    (M : Type) [AddCommGroup M] [Module ℂ M] [FiniteDimensional ℂ M]
    (k r : ℕ) (hd : Module.finrank ℂ (M × (Fin r → ℂ)) = k + 1) :
    Function.Injective (residualCoefficientHyperplane M k r hd) := by
  obtain ⟨e, ι, he⟩ := residual_coefficient_hyperplanes_adapted M k r hd
  intro j t h
  apply ι.injective
  apply paired_coordinate_residue_injective k
  rw [← he j, ← he t, h]

/-- A single residual ideal with a specified pair restriction cannot also
have a different distinguished-pair restriction in the same coordinates.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.3(iv). -/
theorem paired_residual_restriction_determines_pair
    (M : Type) [AddCommGroup M] [Module ℂ M] [FiniteDimensional ℂ M]
    (k r : ℕ) (hd : Module.finrank ℂ (M × (Fin r → ℂ)) = k + 1)
    {V : Scheme} (i : ProjectiveSpace (Fin (k + 1)) (Spec ↧ℂ) ⟶ V)
    (J : V.IdealSheafData)
    (a : ProjectiveSpace (Fin (k + 1)) (Spec ↧ℂ) ≅
      ProjectiveSpace (Fin (k + 1)) (Spec ↧ℂ))
    (j t : Fin r)
    (hj : J.comap i = (residualCoefficientHyperplane M k r hd j).comap a.hom)
    (ht : J.comap i = (residualCoefficientHyperplane M k r hd t).comap a.hom) :
    j = t := by
  apply paired_coefficient_residue_injective M k r hd
  exact residual_ideal_comap_iso_injective a (hj.symm.trans ht)

#print axioms paired_coordinate_residue_injective
#print axioms paired_coefficient_residue_injective
#print axioms paired_residual_restriction_determines_pair

end HodgeLean.Foundations.Program.G32Native
