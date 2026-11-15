import HodgeLean.Foundations.Program.G32Native.EulerModel.NormalKernelSupportedComplex

/-! # Exact sheaf gluing for the original kernel relative cohomology -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open AlgebraicTopology.Singular CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open TopCat.Sheaf
namespace HodgeLean.Foundations.Program.G32Native.EulerModel

/-- Relative cohomology in the actual complex-normal degree is already a sheaf on the original kernel total space. -/
theorem normalKernelRelativeCohomology_isSheaf (k : ℕ) :
    CategoryTheory.Presheaf.IsSheaf
      (Opens.grothendieckTopology (ProjectiveNormalTotalSpace k))
      (supportRelativeCohomologyPresheaf (TopCat.of (ProjectiveNormalTotalSpace k))
        {w | w.1.2 = 0} (2 * k)) := by
  let X := TopCat.of (ProjectiveNormalTotalSpace k)
  let K := normalKernelSupportedSingularComplex k
  letI : T2Space X := normalKernelTotalSpace_t2Space k
  letI (V : Opens X) : ParacompactSpace V := normalKernelTotalSpace_openParacompact k V
  letI : K.IsStrictlyGE 0 := normalKernelSupportedSingularComplex_isStrictlyGE k
  have hK : ∀ j : ℤ, j < (2 * k : ℕ) → IsZero (K.homology j) := by
    intro j hj
    by_cases hneg : j < 0
    · apply ShortComplex.isZero_homology_of_isZero_X₂
      exact K.isZero_of_isStrictlyGE 0 j hneg
    · obtain ⟨j, rfl⟩ := Int.eq_ofNat_of_zero_le (le_of_not_gt hneg)
      exact normalKernelSupportedSingularComplex_homology_isZero_of_ne k j (by omega)
  have hF : ∀ j : ℤ, (K.X j).IsFlasque := by
    intro j
    exact sheafSectionsSupportedOutside_isFlasque X
      ⟨{w : ProjectiveNormalTotalSpace k | w.1.2 = 0}ᶜ,
        (isClosed_normalKernelZeroSection k).isOpen_compl⟩
      ((rationalSingularCochainComplex X).X j)
  haveI : IsIso (sectionCohomologyPresheafToSheaf X K ((2 * k : ℕ) : ℤ)) := by
    haveI (U : (Opens X)ᵒᵖ) :
        IsIso ((sectionCohomologyPresheafToSheaf X K ((2 * k : ℕ) : ℤ)).app U) := by
      letI := sectionCohomologyToSheafSection_isIso_lowest X K 0 ((2 * k : ℕ) : ℤ) hK hF U.unop
      have heq : (sectionCohomologyPresheafToSheaf X K ((2 * k : ℕ) : ℤ)).app U =
          (sectionCohomologyPresheafOnOpenIso X K ((2 * k : ℕ) : ℤ) U.unop).inv ≫
            sectionCohomologyToSheafSection X K ((2 * k : ℕ) : ℤ) U.unop := by
        simp [sectionCohomologyToSheafSection]
      rw [heq]
      infer_instance
    exact NatIso.isIso_of_isIso_app _
  have hP := (CategoryTheory.Presheaf.isSheaf_of_iso_iff
    (asIso (sectionCohomologyPresheafToSheaf X K ((2 * k : ℕ) : ℤ)))).mpr (K.homology ((2 * k : ℕ) : ℤ)).property
  exact (CategoryTheory.Presheaf.isSheaf_of_iso_iff
    (supportedSingularCohomologyPresheafIsoRelative X {w | w.1.2 = 0}
      (isClosed_normalKernelZeroSection k) (2 * k))).mp hP

#print axioms normalKernelRelativeCohomology_isSheaf
end HodgeLean.Foundations.Program.G32Native.EulerModel
