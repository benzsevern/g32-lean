import HodgeLean.Foundations.Program.G32Native.EulerModel.NormalPointExcision

/-! # The global coclass of the specified projective normal zero -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
open CategoryTheory AlgebraicTopology.Singular HodgeLean.RealDefs
namespace HodgeLean.Foundations.Program.G32Native.EulerModel

/-- The actual point-support excision equivalence, retaining the specified affine chart. -/
def normalProjectivePointExcisionEquiv (k n : ℕ) :
    CohomologyWithSupport ℚ
      (TopCat.of (Projectivization ℂ (ℂ × (Fin k → ℂ)))) {normalProjectiveBase k} n ≃ₗ[ℚ]
        RelativeCohomology ℚ (puncturedPair ℂ k) n :=
  LinearEquiv.ofBijective (relativeCohomologyMap ℚ n (normalProjectiveChartPair k))
    (normalProjectiveChartPair_cohomology_bijective k n)

/-- The specified global projective point coclass obtained by actual open-chart excision. -/
def normalProjectivePointCoclass (k : ℕ) :
    CohomologyWithSupport ℚ
      (TopCat.of (Projectivization ℂ (ℂ × (Fin k → ℂ)))) {normalProjectiveBase k} (2 * k) :=
  (normalProjectivePointExcisionEquiv k (2 * k)).symm (normalizedPointCoclass k)

/-- The specified global projective point coclass has exactly the original affine point normalization. -/
theorem normalProjectivePointCoclass_chart (k : ℕ) :
    relativeCohomologyMap ℚ (2 * k) (normalProjectiveChartPair k)
      (normalProjectivePointCoclass k) = normalizedPointCoclass k :=
  (normalProjectivePointExcisionEquiv k (2 * k)).apply_symm_apply _

#print axioms normalProjectivePointExcisionEquiv
#print axioms normalProjectivePointCoclass
#print axioms normalProjectivePointCoclass_chart
/-- The actual global section's point-supported pullback is recovered uniquely from its specified local chart. -/
theorem projectiveNormalSection_supported_reconstruction (k n : ℕ)
    (α : CohomologyWithSupport ℚ (TopCat.of (ProjectiveNormalTotalSpace k))
      {v | v.1.2 = 0} n) :
    relativeCohomologyMap ℚ n (projectiveNormalSectionPairMap k) α =
      (normalProjectivePointExcisionEquiv k n).symm
        (relativeCohomologyMap ℚ n (normalKernelLocalSectionPairMap k)
          (relativeCohomologyMap ℚ n (normalKernelChartInclusionPair k) α)) := by
  apply (normalProjectivePointExcisionEquiv k n).injective
  rw [LinearEquiv.apply_symm_apply]
  exact normalKernelSection_chart_cohomology k n α

#print axioms projectiveNormalSection_supported_reconstruction
/-- The actual local fibre coclass localizes to the exact signed globally normalized projective point coclass. -/
theorem normalKernelLocalThomClass_global_sign (k : ℕ) :
    (normalProjectivePointExcisionEquiv k (2 * k)).symm
      (relativeCohomologyMap ℚ (2 * k) (normalKernelLocalSectionPairMap k)
        (normalKernelLocalThomClass k)) =
      (-1 : ℚ) ^ k • normalProjectivePointCoclass k := by
  rw [normalKernelLocalThomClass_section, map_smul]
  rfl

#print axioms normalKernelLocalThomClass_global_sign
end HodgeLean.Foundations.Program.G32Native.EulerModel
