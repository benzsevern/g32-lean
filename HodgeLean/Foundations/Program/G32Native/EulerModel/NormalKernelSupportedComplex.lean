import HodgeLean.Foundations.Program.G32Native.EulerModel.NormalKernelOpenTopology
import HodgeLean.Foundations.Program.G32Native.EulerModel.NormalKernelLocalPurity
import HodgeConjecture.Definitions.AlgebraicTopology.Support.SingularCohomologySheafComparison
import HodgeConjecture.Lemmas.AlgebraicTopology.Sheaf.CohomologyStalkVanishing
import HodgeConjecture.Definitions.AlgebraicTopology.Sheaf.FlasqueLowestCohomology

/-! # The actual supported singular cochain complex of the kernel zero section -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open AlgebraicTopology.Singular CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
namespace HodgeLean.Foundations.Program.G32Native.EulerModel

/-- The singular cochain sheaf complex supported on precisely the original kernel zero vectors. -/
def normalKernelSupportedSingularComplex (k : ℕ) :
    CochainComplex (TopCat.Sheaf AddCommGrpCat (TopCat.of (ProjectiveNormalTotalSpace k))) ℤ :=
  supportedRationalSingularCochainComplex (TopCat.of (ProjectiveNormalTotalSpace k))
    ⟨{w : ProjectiveNormalTotalSpace k | w.1.2 = 0}ᶜ,
      (isClosed_normalKernelZeroSection k).isOpen_compl⟩

#print axioms normalKernelSupportedSingularComplex
/-- The actual supported singular complex has zero cohomology sheaves off the complex normal degree. -/
theorem normalKernelSupportedSingularComplex_homology_isZero_of_ne (k n : ℕ)
    (hn : n ≠ 2 * k) : IsZero ((normalKernelSupportedSingularComplex k).homology (n : ℤ)) := by
  letI := normalKernelTotalSpace_t2Space k
  letI (V : Opens (ProjectiveNormalTotalSpace k)) : ParacompactSpace V :=
    normalKernelTotalSpace_openParacompact k V
  apply TopCat.Sheaf.cohomologySheaf_isZero_of_cofinal_sections
    (TopCat.of (ProjectiveNormalTotalSpace k)) (normalKernelSupportedSingularComplex k) (n : ℤ)
  intro v U hvU
  obtain ⟨W, hWU, hvW, hW⟩ := normalKernelZeroSupport_exists_relativeCohomology_vanishing k v U hvU
  refine ⟨W, hWU, hvW, ?_⟩
  letI := ModuleCat.subsingleton_of_isZero (hW n hn)
  let e := supportedRationalSingularSectionCohomologyEquivSupportComplement
    (TopCat.of (ProjectiveNormalTotalSpace k)) {w | w.1.2 = 0}
    (isClosed_normalKernelZeroSection k) W n
  exact @AddCommGrpCat.isZero_of_subsingleton _ e.injective.subsingleton

#print axioms normalKernelSupportedSingularComplex_homology_isZero_of_ne
/-- The actual supported singular complex is zero in every negative degree. -/
theorem normalKernelSupportedSingularComplex_isStrictlyGE (k : ℕ) :
    (normalKernelSupportedSingularComplex k).IsStrictlyGE 0 := by
  dsimp [normalKernelSupportedSingularComplex, supportedRationalSingularCochainComplex]
  infer_instance

#print axioms normalKernelSupportedSingularComplex_isStrictlyGE
end HodgeLean.Foundations.Program.G32Native.EulerModel
