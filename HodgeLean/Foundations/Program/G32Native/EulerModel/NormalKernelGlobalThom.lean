import HodgeLean.Foundations.Program.G32Native.EulerModel.NormalKernelRelativeSheaf
import HodgeLean.Foundations.Program.G32Native.EulerModel.NormalKernelCoclassSection

/-! # The global relative Thom coclass of the original kernel zero section -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open AlgebraicTopology.Singular CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
namespace HodgeLean.Foundations.Program.G32Native.EulerModel

/-- The actual relative class map to its supported sheaf is an isomorphism on every original open. -/
theorem normalKernelRelativeCohomologyToSheaf_isIso (k : ℕ)
    (U : Opens (ProjectiveNormalTotalSpace k)) :
    IsIso ((supportRelativeCohomologyToSheaf (TopCat.of (ProjectiveNormalTotalSpace k))
      {w | w.1.2 = 0} (2 * k)).app (op U)) := by
  letI := isIso_toSheafify (Opens.grothendieckTopology (ProjectiveNormalTotalSpace k))
    (normalKernelRelativeCohomology_isSheaf k)
  change IsIso ((toSheafify (Opens.grothendieckTopology (ProjectiveNormalTotalSpace k))
    (supportRelativeCohomologyPresheaf (TopCat.of (ProjectiveNormalTotalSpace k))
      {w | w.1.2 = 0} (2 * k))).app (op U))
  infer_instance

#print axioms normalKernelRelativeCohomologyToSheaf_isIso
/-- The global relative Thom coclass on the entire original kernel space, retaining its specified supported section. -/
def normalKernelGlobalRelativeThomClass (k : ℕ) :
    RelativeCohomology ℚ
      (neighborhoodSupportComplementPair (Set.univ : Set (ProjectiveNormalTotalSpace k))
        {w | w.1.2 = 0}) (2 * k) :=
  letI := normalKernelRelativeCohomologyToSheaf_isIso k ⊤
  (asIso ((supportRelativeCohomologyToSheaf (TopCat.of (ProjectiveNormalTotalSpace k))
    {w | w.1.2 = 0} (2 * k)).app (op ⊤))).inv (normalKernelCoclassSection k)

#print axioms normalKernelGlobalRelativeThomClass
/-- The global relative kernel Thom coclass has exactly the original normalized supported sheaf section. -/
theorem normalKernelGlobalRelativeThomClass_toSheaf (k : ℕ) :
    (supportRelativeCohomologyToSheaf (TopCat.of (ProjectiveNormalTotalSpace k))
      {w | w.1.2 = 0} (2 * k)).app (op ⊤) (normalKernelGlobalRelativeThomClass k) =
        normalKernelCoclassSection k := by
  letI := normalKernelRelativeCohomologyToSheaf_isIso k ⊤
  exact ConcreteCategory.congr_hom
    (asIso ((supportRelativeCohomologyToSheaf (TopCat.of (ProjectiveNormalTotalSpace k))
      {w | w.1.2 = 0} (2 * k)).app (op ⊤))).inv_hom_id (normalKernelCoclassSection k)

#print axioms normalKernelGlobalRelativeThomClass_toSheaf
end HodgeLean.Foundations.Program.G32Native.EulerModel
