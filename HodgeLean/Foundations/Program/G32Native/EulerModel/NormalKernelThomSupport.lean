import HodgeLean.Foundations.Program.G32Native.EulerModel.NormalKernelGlobalThomRestriction
import HodgeLean.Foundations.Program.G32Native.EulerModel.NormalKernelLocalization

/-! # The normalized Thom coclass on the original global kernel support pair -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open AlgebraicTopology.Singular CategoryTheory TopologicalSpace Opposite
namespace HodgeLean.Foundations.Program.G32Native.EulerModel

/-- The all-space neighborhood pair is the original total-space zero-complement pair, retaining every underlying vector. -/
def normalKernelUnivSupportPairIso (k : ℕ) :
    neighborhoodSupportComplementPair (Set.univ : Set (ProjectiveNormalTotalSpace k))
      {w | w.1.2 = 0} ≅
    TopPair.ofSubset (X := TopCat.of (ProjectiveNormalTotalSpace k)) {w | w.1.2 = 0}ᶜ :=
  TopPair.isoOfSubset (Homeomorph.Set.univ (ProjectiveNormalTotalSpace k)) (fun _ => Iff.rfl)

#print axioms normalKernelUnivSupportPairIso
/-- The global normalized Thom coclass on the literal original total-space support pair. -/
def normalKernelGlobalThomClass (k : ℕ) :
    CohomologyWithSupport ℚ (TopCat.of (ProjectiveNormalTotalSpace k)) {w | w.1.2 = 0} (2 * k) :=
  relativeCohomologyMap ℚ (2 * k) (normalKernelUnivSupportPairIso k).inv
    (normalKernelGlobalRelativeThomClass k)

#print axioms normalKernelGlobalThomClass
end HodgeLean.Foundations.Program.G32Native.EulerModel
