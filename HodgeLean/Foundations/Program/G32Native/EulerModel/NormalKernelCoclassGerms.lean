import HodgeLean.Foundations.Program.G32Native.EulerModel.NormalKernelCoclassOverlap
import HodgeLean.Foundations.Program.G32Native.EulerModel.NormalKernelZeroSupport
import HodgeConjecture.Lemmas.AlgebraicTopology.Support.RelativeCohomologySheaf

/-! # Actual kernel chart normal classes in the supported cohomology sheaf -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open AlgebraicTopology.Singular CategoryTheory Opposite
namespace HodgeLean.Foundations.Program.G32Native.EulerModel

/-- The original open source of the specified kernel chart. -/
def normalKernelCoclassChartOpen (k : ℕ) (j : Fin (k + 1)) :
    TopologicalSpace.Opens (ProjectiveNormalTotalSpace k) :=
  ⟨(normalCoordinateKernelChart k j).source, (normalCoordinateKernelChart k j).open_source⟩

/-- The supported sheaf germ of the actual chart normal coclass. -/
def normalKernelChartCoclassGerm (k : ℕ) (j : Fin (k + 1))
    (v : ProjectiveNormalTotalSpace k) (hv : v ∈ normalKernelCoclassChartOpen k j) :
    (supportRelativeCohomologySheaf (TopCat.of (ProjectiveNormalTotalSpace k))
      {w | w.1.2 = 0} (2 * k)).presheaf.stalk v :=
  supportRelativeCohomologyGerm (TopCat.of (ProjectiveNormalTotalSpace k))
    {w | w.1.2 = 0} (2 * k) (normalKernelCoclassChartOpen k j) v hv
    (chartNormalProjectionCoclass (Fin k → ℂ) k (normalCoordinateKernelChart k j)
      {w | w.1.2 = 0} (normalCoordinateKernelChart_support k j)
      (normalKernelCoclassChartOpen k j) (le_refl _))

#print axioms normalKernelCoclassChartOpen
#print axioms normalKernelChartCoclassGerm
/-- All actual chart normal coclasses define the same supported germ at every shared point. -/
theorem normalKernelChartCoclassGerm_eq (k : ℕ) (i j : Fin (k + 1))
    (v : ProjectiveNormalTotalSpace k)
    (hi : v ∈ normalKernelCoclassChartOpen k i)
    (hj : v ∈ normalKernelCoclassChartOpen k j) :
    normalKernelChartCoclassGerm k i v hi = normalKernelChartCoclassGerm k j v hj := by
  by_cases hv : v.1.2 = 0
  · obtain ⟨W, hW, hW', hvW, heq⟩ := normalCoordinateKernelCoclass_overlap k j i v hv hi hj
    apply supportRelativeCohomologyGerm_eq_of_restrict_eq
      (TopCat.of (ProjectiveNormalTotalSpace k)) {w | w.1.2 = 0} (2 * k)
      hW hW' v hvW
    simpa only [chartNormalProjectionCoclass_restrict] using heq
  · unfold normalKernelChartCoclassGerm
    rw [supportRelativeCohomologyGerm_eq_zero_of_not_mem
      (TopCat.of (ProjectiveNormalTotalSpace k)) _ _ (isClosed_normalKernelZeroSection k)
      _ v hi hv,
      supportRelativeCohomologyGerm_eq_zero_of_not_mem
      (TopCat.of (ProjectiveNormalTotalSpace k)) _ _ (isClosed_normalKernelZeroSection k)
      _ v hj hv]

#print axioms normalKernelChartCoclassGerm_eq
end HodgeLean.Foundations.Program.G32Native.EulerModel
