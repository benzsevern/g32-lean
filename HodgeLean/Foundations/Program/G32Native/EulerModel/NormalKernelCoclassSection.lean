import HodgeLean.Foundations.Program.G32Native.EulerModel.NormalKernelCoclassGerms
import HodgeConjecture.Definitions.AlgebraicTopology.Sheaf.MapOfLocalStalks

/-! # A globally normalized supported kernel coclass section -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open AlgebraicTopology.Singular CategoryTheory Opposite TopCat.Presheaf
namespace HodgeLean.Foundations.Program.G32Native.EulerModel

/-- The normalized supported germ family on the original kernel total space. -/
def normalKernelCoclassStalk (k : ℕ) (v : ProjectiveNormalTotalSpace k) :
    (supportRelativeCohomologySheaf (TopCat.of (ProjectiveNormalTotalSpace k))
      {w | w.1.2 = 0} (2 * k)).presheaf.stalk v :=
  normalKernelChartCoclassGerm k (Classical.choose (normalCoordinateKernelChart_cover k v)) v
    (Classical.choose_spec (normalCoordinateKernelChart_cover k v))

#print axioms normalKernelCoclassStalk
/-- The original normalized germ family retains every specified chart germ. -/
theorem normalKernelCoclassStalk_eq_chartGerm (k : ℕ) (j : Fin (k + 1))
    (v : ProjectiveNormalTotalSpace k) (hv : v ∈ normalKernelCoclassChartOpen k j) :
    normalKernelCoclassStalk k v = normalKernelChartCoclassGerm k j v hv := by
  exact normalKernelChartCoclassGerm_eq k _ j v _ hv

#print axioms normalKernelCoclassStalk_eq_chartGerm
/-- The original kernel normal germ family is locally represented by its specified chart coclasses. -/
theorem normalKernelCoclassStalk_locallyRepresentable (k : ℕ) :
    ∀ v : ProjectiveNormalTotalSpace k,
      ∃ (U : TopologicalSpace.Opens (ProjectiveNormalTotalSpace k)) (_ : v ∈ U)
        (s : (supportRelativeCohomologySheaf (TopCat.of (ProjectiveNormalTotalSpace k))
          {w | w.1.2 = 0} (2 * k)).presheaf.obj (op U)),
        ∀ (w : ProjectiveNormalTotalSpace k) (hw : w ∈ U),
          (supportRelativeCohomologySheaf (TopCat.of (ProjectiveNormalTotalSpace k))
            {w | w.1.2 = 0} (2 * k)).presheaf.germ U w hw s = normalKernelCoclassStalk k w := by
  intro v
  obtain ⟨j, hj⟩ := normalCoordinateKernelChart_cover k v
  refine ⟨normalKernelCoclassChartOpen k j, hj,
    (supportRelativeCohomologyToSheaf (TopCat.of (ProjectiveNormalTotalSpace k))
      {w | w.1.2 = 0} (2 * k)).app _
      (chartNormalProjectionCoclass (Fin k → ℂ) k (normalCoordinateKernelChart k j)
        {w | w.1.2 = 0} (normalCoordinateKernelChart_support k j)
        (normalKernelCoclassChartOpen k j) (le_refl _)), ?_⟩
  exact fun w hw => (normalKernelCoclassStalk_eq_chartGerm k j w hw).symm

#print axioms normalKernelCoclassStalk_locallyRepresentable
/-- The global supported cohomology-sheaf section with the actual complex-normalized kernel chart germs. -/
def normalKernelCoclassSection (k : ℕ) :
    (supportRelativeCohomologySheaf (TopCat.of (ProjectiveNormalTotalSpace k))
      {w | w.1.2 = 0} (2 * k)).presheaf.obj (op ⊤) :=
  TopCat.Sheaf.sectionOfLocallyRepresentable _ (normalKernelCoclassStalk k)
    (normalKernelCoclassStalk_locallyRepresentable k)

#print axioms normalKernelCoclassSection
/-- The actual global supported section retains every original normalized kernel chart germ exactly. -/
theorem normalKernelCoclassSection_germ (k : ℕ) (j : Fin (k + 1))
    (v : ProjectiveNormalTotalSpace k) (hv : v ∈ normalKernelCoclassChartOpen k j) :
    (supportRelativeCohomologySheaf (TopCat.of (ProjectiveNormalTotalSpace k))
      {w | w.1.2 = 0} (2 * k)).presheaf.Γgerm v (normalKernelCoclassSection k) =
      normalKernelChartCoclassGerm k j v hv := by
  rw [normalKernelCoclassSection, TopCat.Sheaf.sectionOfLocallyRepresentable_germ]
  exact normalKernelCoclassStalk_eq_chartGerm k j v hv

#print axioms normalKernelCoclassSection_germ
end HodgeLean.Foundations.Program.G32Native.EulerModel
