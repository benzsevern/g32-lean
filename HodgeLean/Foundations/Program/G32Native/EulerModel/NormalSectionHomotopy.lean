import HodgeLean.Foundations.Program.G32Native.EulerModel.GlobalNormalTopology
import Other.AlgebraicTopology.Singular.SupportNaturality

/-! # Comparing the zero section and the global kernel section on singular cohomology -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicTopology.Singular
namespace HodgeLean.Foundations.Program.G32Native.EulerModel

/-- The continuous zero section into the actual total space of the kernel family. -/
def projectiveNormalZeroSection (k : ℕ) :
    C(Projectivization ℂ (ℂ × (Fin k → ℂ)), ProjectiveNormalTotalSpace k) where
  toFun p := ⟨(p, 0), (projectiveNormalKernel k p).zero_mem⟩
  continuous_toFun := (continuous_id.prodMk continuous_const).subtype_mk _

/-- Linear interpolation stays in each actual kernel fibre. -/
def projectiveNormalSectionHomotopy (k : ℕ) :
    ContinuousMap.Homotopy (projectiveNormalZeroSection k)
      ⟨projectiveNormalSectionMap k, continuous_projectiveNormalSectionMap k⟩ where
  toFun t := ⟨(t.2, (t.1.val : ℂ) • projectiveNormalSectionVector k t.2),
    (projectiveNormalKernel k t.2).smul_mem _ (projectiveNormalSectionVector_mem k t.2)⟩
  continuous_toFun := (continuous_snd.prodMk
    ((Complex.continuous_ofReal.comp (continuous_subtype_val.comp continuous_fst)).smul
      ((continuous_projectiveNormalSectionVector k).comp continuous_snd))).subtype_mk _
  map_zero_left p := by
    apply Subtype.ext
    simp [projectiveNormalZeroSection]
  map_one_left p := by
    apply Subtype.ext
    simp [projectiveNormalSectionMap]

#print axioms projectiveNormalSectionHomotopy

/-- Zero-section and global-section pullbacks agree on every actual singular cohomology class. -/
theorem projectiveNormalSection_cohomology_pullback (k n : ℕ)
    (α : Cohomology ℚ (TopCat.of (ProjectiveNormalTotalSpace k)) n) :
    cohomologyMap ℚ n (TopCat.ofHom (projectiveNormalZeroSection k)) α =
      cohomologyMap ℚ n (TopCat.ofHom
        ⟨projectiveNormalSectionMap k, continuous_projectiveNormalSectionMap k⟩) α := by
  exact congrArg (fun f => f α)
    (cohomologyMap_eq_of_homotopy ℚ n
      (f := TopCat.ofHom (projectiveNormalZeroSection k))
      (g := TopCat.ofHom ⟨projectiveNormalSectionMap k, continuous_projectiveNormalSectionMap k⟩)
      (projectiveNormalSectionHomotopy k))

#print axioms projectiveNormalSection_cohomology_pullback
end HodgeLean.Foundations.Program.G32Native.EulerModel
