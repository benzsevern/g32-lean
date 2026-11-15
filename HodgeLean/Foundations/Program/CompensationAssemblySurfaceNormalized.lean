import HodgeLean.Foundations.Program.CompensationAssemblyNormalizedTrace
import HodgeLean.Foundations.Program.CompensationAssemblyCrossComparison

noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 10000
set_option maxRecDepth 2048
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj
open AlgebraicTopology.Singular
open HodgeLean.RealDefs HodgeLean.Adapters HodgeLean.Foundations.Singular
namespace HodgeLean.Foundations.Program

def cq_surfaceTrace (T : TopCat.{0}) (Y : Over (Spec ↧ℂ))
    [GrpObj Y] [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]
    (hY : TopologicalSpace.dim Y.left = 2) (I : HQ Y 4 ≃ₗ[ℚ] ℚ) (n : ℕ) :
    Cohomology ℚ (TopCat.of (T × ComplexPoint Y)) (n + 4) →ₗ[ℚ] Cohomology ℚ T n := by
  letI : SmoothOfRelativeDimension 2 Y.hom := by
    have h := SmoothOfRelativeDimension.of_isIntegral (f := Y.hom)
    rwa [hY] at h
  exact cq_normalizedFibreTrace T (TopCat.of (ComplexPoint Y)) 4 n
    (HodgeLean.Foundations.complexPointTorusHomeomorph Y 2)
    ((cupComparison Y 4).symm.trans I)

theorem cq_surfaceTrace_cross (T : TopCat.{0}) (Y : Over (Spec ↧ℂ))
    [GrpObj Y] [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]
    (hY : TopologicalSpace.dim Y.left = 2) (I : HQ Y 4 ≃ₗ[ℚ] ℚ) (i : ℕ)
    (a : Cohomology ℚ T i) (b : HQ Y 4) :
    cq_surfaceTrace T Y hY I i
      (cup (TopCat.of (T × ComplexPoint Y)) rfl
        (cohomologyMap ℚ i (TopCat.ofHom ⟨Prod.fst, continuous_fst⟩) a)
        (cohomologyMap ℚ 4 (TopCat.ofHom ⟨Prod.snd, continuous_snd⟩)
          (cupComparison Y 4 b))) = I b • a := by
  letI : SmoothOfRelativeDimension 2 Y.hom := by
    have h := SmoothOfRelativeDimension.of_isIntegral (f := Y.hom)
    rwa [hY] at h
  simpa only [Nat.add_zero, Nat.zero_add, cq_surfaceTrace, LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply] using
    cq_normalizedFibreTrace_cross T (TopCat.of (ComplexPoint Y)) 4 i
      (HodgeLean.Foundations.complexPointTorusHomeomorph Y 2)
      ((cupComparison Y 4).symm.trans I) a (cupComparison Y 4 b)

theorem cq_surfaceTrace_naturality {U T : TopCat.{0}} (f : U ⟶ T)
    (Y : Over (Spec ↧ℂ))
    [GrpObj Y] [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]
    (hY : TopologicalSpace.dim Y.left = 2) (I : HQ Y 4 ≃ₗ[ℚ] ℚ) (n : ℕ)
    (c : Cohomology ℚ (TopCat.of (T × ComplexPoint Y)) (n + 4)) :
    cq_surfaceTrace U Y hY I n
      (cohomologyMap ℚ (n + 4) (cq_fibreProductMap f (TopCat.of (ComplexPoint Y))) c) =
      cohomologyMap ℚ n f (cq_surfaceTrace T Y hY I n c) := by
  letI : SmoothOfRelativeDimension 2 Y.hom := by
    have h := SmoothOfRelativeDimension.of_isIntegral (f := Y.hom)
    rwa [hY] at h
  exact cq_normalizedFibreTrace_naturality f (TopCat.of (ComplexPoint Y)) 4 n
    (HodgeLean.Foundations.complexPointTorusHomeomorph Y 2)
    ((cupComparison Y 4).symm.trans I) c

def cq_surfaceProjection (A Y : Over (Spec ↧ℂ))
    [GrpObj A] [IsCommMonObj A] [IsIntegral A.left] [Smooth A.hom] [IsProjective A.hom]
    [GrpObj Y] [IsCommMonObj Y] [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]
    (hY : TopologicalSpace.dim Y.left = 2) (I : HQ Y 4 ≃ₗ[ℚ] ℚ) (n : ℕ) :
    HQ (A ⊗ Y) (n + 4) →ₗ[ℚ] HQ A n :=
  (cupComparison A n).symm.toLinearMap ∘ₗ
    cq_surfaceTrace (TopCat.of (ComplexPoint A)) Y hY I n ∘ₗ
    (cohomologyHomeomorphEquiv
      (HodgeLean.Foundations.complexPointProdHomeomorph A Y) (n + 4)).toLinearMap ∘ₗ
    (cupComparison (A ⊗ Y) (n + 4)).toLinearMap

theorem cq_surfaceProjection_cross (A Y : Over (Spec ↧ℂ))
    [GrpObj A] [IsCommMonObj A] [IsIntegral A.left] [Smooth A.hom] [IsProjective A.hom]
    [GrpObj Y] [IsCommMonObj Y] [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]
    (hY : TopologicalSpace.dim Y.left = 2) (I : HQ Y 4 ≃ₗ[ℚ] ℚ) (i : ℕ)
    (a : HQ A i) (b : HQ Y 4) :
    cq_surfaceProjection A Y hY I i (cq_cross A Y i 4 a b) = I b • a := by
  simp only [cq_surfaceProjection, LinearMap.comp_apply, LinearEquiv.coe_coe]
  rw [cq_cross_singular_product, cq_surfaceTrace_cross, map_smul,
    LinearEquiv.symm_apply_apply]

end HodgeLean.Foundations.Program
