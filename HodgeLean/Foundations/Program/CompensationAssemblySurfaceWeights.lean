import HodgeLean.Foundations.Program.CompensationAssemblySurfaceNormalized
import HodgeLean.Foundations.Program.CompensationAssemblyScalarPullback

noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 10000
set_option maxRecDepth 2048
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open scoped CategoryTheory.MonObj
open AlgebraicTopology.Singular
open HodgeLean.RealDefs HodgeLean.Adapters HodgeLean.Foundations.Singular
namespace HodgeLean.Foundations.Program

theorem cq_surfaceTrace_cross_ne (A Y : Over (Spec ↧ℂ))
    [GrpObj A] [IsCommMonObj A] [IsIntegral A.left] [Smooth A.hom] [IsProjective A.hom]
    [GrpObj Y] [IsCommMonObj Y] [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]
    (hY : TopologicalSpace.dim Y.left = 2) (I : HQ Y 4 ≃ₗ[ℚ] ℚ)
    (i j n : ℕ) (hij : i + j = n + 4) (hi : i ≠ n)
    (a : HQ A i) (b : HQ Y j) :
    cq_surfaceTrace (TopCat.of (ComplexPoint A)) Y hY I n
      (cup (TopCat.of (ComplexPoint A × ComplexPoint Y)) hij
        (cohomologyMap ℚ i (TopCat.ofHom ⟨Prod.fst, continuous_fst⟩) (cupComparison A i a))
        (cohomologyMap ℚ j (TopCat.ofHom ⟨Prod.snd, continuous_snd⟩) (cupComparison Y j b))) = 0 := by
  let f : TopCat.of (ComplexPoint A) ⟶ TopCat.of (ComplexPoint A) :=
    TopCat.ofHom (Point.continuousMap ((𝟙 A : A ⟶ A) ^ (2 : ℤ)))
  let F := cq_fibreProductMap f (TopCat.of (ComplexPoint Y))
  let C := cup (TopCat.of (ComplexPoint A × ComplexPoint Y)) hij
    (cohomologyMap ℚ i (TopCat.ofHom ⟨Prod.fst, continuous_fst⟩) (cupComparison A i a))
    (cohomologyMap ℚ j (TopCat.ofHom ⟨Prod.snd, continuous_snd⟩) (cupComparison Y j b))
  have hfA : F ≫ TopCat.ofHom ⟨Prod.fst, continuous_fst⟩ =
      (TopCat.ofHom ⟨Prod.fst, continuous_fst⟩) ≫ f := rfl
  have hpA : cohomologyMap ℚ i F
      (cohomologyMap ℚ i (TopCat.ofHom ⟨Prod.fst, continuous_fst⟩) (cupComparison A i a)) =
      (2 : ℚ) ^ i •
        cohomologyMap ℚ i (TopCat.ofHom ⟨Prod.fst, continuous_fst⟩) (cupComparison A i a) := by
    change (cohomologyMap ℚ i F ∘ₗ
      cohomologyMap ℚ i (TopCat.ofHom ⟨Prod.fst, continuous_fst⟩)) (cupComparison A i a) = _
    rw [← cohomologyMap_comp, hfA, cohomologyMap_comp, LinearMap.comp_apply,
      cq_double_pullback_singular, map_smul]
  have hpY : cohomologyMap ℚ j F
      (cohomologyMap ℚ j (TopCat.ofHom ⟨Prod.snd, continuous_snd⟩) (cupComparison Y j b)) =
      cohomologyMap ℚ j (TopCat.ofHom ⟨Prod.snd, continuous_snd⟩) (cupComparison Y j b) := by
    change (cohomologyMap ℚ j F ∘ₗ
      cohomologyMap ℚ j (TopCat.ofHom ⟨Prod.snd, continuous_snd⟩)) (cupComparison Y j b) = _
    rw [← cohomologyMap_comp]
    rfl
  have hc : cohomologyMap ℚ (n + 4) F C = (2 : ℚ) ^ i • C := by
    dsimp only [C]
    rw [cohomologyMap_cup, hpA, hpY, map_smul, LinearMap.smul_apply]
  have ht := cq_surfaceTrace_naturality f Y hY I n C
  rw [hc, map_smul, cq_double_pullback_singular] at ht
  have hneq : (2 : ℚ) ^ i ≠ (2 : ℚ) ^ n := by
    intro h
    exact hi ((pow_right_injective₀ (by norm_num : (0 : ℚ) < 2) (by norm_num : (2 : ℚ) ≠ 1)) h)
  have hz : ((2 : ℚ) ^ i - (2 : ℚ) ^ n) •
      cq_surfaceTrace (TopCat.of (ComplexPoint A)) Y hY I n C = 0 := by
    rw [sub_smul, ht, sub_self]
  exact (smul_eq_zero.mp hz).resolve_left (sub_ne_zero.mpr hneq)

end HodgeLean.Foundations.Program
