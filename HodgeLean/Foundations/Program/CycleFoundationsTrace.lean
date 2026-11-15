import HodgeLean.Foundations.Program.CompensationAssemblyNormalizedTrace
import HodgeLean.Foundations.Program.CompensationAssemblyCrossComparison
import HodgeLean.Foundations.Program.CompensationAssemblyScalarPullback

noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 10000
set_option maxRecDepth 2048
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj
open AlgebraicTopology.Singular
open HodgeLean.RealDefs HodgeLean.Adapters HodgeLean.Foundations.Singular
attribute [local irreducible] cupComparison
namespace HodgeLean.Foundations.Program

def cfd_fibreTrace (T : TopCat.{0}) (Y : Over (Spec ↧ℂ))
    [GrpObj Y] [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]
    (d : ℕ) (hY : TopologicalSpace.dim Y.left = d) (I : HQ Y (2 * d) ≃ₗ[ℚ] ℚ) (n : ℕ) :
    Cohomology ℚ (TopCat.of (T × ComplexPoint Y)) (n + 2 * d) →ₗ[ℚ] Cohomology ℚ T n := by
  letI : SmoothOfRelativeDimension d Y.hom := by
    have h := SmoothOfRelativeDimension.of_isIntegral (f := Y.hom)
    rwa [hY] at h
  let J : Cohomology ℚ (TopCat.of (ComplexPoint Y)) (0 + 2 * d) ≃ₗ[ℚ] ℚ := by
    rw [Nat.zero_add]
    exact (cupComparison Y (2 * d)).symm.trans I
  exact cq_normalizedFibreTrace T (TopCat.of (ComplexPoint Y)) (2 * d) n
    (HodgeLean.Foundations.complexPointTorusHomeomorph Y d) J

theorem cfd_normalizedFibreTrace_cross_degree (T Y : TopCat.{0})
    (k m i : ℕ) (hm : 0 + k = m) (e : Y ≃ₜ UnitAddTorus (Fin k))
    (I : Cohomology ℚ Y m ≃ₗ[ℚ] ℚ) (a : Cohomology ℚ T i) (b : Cohomology ℚ Y m) :
    cq_normalizedFibreTrace T Y k i e (by rw [hm]; exact I)
      (cup (TopCat.of (T × Y)) (show i + m = i + k by omega)
        (cohomologyMap ℚ i (TopCat.ofHom ⟨Prod.fst, continuous_fst⟩) a)
        (cohomologyMap ℚ m (TopCat.ofHom ⟨Prod.snd, continuous_snd⟩) b)) = I b • a := by
  subst m
  simpa [Nat.add_zero] using cq_normalizedFibreTrace_cross T Y k i e I a b

theorem cfd_fibreTrace_cross (T : TopCat.{0}) (Y : Over (Spec ↧ℂ))
    [GrpObj Y] [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]
    (d : ℕ) (hY : TopologicalSpace.dim Y.left = d) (I : HQ Y (2 * d) ≃ₗ[ℚ] ℚ) (i : ℕ)
    (a : Cohomology ℚ T i) (b : HQ Y (2 * d)) :
    cfd_fibreTrace T Y d hY I i
      (cup (TopCat.of (T × ComplexPoint Y)) rfl
        (cohomologyMap ℚ i (TopCat.ofHom ⟨Prod.fst, continuous_fst⟩) a)
        (cohomologyMap ℚ (2 * d) (TopCat.ofHom ⟨Prod.snd, continuous_snd⟩)
          (cupComparison Y (2 * d) b))) = I b • a := by
  letI : SmoothOfRelativeDimension d Y.hom := by
    have h := SmoothOfRelativeDimension.of_isIntegral (f := Y.hom)
    rwa [hY] at h
  simpa only [cfd_fibreTrace, LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply] using
    cfd_normalizedFibreTrace_cross_degree T (TopCat.of (ComplexPoint Y))
      (2 * d) (2 * d) i (Nat.zero_add _)
      (HodgeLean.Foundations.complexPointTorusHomeomorph Y d)
      ((cupComparison Y (2 * d)).symm.trans I) a (cupComparison Y (2 * d) b)

theorem cfd_fibreTrace_naturality {U T : TopCat.{0}} (f : U ⟶ T)
    (Y : Over (Spec ↧ℂ))
    [GrpObj Y] [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]
    (d : ℕ) (hY : TopologicalSpace.dim Y.left = d) (I : HQ Y (2 * d) ≃ₗ[ℚ] ℚ) (n : ℕ)
    (c : Cohomology ℚ (TopCat.of (T × ComplexPoint Y)) (n + 2 * d)) :
    cfd_fibreTrace U Y d hY I n
      (cohomologyMap ℚ (n + 2 * d) (cq_fibreProductMap f (TopCat.of (ComplexPoint Y))) c) =
      cohomologyMap ℚ n f (cfd_fibreTrace T Y d hY I n c) := by
  letI : SmoothOfRelativeDimension d Y.hom := by
    have h := SmoothOfRelativeDimension.of_isIntegral (f := Y.hom)
    rwa [hY] at h
  let J : Cohomology ℚ (TopCat.of (ComplexPoint Y)) (0 + 2 * d) ≃ₗ[ℚ] ℚ := by
    rw [Nat.zero_add]
    exact (cupComparison Y (2 * d)).symm.trans I
  exact cq_normalizedFibreTrace_naturality f (TopCat.of (ComplexPoint Y)) (2 * d) n
    (HodgeLean.Foundations.complexPointTorusHomeomorph Y d) J c

def cfd_traceProjection (A Y : Over (Spec ↧ℂ))
    [GrpObj A] [IsCommMonObj A] [IsIntegral A.left] [Smooth A.hom] [IsProjective A.hom]
    [GrpObj Y] [IsCommMonObj Y] [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]
    (d : ℕ) (hY : TopologicalSpace.dim Y.left = d) (I : HQ Y (2 * d) ≃ₗ[ℚ] ℚ) (n : ℕ) :
    HQ (A ⊗ Y) (n + 2 * d) →ₗ[ℚ] HQ A n :=
  (cupComparison A n).symm.toLinearMap ∘ₗ
    cfd_fibreTrace (TopCat.of (ComplexPoint A)) Y d hY I n ∘ₗ
    (cohomologyHomeomorphEquiv
      (HodgeLean.Foundations.complexPointProdHomeomorph A Y) (n + 2 * d)).toLinearMap ∘ₗ
    (cupComparison (A ⊗ Y) (n + 2 * d)).toLinearMap

theorem cfd_traceProjection_cross (A Y : Over (Spec ↧ℂ))
    [GrpObj A] [IsCommMonObj A] [IsIntegral A.left] [Smooth A.hom] [IsProjective A.hom]
    [GrpObj Y] [IsCommMonObj Y] [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]
    (d : ℕ) (hY : TopologicalSpace.dim Y.left = d) (I : HQ Y (2 * d) ≃ₗ[ℚ] ℚ) (i : ℕ)
    (a : HQ A i) (b : HQ Y (2 * d)) :
    cfd_traceProjection A Y d hY I i (cq_cross A Y i (2 * d) a b) = I b • a := by
  simp only [cfd_traceProjection, LinearMap.comp_apply, LinearEquiv.coe_coe]
  rw [cq_cross_singular_product, cfd_fibreTrace_cross, map_smul,
    LinearEquiv.symm_apply_apply]

theorem cfd_fibreTrace_cross_ne (A Y : Over (Spec ↧ℂ))
    [GrpObj A] [IsCommMonObj A] [IsIntegral A.left] [Smooth A.hom] [IsProjective A.hom]
    [GrpObj Y] [IsCommMonObj Y] [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]
    (d : ℕ) (hY : TopologicalSpace.dim Y.left = d) (I : HQ Y (2 * d) ≃ₗ[ℚ] ℚ)
    (i j n : ℕ) (hij : i + j = n + 2 * d) (hi : i ≠ n)
    (a : HQ A i) (b : HQ Y j) :
    cfd_fibreTrace (TopCat.of (ComplexPoint A)) Y d hY I n
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
  have hc : cohomologyMap ℚ (n + 2 * d) F C = (2 : ℚ) ^ i • C := by
    dsimp only [C]
    rw [cohomologyMap_cup, hpA, hpY, map_smul, LinearMap.smul_apply]
  have ht := cfd_fibreTrace_naturality f Y d hY I n C
  rw [hc, map_smul, cq_double_pullback_singular] at ht
  have hneq : (2 : ℚ) ^ i ≠ (2 : ℚ) ^ n := by
    intro h
    exact hi ((pow_right_injective₀ (by norm_num : (0 : ℚ) < 2) (by norm_num : (2 : ℚ) ≠ 1)) h)
  have hz : ((2 : ℚ) ^ i - (2 : ℚ) ^ n) •
      cfd_fibreTrace (TopCat.of (ComplexPoint A)) Y d hY I n C = 0 := by
    rw [sub_smul, ht, sub_self]
  exact (smul_eq_zero.mp hz).resolve_left (sub_ne_zero.mpr hneq)


end HodgeLean.Foundations.Program
