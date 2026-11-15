import HodgeLean.Foundations.Program.G32ContractionTwoDefs
import HodgeLean.Foundations.Program.G32Contraction
import HodgeLean.Foundations.Program.G32RepTransport

/-! # Bodies of the second stage of the G32 contraction

One auxiliary body per statement of `G32ContractionTwo.lean`. HC no distance; AV milestone no
distance.
-/

noncomputable section
set_option maxHeartbeats 400000
set_option maxRecDepth 4000
set_option Elab.async false

open scoped TensorProduct CategoryTheory.MonObj
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory
open HodgeLean.RealDefs HodgeLean.Adapters HodgeLean.Papers HodgeLean.Foundations
open HodgeLean.Foundations.Symplectic

namespace HodgeLean.Foundations.Program

variable {A : g32t_Sixfold}

theorem g32c_A_incl_proj (X : g32p_Cover A) :
    homPullback X.inclA 1 ∘ₗ homPullback X.projA 1 =
      (X.NA : ℚ) • LinearMap.id := by
  rw [← spec_homPullback_comp, X.retractA, ← zpow_natCast, spec_homPullback_zpow,
    spec_homPullback_id, Int.cast_natCast]

theorem g32c_A_incl_proj_C (X : g32p_Cover A) (y : ℂ ⊗[ℚ] HQ A.X 1) :
    (homPullback X.inclA 1).baseChange ℂ ((homPullback X.projA 1).baseChange ℂ y) =
      (X.NA : ℂ) • y := by
  rw [← LinearMap.comp_apply, ← LinearMap.baseChange_comp, g32c_A_incl_proj,
    LinearMap.baseChange_smul, LinearMap.baseChange_id, LinearMap.smul_apply, LinearMap.id_apply]
  exact (algebraMap_smul ℂ (X.NA : ℚ) y).symm.trans (by simp)

theorem g32c_A_restrict_proj (X : g32p_Cover A)
    {u : Module.End ℂ (ℂ ⊗[ℚ] HQ X.J 1)} (hu : u ∈ g32c_U X) :
    (homPullback X.projA 1).baseChange ℂ ∘ₗ g32c_restrict X.inclA X.projA X.NA u =
      u ∘ₗ (homPullback X.projA 1).baseChange ℂ := by
  have hcomm : u ∘ₗ ((homPullback X.projA 1).baseChange ℂ ∘ₗ
      (homPullback X.inclA 1).baseChange ℂ) =
      ((homPullback X.projA 1).baseChange ℂ ∘ₗ
      (homPullback X.inclA 1).baseChange ℂ) ∘ₗ u := by
    simp only [← LinearMap.baseChange_comp, ← spec_homPullback_comp]
    obtain ⟨c, hc⟩ := X.groupRing
    simp only [hc]
    have hterm (g : g32p_G) :
        u ∘ₗ (homPullback (X.aut g ^ c g) 1).baseChange ℂ =
          (homPullback (X.aut g ^ c g) 1).baseChange ℂ ∘ₗ u := by
      rw [spec_homPullback_zpow, LinearMap.baseChange_smul,
        LinearMap.comp_smul, LinearMap.smul_comp, hu.2.1 g]
    induction (Finset.univ : Finset g32p_G) using Finset.induction_on with
    | empty => simp only [Finset.prod_empty, spec_homPullback_one,
        LinearMap.baseChange_zero, LinearMap.comp_zero, LinearMap.zero_comp]
    | insert g t hgt ih =>
        rw [Finset.prod_insert hgt, spec_homPullback_mul, LinearMap.baseChange_add,
          LinearMap.comp_add, LinearMap.add_comp, hterm, ih]
  apply LinearMap.ext
  intro y
  have h := LinearMap.congr_fun hcomm ((homPullback X.projA 1).baseChange ℂ y)
  simp only [LinearMap.comp_apply] at h
  simp only [g32c_A_incl_proj_C, map_smul] at h
  simp only [LinearMap.comp_apply, g32c_restrict, LinearMap.smul_apply]
  rw [map_smul, ← h, smul_smul, inv_mul_cancel₀ (Nat.cast_ne_zero.mpr X.NA_pos.ne'), one_smul]

theorem g32c_scaled_pullback {P J : Over (Spec ↧ℂ)}
    [GrpObj P] [IsIntegral P.left] [Smooth P.hom] [IsProjective P.hom]
    [GrpObj J] [IsIntegral J.left] [Smooth J.hom] [IsProjective J.hom]
    (f : J ⟶ P) (k : ℕ) :
    (homPullback (f ≫ 𝟙 P ^ k) 1).baseChange ℂ =
      (k : ℂ) • (homPullback f 1).baseChange ℂ := by
  rw [spec_homPullback_comp, ← zpow_natCast, spec_homPullback_zpow,
    spec_homPullback_id, Int.cast_natCast, LinearMap.comp_smul, LinearMap.comp_id,
    LinearMap.baseChange_smul]
  apply LinearMap.ext
  intro y
  simp only [LinearMap.smul_apply]
  exact (algebraMap_smul ℂ (k : ℚ) _).symm.trans (by simp)

theorem g32c_lowerOne_equivariant_aux (X : g32p_Cover A) {r : ℕ} (S : Fin r → g32p_Supplier)
    (hS : ∀ j, g32p_Admissible X.aut (S j)) {u : Module.End ℂ (ℂ ⊗[ℚ] HQ X.J 1)}
    (hu : u ∈ g32c_U X) :
    g32p_diag X.J u (r + 1) ∘ₗ g32c_lowerOne X S hS =
      g32c_lowerOne X S hS ∘ₗ LinearMap.prodMap (g32c_restrict X.inclA X.projA X.NA u)
        (LinearMap.pi fun j => g32c_restrict (X.part (S j) (hS j)).incl
          (X.part (S j) (hS j)).proj (X.part (S j) (hS j)).N u ∘ₗ LinearMap.proj j) := by
  apply LinearMap.ext
  intro v
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · change u ((homPullback (X.projA ≫ 𝟙 A.X ^ (g32c_N X S hS / X.NA)) 1).baseChange ℂ v.1) =
      (homPullback (X.projA ≫ 𝟙 A.X ^ (g32c_N X S hS / X.NA)) 1).baseChange ℂ
        (g32c_restrict X.inclA X.projA X.NA u v.1)
    rw [g32c_scaled_pullback]
    simp only [LinearMap.smul_apply, map_smul]
    exact congrArg (((g32c_N X S hS / X.NA : ℕ) : ℂ) • ·)
      (LinearMap.congr_fun (g32c_A_restrict_proj X hu) v.1).symm
  · change u ((homPullback ((X.part (S j) (hS j)).proj ≫
        𝟙 (g32c_parts X S hS j) ^ (g32c_N X S hS / (X.part (S j) (hS j)).N)) 1).baseChange ℂ (v.2 j)) =
      (homPullback ((X.part (S j) (hS j)).proj ≫
        𝟙 (g32c_parts X S hS j) ^ (g32c_N X S hS / (X.part (S j) (hS j)).N)) 1).baseChange ℂ
        (g32c_restrict (X.part (S j) (hS j)).incl (X.part (S j) (hS j)).proj
          (X.part (S j) (hS j)).N u (v.2 j))
    rw [g32c_scaled_pullback]
    simp only [LinearMap.smul_apply, map_smul]
    exact congrArg (((g32c_N X S hS / (X.part (S j) (hS j)).N : ℕ) : ℂ) • ·)
      (LinearMap.congr_fun (g32rep_restrict_proj X (S j) (hS j) hu) (v.2 j)).symm

end HodgeLean.Foundations.Program
