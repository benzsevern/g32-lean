import HodgeLean.Foundations.Program.CycleFoundationsDefs
/-! Evaluation of the Künneth projection on cross summands. -/
noncomputable section
set_option maxHeartbeats 400000
set_option maxRecDepth 2048
set_option backward.isDefEq.respectTransparency true
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj TensorProduct DirectSum
open HodgeLean.RealDefs HodgeLean.Adapters
attribute [local irreducible] cupProductOf algebraicCycleClassSpan homPullback
namespace HodgeLean.Foundations.Program
theorem cfd_projection_cross_evaluation (A : Over (Spec ↧ℂ)) [GrpObj A] [IsCommMonObj A]
    [IsIntegral A.left] [Smooth A.hom] [IsProjective A.hom] (B : Over (Spec ↧ℂ)) [GrpObj B] [IsCommMonObj B]
    [IsIntegral B.left] [Smooth B.hom] [IsProjective B.hom]
    (d : ℕ) (hB : TopologicalSpace.dim B.left = d)
    (I : HQ B (2 * d) ≃ₗ[ℚ] ℚ)
    (n : ℕ) (a : HQ A n) (b : HQ B (2 * d)) :
    cfd_projection A B d I n
      ((cupProductOf (A ⊗ B)).cup rfl
        (homPullback (fst A B) n a) (homPullback (snd A B) (2 * d) b)) = I b • a := by
  classical
  let k : Finset.HasAntidiagonal.antidiagonal (n + 2 * d) :=
    ⟨(n, 2 * d), Finset.HasAntidiagonal.mem_antidiagonal.mpr rfl⟩
  let v : (⨁ p : Finset.HasAntidiagonal.antidiagonal (n + 2 * d),
      HQ A p.1.1 ⊗[ℚ] HQ B p.1.2) := DirectSum.lof ℚ _ _ k (a ⊗ₜ[ℚ] b)
  have hv : cp_kunnethMap A B (n + 2 * d) v =
      (cupProductOf (A ⊗ B)).cup rfl
        (homPullback (fst A B) n a) (homPullback (snd A B) (2 * d) b) := by
    simp [v, cp_kunnethMap, k]
  rw [← hv]
  change (TensorProduct.rid ℚ (HQ A n))
    (TensorProduct.map LinearMap.id I.toLinearMap
      (DirectSum.component ℚ _ _ k
        ((LinearEquiv.ofBijective (cp_kunnethMap A B (n + 2 * d))
          (cp_kunneth A B (n + 2 * d))).symm
          ((LinearEquiv.ofBijective (cp_kunnethMap A B (n + 2 * d))
            (cp_kunneth A B (n + 2 * d))) v)))) = _
  rw [LinearEquiv.symm_apply_apply]
  dsimp only [v]
  rw [DirectSum.component.lof_self]
  simp only [TensorProduct.map_tmul, LinearMap.id_apply, LinearEquiv.coe_coe,
    TensorProduct.rid_tmul]

theorem cfd_projection_cross_off_evaluation (A : Over (Spec ↧ℂ)) [GrpObj A] [IsCommMonObj A]
    [IsIntegral A.left] [Smooth A.hom] [IsProjective A.hom] (B : Over (Spec ↧ℂ)) [GrpObj B] [IsCommMonObj B]
    [IsIntegral B.left] [Smooth B.hom] [IsProjective B.hom]
    (d : ℕ) (I : HQ B (2 * d) ≃ₗ[ℚ] ℚ) (n u v : ℕ)
    (h : u + v = n + 2 * d) (hv : v ≠ 2 * d) (a : HQ A u) (b : HQ B v) :
    cfd_projection A B d I n ((cupProductOf (A ⊗ B)).cup h
      (homPullback (fst A B) u a) (homPullback (snd A B) v b)) = 0 := by
  classical
  let k : Finset.HasAntidiagonal.antidiagonal (n + 2 * d) :=
    ⟨(u, v), Finset.HasAntidiagonal.mem_antidiagonal.mpr h⟩
  let z : (⨁ p : Finset.HasAntidiagonal.antidiagonal (n + 2 * d),
      HQ A p.1.1 ⊗[ℚ] HQ B p.1.2) := DirectSum.lof ℚ _ _ k (a ⊗ₜ[ℚ] b)
  have hz : cp_kunnethMap A B (n + 2 * d) z =
      (cupProductOf (A ⊗ B)).cup h
        (homPullback (fst A B) u a) (homPullback (snd A B) v b) := by
    simp only [z, cp_kunnethMap, DirectSum.toModule_lof, TensorProduct.lift.tmul,
      LinearMap.compl₁₂_apply]
    rfl
  rw [← hz]
  let t : Finset.HasAntidiagonal.antidiagonal (n + 2 * d) :=
    ⟨(n, 2 * d), Finset.HasAntidiagonal.mem_antidiagonal.mpr rfl⟩
  have hkt : k ≠ t := fun he => hv (congrArg (fun p => p.1.2) he)
  change (TensorProduct.rid ℚ (HQ A n))
    (TensorProduct.map LinearMap.id I.toLinearMap
      (DirectSum.component ℚ _ _ t
        ((LinearEquiv.ofBijective (cp_kunnethMap A B (n + 2 * d))
          (cp_kunneth A B (n + 2 * d))).symm
          ((LinearEquiv.ofBijective (cp_kunnethMap A B (n + 2 * d))
            (cp_kunneth A B (n + 2 * d))) z)))) = 0
  rw [LinearEquiv.symm_apply_apply]
  simp only [z, DirectSum.component.of, dif_neg hkt, map_zero]


end HodgeLean.Foundations.Program
