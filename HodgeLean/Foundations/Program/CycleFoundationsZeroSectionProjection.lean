import HodgeLean.Foundations.Program.CycleFoundationsZeroSection

noncomputable section
set_option maxHeartbeats 400000
set_option maxRecDepth 2048
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj TensorProduct DirectSum
open HodgeLean.RealDefs HodgeLean.Adapters
attribute [local irreducible] cupProductOf algebraicCycleClassSpan homPullback
namespace HodgeLean.Foundations.Program

variable (A B : Over (Spec ↧ℂ))
    [GrpObj A] [IsCommMonObj A] [IsIntegral A.left] [Smooth A.hom] [IsProjective A.hom]
    [GrpObj B] [IsCommMonObj B] [IsIntegral B.left] [Smooth B.hom] [IsProjective B.hom]

theorem cfd_zero_section_projection (d : ℕ) (hA : TopologicalSpace.dim A.left = d)
    (I : HQ A (2 * d) ≃ₗ[ℚ] ℚ) (t : HQ A (2 * d)) (ht : I t = 1)
    (n : ℕ) (x : HQ (B ⊗ A) n) :
    homPullback (lift (𝟙 B) (1 : B ⟶ A)) n x =
      cfd_projection B A d I n ((cupProductOf (B ⊗ A)).cup rfl
        x (homPullback (snd B A) (2 * d) t)) := by
  classical
  let L := homPullback (lift (𝟙 B) (1 : B ⟶ A)) n
  let R := (cfd_projection B A d I n).comp
    ((cupProductOf (B ⊗ A)).cup rfl |>.flip
      (homPullback (snd B A) (2 * d) t))
  have he : L.comp (cp_kunnethMap B A n) = R.comp (cp_kunnethMap B A n) := by
    apply DirectSum.linearMap_ext ℚ
    intro k
    apply TensorProduct.ext'
    intro a b
    rcases k with ⟨⟨u, v⟩, hk⟩
    have huv : u + v = n := Finset.HasAntidiagonal.mem_antidiagonal.mp hk
    simp only [LinearMap.comp_apply, cp_kunnethMap, DirectSum.toModule_lof,
      TensorProduct.lift.tmul, LinearMap.compl₁₂_apply]
    change homPullback (lift (𝟙 B) (1 : B ⟶ A)) n
      ((cupProductOf (B ⊗ A)).cup huv
        (homPullback (fst B A) u a) (homPullback (snd B A) v b)) =
      cfd_projection B A d I n ((cupProductOf (B ⊗ A)).cup rfl
        ((cupProductOf (B ⊗ A)).cup huv
          (homPullback (fst B A) u a) (homPullback (snd B A) v b))
        (homPullback (snd B A) (2 * d) t))
    have hf : homPullback (lift (𝟙 B) (1 : B ⟶ A)) u
        (homPullback (fst B A) u a) = a := by
      rw [← LinearMap.comp_apply, ← spec_homPullback_comp,
        lift_fst, spec_homPullback_id, LinearMap.id_apply]
    have hs : homPullback (lift (𝟙 B) (1 : B ⟶ A)) v
        (homPullback (snd B A) v b) = homPullback (1 : B ⟶ A) v b := by
      rw [← LinearMap.comp_apply, ← spec_homPullback_comp, lift_snd]
    rw [spec_homPullback_cup, hf, hs]
    by_cases hv : v = 0
    · subst v
      have hu : u = n := by omega
      subst u
      obtain ⟨r, rfl⟩ := (cupProductOf_zeroEquiv A).surjective b
      simp only [cupProductOf_zeroEquiv_apply, map_smul, spec_homPullback_unit,
        LinearMap.smul_apply]
      have huB : (cupProductOf B).cup huv a (cupUnit B) = a :=
        (cupProductOf B).cup_one a
      have huP : (cupProductOf (B ⊗ A)).cup huv
          (homPullback (fst B A) n a) (cupUnit (B ⊗ A)) =
          homPullback (fst B A) n a :=
        (cupProductOf (B ⊗ A)).cup_one _
      rw [huB, huP, cfd_projection_cross_evaluation B A d hA I n, ht, one_smul]
    · rw [(cupProductOf (B ⊗ A)).assoc huv rfl rfl (by omega),
        ← spec_homPullback_cup (snd B A) rfl]
      rw [cfd_constant_pullback_positive A B v hv, LinearMap.zero_apply, map_zero]
      have hz : (cupProductOf A).cup rfl b t = 0 := by
        have hs := (vanishingAboveTop_abelian A).subsingleton (v + 2 * d) (by omega)
        exact hs.elim _ _
      rw [hz, map_zero, map_zero, map_zero]
  obtain ⟨z, hz⟩ := (cp_kunneth B A n).surjective x
  exact hz ▸ LinearMap.congr_fun he z

end HodgeLean.Foundations.Program
