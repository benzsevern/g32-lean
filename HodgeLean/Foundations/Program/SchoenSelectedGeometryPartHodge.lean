import HodgeLean.Foundations.Program.SchoenSelectedGeometryPartRetraction

noncomputable section
set_option maxHeartbeats 400000
set_option maxRecDepth 2000
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open HodgeLean.Adapters HodgeLean.RealDefs HodgeLean.Foundations
open scoped CategoryTheory.MonObj TensorProduct
namespace HodgeLean.Foundations.Program

/-- A part transports its balanced cyclotomic coordinates to the primitive subspace. -/
theorem s0_part_primitive_hodge_coordinates
    (J : Over (Spec ↧ℂ)) [GrpObj J] [IsCommMonObj J] [IsIntegral J.left]
    [Smooth J.hom] [IsProjective J.hom]
    (aut : g32p_G → (J ⟶ J)) (S : g32p_Supplier) (P : g32p_Part J aut S) :
    ∃ e : g32p_primitive aut S ≃ₗ[ℚ] (Fin (2 * P.k) → cyc_Field S.m),
      (∀ h : S.H, (g32p_primitive aut S).subtype ∘ₗ
        cyc_scalar e (g32p_fieldValue S h) =
        homPullback (aut h) 1 ∘ₗ (g32p_primitive aut S).subtype) ∧
      ∀ σ : cyc_Field S.m →ₐ[ℚ] ℂ,
        Module.finrank ℂ ↥(cyc_eigenspace e σ ⊓
          (cohomologyHodgePiece J 1 (1, 0)).comap
            ((g32p_primitive aut S).subtype.baseChange ℂ)) = P.k := by
  letI := P.incl_hom
  letI := P.proj_hom
  let V := g32p_primitive aut S
  let r : HQ P.P 1 ≃ₗ[ℚ] V :=
    (LinearEquiv.ofInjective (homPullback P.proj 1)
      (s0_part_proj_injective J aut S P)).trans (LinearEquiv.ofEq _ _ P.image)
  have hsub : V.subtype ∘ₗ r.toLinearMap = homPullback P.proj 1 := rfl
  let e := r.symm.trans P.act.cyc_coordinates
  have hre : r.trans e = P.act.cyc_coordinates := by
    ext v
    simp only [e, LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply]
  have hsubC : V.subtype.baseChange ℂ ∘ₗ (r.baseChange ℚ ℂ _ _).toLinearMap =
      (homPullback P.proj 1).baseChange ℂ :=
    (LinearMap.baseChange_comp _ _).symm.trans (congrArg (LinearMap.baseChange ℂ) hsub)
  have hcompC : (homPullback P.incl 1).baseChange ℂ ∘ₗ (homPullback P.proj 1).baseChange ℂ =
      (P.N : ℚ) • LinearMap.id := by
    rw [← LinearMap.baseChange_comp, s0_part_retract,
      LinearMap.baseChange_smul, LinearMap.baseChange_id]
  have hH (pq : ℤ × ℤ) :
      ((cohomologyHodgePiece J 1 pq).comap (V.subtype.baseChange ℂ)).comap
        (r.baseChange ℚ ℂ _ _).toLinearMap = cohomologyHodgePiece P.P 1 pq := by
    rw [← Submodule.comap_comp, hsubC]
    apply le_antisymm
    · intro x hx
      have hh := spec_homPullback_hodgePiece_one P.incl pq (Submodule.mem_map_of_mem hx)
      have he := LinearMap.congr_fun hcompC x
      change (homPullback P.incl 1).baseChange ℂ ((homPullback P.proj 1).baseChange ℂ x) =
        (P.N : ℚ) • x at he
      rw [he] at hh
      exact (Submodule.smul_mem_iff _ (show (P.N : ℚ) ≠ 0 from Nat.cast_ne_zero.mpr P.N_pos.ne')).mp hh
    · exact (Submodule.map_le_iff_le_comap).mp (spec_homPullback_hodgePiece_one P.proj pq)
  refine ⟨e, ?_, ?_⟩
  · intro h
    ext w
    obtain ⟨v, rfl⟩ := r.surjective w
    have hc := LinearMap.congr_fun (g32y_scalar_trans r e (g32p_fieldValue S h)) v
    rw [hre] at hc
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe] at hc
    change V.subtype (cyc_scalar e (g32p_fieldValue S h) (r v)) =
      homPullback (aut h) 1 (V.subtype (r v))
    rw [← hc]
    exact LinearMap.congr_fun (P.equivariant h) v
  · intro σ
    have hs := P.act.cyc_signature σ
    change Module.finrank ℂ ↥(cyc_eigenspace P.act.cyc_coordinates σ ⊓
      cohomologyHodgePiece P.P 1 (1, 0)) = P.k at hs
    rw [← hre, g32y_eigenspace_trans, ← hH (1, 0), ← Submodule.comap_inf] at hs
    rw [((r.baseChange ℚ ℂ _ _).ofSubmodule' _).finrank_eq] at hs
    exact hs

#print axioms s0_part_primitive_hodge_coordinates
end HodgeLean.Foundations.Program
