import HodgeLean.Foundations.Program.SchoenTransferJ12CurveAdjointMap

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 4000
open CategoryTheory AlgebraicGeometry MonoidalCategory
open HodgeLean.RealDefs HodgeLean.Adapters HodgeLean.Foundations HodgeLean.Foundations.Symplectic
namespace HodgeLean.Foundations.Program
attribute [local irreducible] cupProductOf homPullback s4_selected_projection

/-- The actual adjoint curve map supplies a normalized algebraic mixed-divisor kernel. -/
theorem s4_selected_curve_kernel_from_abelian_factor
    (A B Y : Over (Spec ↧ℂ)) [GrpObj A] [IsCommMonObj A] [GrpObj B] [IsCommMonObj B]
    [IsIntegral A.left] [Smooth A.hom] [IsProjective A.hom]
    [IsIntegral B.left] [Smooth B.hom] [IsProjective B.hom]
    [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]
    (hdim : TopologicalSpace.dim Y.left = 1) (I : HQ Y 2 ≃ₗ[ℚ] ℚ)
    (f : Y ⟶ A) (j : Y ⟶ B) (π : B ⟶ A) (s : A ⟶ B) [IsMonHom s] (N : ℕ) (hN : 0 < N)
    (hfac : (homPullback j 1).comp (homPullback π 1) = homPullback f 1)
    (hsec : (homPullback s 1).comp (homPullback π 1) = (N : ℚ) • LinearMap.id)
    (qB : HQ B 2) (hqB : qB ∈ cfd_cycleSpan B 1)
    (hDqB : s4_selected_curve_divisor_operator B Y j I qB = LinearMap.id) :
    ∃ ξ : HQ (A ⊗ Y) 2, ξ ∈ cfd_cycleSpan (A ⊗ Y) 1 ∧
      ∀ v : HQ A 1,
        s4_selected_corr_action A Y 1 I 1 1 1 (by norm_num) ξ
          (homPullback f 1 v) = v := by
  obtain ⟨pA, hpA, f', c, hc, hpair⟩ :=
    s4_selected_curve_adjoint_map_from_abelian_factor A B Y hdim I f j π s N hN
      hfac hsec qB hqB hDqB
  letI := (torusCohomology_cupProductOf A).finite
  let hA := p1_isNondegenerate A hpA
  have hAlgA : pA ∈ cfd_cycleSpan A 1 := by
    unfold cfd_cycleSpan
    exact chowG_lefschetzOneOne_abelian A (p1_mem_hdg A hpA)
  let P := ((cupProductOf Y).cup (show 1 + 1 = 2 from rfl)).compr₂ I.toLinearMap
  have hC (v : HQ A 1) : (P.flip (homPullback f 1 v)).comp (homPullback f' 1) =
      -(c : ℚ) • (contractEquiv hA).symm v := by
    ext w
    exact hpair w v
  let ξ₀ := s4_selected_curve_mixed_divisor A Y f' pA
  have hact (v : HQ A 1) : s4_selected_corr_action A Y 1 I 1 1 1 (by norm_num) ξ₀
      (homPullback f 1 v) = (c : ℚ) • v := by
    have h := s4_selected_curve_mixed_action_contract A Y f' I
      (polarizationVec (torusCohomology_cupProductOf A) pA) (homPullback f 1 v)
    rw [cupWedgeMap_polarizationVec, hC] at h
    simpa only [map_smul, map_neg, contract_contractEquiv_symm, neg_smul, neg_neg] using h
  have hc0 : (c : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hc.ne'
  refine ⟨(c : ℚ)⁻¹ • ξ₀,
    Submodule.smul_mem _ _ (s4_selected_curve_mixed_divisor_mem A Y hdim f' pA hAlgA), ?_⟩
  intro v
  change (s4_selected_kernel_linear_map A Y 1 I 1 1 1 (by norm_num)
    ((c : ℚ)⁻¹ • ξ₀)) (homPullback f 1 v) = v
  rw [map_smul, LinearMap.smul_apply]
  change (c : ℚ)⁻¹ •
    s4_selected_corr_action A Y 1 I 1 1 1 (by norm_num) ξ₀ (homPullback f 1 v) = v
  rw [hact, smul_smul, inv_mul_cancel₀ hc0, one_smul]

#print axioms s4_selected_curve_kernel_from_abelian_factor
end HodgeLean.Foundations.Program
