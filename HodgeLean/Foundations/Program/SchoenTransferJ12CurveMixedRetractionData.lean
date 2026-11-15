import HodgeLean.Foundations.Program.SchoenTransferJ12CurveAdjointKernel

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 4000
open CategoryTheory AlgebraicGeometry MonoidalCategory
open HodgeLean.RealDefs HodgeLean.Adapters HodgeLean.Foundations HodgeLean.Foundations.Symplectic
namespace HodgeLean.Foundations.Program
attribute [local irreducible] cupProductOf homPullback s4_selected_projection

/-- The Abel factor construction retains the actual map, algebraic divisor and positive integral scalar.
Source: the actual cross adjoint and its mixed-divisor contraction formula. -/
theorem s4_selected_curve_mixed_retraction_data
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
    ∃ pol : HQ A 2, pol ∈ cfd_cycleSpan A 1 ∧
      ∃ f' : Y ⟶ A, ∃ c : ℕ, 0 < c ∧
        ∀ v : HQ A 1,
          s4_selected_corr_action A Y 1 I 1 1 1 (by norm_num)
            (s4_selected_curve_mixed_divisor A Y f' pol) (homPullback f 1 v) = (c : ℚ) • v := by
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
  exact ⟨pA, hAlgA, f', c, hc, hact⟩

#print axioms s4_selected_curve_mixed_retraction_data
end HodgeLean.Foundations.Program
