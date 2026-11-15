import HodgeLean.Foundations.Program.SchoenTransferJ12CrossAdjointHodge
import HodgeLean.Foundations.Program.SchoenTransferJ12CurveInverseForm
import HodgeLean.Foundations.Program.MilneFactorsHodgeSemisimple
import HodgeLean.Foundations.DivisorClassHodge

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 4000
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint MonoidalCategory
open HodgeLean.RealDefs HodgeLean.Adapters HodgeLean.Foundations HodgeLean.Foundations.Symplectic
namespace HodgeLean.Foundations.Program
attribute [local irreducible] cupProductOf homPullback s4_selected_projection

/-- The actual Abel factor and multiplication section supply a curve map adjoint to the generating map. -/
theorem s4_selected_curve_adjoint_map_from_abelian_factor
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
    ∃ pA : HQ A 2, ∃ hpA : p1_IsPolarization A pA,
      ∃ f' : Y ⟶ A, ∃ c : ℕ, 0 < c ∧
        ∀ w v : HQ A 1,
          I ((cupProductOf Y).cup rfl (homPullback f' 1 w) (homPullback f 1 v)) =
            -(c : ℚ) * polarizationForm (torusCohomology_cupProductOf A)
              (p1_isNondegenerate A hpA) w v := by
  letI := (torusCohomology_cupProductOf A).finite
  letI := (torusCohomology_cupProductOf B).finite
  obtain ⟨hB, hform⟩ := s4_selected_curve_identity_divisor_form B Y j I qB hDqB
  obtain ⟨pA, hpA⟩ := m1_exists_positive_polarization A
  let hA := p1_isNondegenerate A hpA
  have hHodgeB : (qB : H^(2 * 1)(B; ℚ)) ∈ Hdg^1(B; ℚ) :=
    dc1_divisorClass_le_hodge B hqB
  let G := s4_selected_cross_adjoint hB hA (homPullback s 1)
  have hG := s4_selected_cross_adjoint_holomorphic A B pA qB hA hB
    (p1_mem_hdg A hpA) hHodgeB s
  obtain ⟨M, hM, g, hg, hgp⟩ := b60c_hom_of_holomorphic B A G hG
  let f' := j ≫ g
  let EA := polarizationForm (torusCohomology_cupProductOf A) hA
  let EB := polarizationForm (torusCohomology_cupProductOf B) hB
  have hcurve (x y : HQ B 1) :
      I ((cupProductOf Y).cup rfl (homPullback j 1 x) (homPullback j 1 y)) = -EB x y := by
    have h := hform x y
    change EB x y = -I ((cupProductOf Y).cup rfl (homPullback j 1 x) (homPullback j 1 y)) at h
    simpa only [neg_neg] using (congrArg (fun z : ℚ => -z) h).symm
  have hAskew (x y : HQ A 1) : EA x y = -EA y x :=
    ((isAlt_polarizationForm (torusCohomology_cupProductOf A) hA).neg_eq y x).symm
  have hBskew (x y : HQ B 1) : EB x y = -EB y x :=
    ((isAlt_polarizationForm (torusCohomology_cupProductOf B) hB).neg_eq y x).symm
  have hadj (x : HQ B 1) (y : HQ A 1) : EA (homPullback s 1 x) y = EB x (G y) :=
    s4_selected_cross_adjoint_pairing hB hA (homPullback s 1) x y
  have hff (w : HQ A 1) : homPullback f' 1 w =
      (M : ℚ) • homPullback j 1 (G w) := by
    simp only [f', spec_homPullback_comp, hgp, LinearMap.comp_apply,
      LinearMap.smul_apply, map_smul]
  have hfactor (v : HQ A 1) : homPullback f 1 v =
      homPullback j 1 (homPullback π 1 v) := (LinearMap.congr_fun hfac v).symm
  have hsection (v : HQ A 1) : homPullback s 1 (homPullback π 1 v) = (N : ℚ) • v :=
    LinearMap.congr_fun hsec v
  let P := ((cupProductOf Y).cup (show 1 + 1 = 2 from rfl)).compr₂ I.toLinearMap
  have hC (v : HQ A 1) : (P.flip (homPullback f 1 v)).comp (homPullback f' 1) =
      -((M : ℚ) * (N : ℚ)) • (contractEquiv hA).symm v := by
    ext w
    change I ((cupProductOf Y).cup rfl (homPullback f' 1 w) (homPullback f 1 v)) =
      -((M : ℚ) * (N : ℚ)) * ((contractEquiv hA).symm v) w
    calc
      _ = (M : ℚ) * I ((cupProductOf Y).cup rfl
          (homPullback j 1 (G w)) (homPullback j 1 (homPullback π 1 v))) := by
        rw [hff, hfactor]
        simp only [map_smul, LinearMap.smul_apply, RingHom.id_apply, smul_eq_mul]
      _ = (M : ℚ) * EB (homPullback π 1 v) (G w) := by
        rw [hcurve, hBskew (G w) (homPullback π 1 v), neg_neg]
      _ = (M : ℚ) * EA (homPullback s 1 (homPullback π 1 v)) w := by rw [hadj]
      _ = ((M : ℚ) * (N : ℚ)) * EA v w := by
        rw [hsection]
        simp only [map_smul, LinearMap.smul_apply, RingHom.id_apply, smul_eq_mul]
        ring
      _ = _ := by
        rw [hAskew]
        change (M : ℚ) * (N : ℚ) * -((contractEquiv hA).symm v) w = _
        ring
  refine ⟨pA, hpA, f', M * N, Nat.mul_pos hM hN, ?_⟩
  intro w v
  have h := LinearMap.congr_fun (hC v) w
  change I ((cupProductOf Y).cup rfl (homPullback f' 1 w) (homPullback f 1 v)) =
    -((M : ℚ) * (N : ℚ)) * EA w v at h
  simpa only [Nat.cast_mul] using h

#print axioms s4_selected_curve_adjoint_map_from_abelian_factor
end HodgeLean.Foundations.Program
