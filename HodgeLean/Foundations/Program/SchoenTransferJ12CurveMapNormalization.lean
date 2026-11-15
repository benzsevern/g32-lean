import HodgeLean.Foundations.Program.SchoenTransferDefs
import HodgeLean.Foundations.Program.SchoenTransferComparison
import HodgeLean.Foundations.Program.G32PropFourSixDefs

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
open HodgeLean.Adapters HodgeLean.RealDefs
namespace HodgeLean.Foundations.Program

/-- The exact positive-integer pullback equation retains the primitive image and action. -/
theorem s4_selected_curve_map_normalization
    (J : Over (Spec ↧ℂ)) [GrpObj J] [IsCommMonObj J]
    [IsIntegral J.left] [Smooth J.hom] [IsProjective J.hom]
    (aut : g32p_G → (J ⟶ J)) (S : g32p_Supplier) (P : g32p_Part J aut S)
    (Y : Over (Spec ↧ℂ)) [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]
    (a : (S.H ⧸ S.χ.ker) → (Y ⟶ Y))
    (e : (S.H ⧸ S.χ.ker) ≃* Multiplicative (ZMod S.m))
    (primitive : HQ P.P 1 ≃ₗ[ℚ] LinearMap.ker
      (Polynomial.aeval (homPullback (a (e.symm (Multiplicative.ofAdd 1))) 1)
        (Polynomial.cyclotomic S.m ℚ)))
    (hscalar : ∀ (u : S.H) v,
      homPullback (a ((QuotientGroup.mk u)⁻¹)) 1 (primitive v : HQ Y 1) =
        (primitive (cyc_scalar P.act.cyc_coordinates (g32p_fieldValue S u) v) : HQ Y 1))
    (N : ℕ) (hN : 0 < N) (f : Y ⟶ P.P)
    (hf : ∀ v, homPullback f 1 v = (N : ℚ) • (primitive v : HQ Y 1)) :
    Function.Injective (homPullback f 1) ∧
      LinearMap.range (homPullback f 1) = LinearMap.ker
        (Polynomial.aeval (homPullback (a (e.symm (Multiplicative.ofAdd 1))) 1)
          (Polynomial.cyclotomic S.m ℚ)) ∧
      ∀ (u : S.H) v,
        homPullback (a ((QuotientGroup.mk u)⁻¹)) 1 (homPullback f 1 v) =
          homPullback f 1 (cyc_scalar P.act.cyc_coordinates (g32p_fieldValue S u) v) := by
  have hNq : (N : ℚ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hN
  obtain ⟨hinj, himage⟩ := s4_scaled_submodule_comparison _ primitive
    (homPullback f 1) (N : ℚ) hNq hf
  refine ⟨hinj, himage, ?_⟩
  intro u v
  rw [hf, map_smul, hscalar, hf]

#print axioms s4_selected_curve_map_normalization

end HodgeLean.Foundations.Program
