import HodgeLean.Foundations.Program.SchoenTransferForwardScalar
import HodgeLean.Foundations.Program.SchoenTransferCyclotomicEigenGenerator
import HodgeLean.Foundations.Program.SchoenTransferEigenspaceRange
import HodgeLean.Foundations.Program.SchoenTransferBaseChangeRange
import HodgeLean.Foundations.Program.SchoenTransferE2ChainDefs

noncomputable section
set_option maxHeartbeats 200000
set_option maxRecDepth 2048
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint MonoidalCategory
open scoped TensorProduct DirectSum BigOperators CategoryTheory.MonObj
open HodgeLean.RealDefs HodgeLean.Adapters HodgeLean.Foundations
namespace HodgeLean.Foundations.Program
attribute [local irreducible] cupProductOf homPullback
/-- Each intrinsic curve character space is the exact forward-generator eigenspace.
Source: Schoen (1988), Remark 1.4, pp. 6–7; the actual primitive-image and scalar equations. -/
theorem s4_curveSpace_eq_forward_eigenspace (J : Over (Spec ↧ℂ)) [GrpObj J] [IsCommMonObj J]
    [IsIntegral J.left] [Smooth J.hom] [IsProjective J.hom]
    (aut : g32p_G → (J ⟶ J)) (S : g32p_Supplier)
    (P : g32p_Part J aut S)
    (Y : Over (Spec ↧ℂ)) [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]
    (hdim : TopologicalSpace.dim Y.left = 1)
    [IsIntegral (g3_power Y (2 * P.k)).left]
    [Smooth (g3_power Y (2 * P.k)).hom]
    [IsProjective (g3_power Y (2 * P.k)).hom]
    (a : (S.H ⧸ S.χ.ker) → (Y ⟶ Y))
    (e : (S.H ⧸ S.χ.ker) ≃* Multiplicative (ZMod S.m))
    (he : ∀ u : S.H, e (QuotientGroup.mk u) = S.χ u)
    (ha1 : a 1 = 𝟙 Y) (hamul : ∀ u v, a (u * v) = a u ≫ a v)
    (hfaithful : Function.Injective a)
    (f : Y ⟶ P.P) (hf : Function.Injective (homPullback f 1))
    (himage : LinearMap.range (homPullback f 1) = LinearMap.ker
      (Polynomial.aeval (homPullback (a (e.symm (Multiplicative.ofAdd 1))) 1)
        (Polynomial.cyclotomic S.m ℚ)))
    (hscalar : ∀ (u : S.H) v,
      homPullback (a ((QuotientGroup.mk u)⁻¹)) 1 (homPullback f 1 v) =
        homPullback f 1 (cyc_scalar P.act.cyc_coordinates (g32p_fieldValue S u) v)) :
    ∀ t : cyc_Field S.m →ₐ[ℚ] ℂ,
      s4_e2_curveSpace S Y a e t = Module.End.eigenspace
        ((homPullback (a (e.symm (.ofAdd 1))) 1).baseChange ℂ)
        (t ((IsCyclotomicExtension.zeta S.m ℚ (cyc_Field S.m))⁻¹)) := by
  intro t
  let ζ := IsCyclotomicExtension.zeta S.m ℚ (cyc_Field S.m)
  let F := (homPullback f 1).baseChange ℂ
  let A := (homPullback (a (e.symm (.ofAdd 1))) 1).baseChange ℂ
  let T := (cyc_scalar P.act.cyc_coordinates ζ⁻¹).baseChange ℂ
  let Q := (Polynomial.cyclotomic S.m ℚ).map (algebraMap ℚ ℂ)
  have hζ : IsPrimitiveRoot ζ⁻¹ S.m := (IsCyclotomicExtension.zeta_spec S.m ℚ (cyc_Field S.m)).inv
  have hF : Function.Injective F := Module.Flat.lTensor_preserves_injective_linearMap _ hf
  have hr : LinearMap.range F = LinearMap.ker (Polynomial.aeval A Q) := by
    dsimp only [F, A, Q]
    rw [s4_baseChange_range, himage, ← ker_baseChange, baseChange_aeval]
  have hFA : ∀ x, A (F x) = F (T x) := by
    have hh : homPullback (a (e.symm (.ofAdd 1))) 1 ∘ₗ homPullback f 1 =
        homPullback f 1 ∘ₗ cyc_scalar P.act.cyc_coordinates ζ⁻¹ :=
      LinearMap.ext (s4_curve_forward_scalar J aut S P Y hdim a e he ha1 hamul hfaithful f hf himage hscalar)
    have hb := congrArg (LinearMap.baseChange ℂ) hh
    rw [LinearMap.baseChange_comp, LinearMap.baseChange_comp] at hb
    exact LinearMap.congr_fun hb
  have hroot : Q.IsRoot (t ζ⁻¹) := by
    dsimp only [Q]
    rw [Polynomial.map_cyclotomic]
    exact Polynomial.isRoot_cyclotomic_iff.mpr (hζ.map_of_injective t.injective)
  have ht := s4_e2_curve_character_transport J aut S P Y hdim a e he ha1 hamul hfaithful f hf himage hscalar t
  change (cyc_eigenspace P.act.cyc_coordinates t).map F = s4_e2_curveSpace S Y a e t at ht
  rw [← ht, s4_cyclotomic_eigenspace_primitive_generator P.act.cyc_coordinates t ζ⁻¹ hζ]
  exact s4_eigenspace_map_of_polynomial_range F T A Q hF hFA hr (t ζ⁻¹) hroot

end HodgeLean.Foundations.Program
