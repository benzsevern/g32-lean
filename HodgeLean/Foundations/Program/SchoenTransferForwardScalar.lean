import HodgeLean.Foundations.Program.SchoenTransferCharacterSuppliers
import HodgeLean.Foundations.Program.SchoenTransferE1CurveRepresentation

noncomputable section
set_option maxHeartbeats 200000
set_option maxRecDepth 2048
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint MonoidalCategory
open scoped TensorProduct DirectSum BigOperators CategoryTheory.MonObj
open HodgeLean.RealDefs HodgeLean.Adapters HodgeLean.Foundations
namespace HodgeLean.Foundations.Program
attribute [local irreducible] cupProductOf homPullback
/-- Forward residual pullback corresponds to multiplication by the inverse primitive scalar.
Source: Schoen (1988), Remark 1.4, pp. 6–7; the supplied inverse-residual equation. -/
theorem s4_curve_forward_scalar (J : Over (Spec ↧ℂ)) [GrpObj J] [IsCommMonObj J]
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
    ∀ v, homPullback (a (e.symm (.ofAdd 1))) 1 (homPullback f 1 v) =
      homPullback f 1 (cyc_scalar P.act.cyc_coordinates
        (IsCyclotomicExtension.zeta S.m ℚ (cyc_Field S.m))⁻¹ v) := by
  let ζ := IsCyclotomicExtension.zeta S.m ℚ (cyc_Field S.m)
  let δ := e.symm (Multiplicative.ofAdd 1)
  let D := homPullback (a δ) 1
  let B := homPullback (a δ⁻¹) 1
  let T := cyc_scalar P.act.cyc_coordinates ζ
  let Ti := cyc_scalar P.act.cyc_coordinates ζ⁻¹
  obtain ⟨u, hu⟩ := S.surjective (Multiplicative.ofAdd 1)
  have huq : QuotientGroup.mk u = δ := by
    apply e.injective
    rw [he, hu]
    exact (e.apply_symm_apply _).symm
  have hfu : g32p_fieldValue S u = ζ := by
    simp only [g32p_fieldValue, hu, toAdd_ofAdd,
      ZMod.val_one'' (n := S.m) (by have := S.three_le; omega), pow_one]
    rfl
  have hDB : D.comp B = LinearMap.id := by
    dsimp only [D, B]
    rw [← spec_homPullback_comp, ← hamul, mul_inv_cancel, ha1, spec_homPullback_id]
  have hTi : T.comp Ti = LinearMap.id := by
    change cyc_rep P.act.cyc_coordinates ζ * cyc_rep P.act.cyc_coordinates ζ⁻¹ = 1
    rw [← map_mul, mul_inv_cancel₀ ((IsCyclotomicExtension.zeta_spec S.m ℚ
      (cyc_Field S.m)).ne_zero (by have := S.three_le; omega)), map_one]
  intro v
  have hs := hscalar u (Ti v)
  rw [huq, hfu] at hs
  have ht := congrArg D hs
  change D (B (homPullback f 1 (Ti v))) = D (homPullback f 1 (T (Ti v))) at ht
  rw [← LinearMap.comp_apply D B, hDB, LinearMap.id_apply,
    ← LinearMap.comp_apply T Ti, hTi, LinearMap.id_apply] at ht
  exact ht.symm

end HodgeLean.Foundations.Program
