import HodgeLean.Foundations.Program.SchoenSelectedGeometryPrimitiveTransport
import HodgeLean.Foundations.Program.SchoenSelectedGeometryPrimitiveComparison

noncomputable section
set_option maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open HodgeLean.Adapters HodgeLean.RealDefs HodgeLean.Foundations
open scoped CategoryTheory.MonObj
namespace HodgeLean.Foundations.Program

/-- Primitive quotient comparison supplies the exact square, scalar action, and rational rank. -/
theorem s0_part_primitive_comparison
    (J : Over (Spec ↧ℂ)) [GrpObj J] [IsCommMonObj J] [IsIntegral J.left]
    [Smooth J.hom] [IsProjective J.hom]
    (aut : g32p_G → (J ⟶ J)) (S : g32p_Supplier) (P : g32p_Part J aut S)
    (hP : Function.Injective (homPullback P.proj 1))
    {C Y : Type*} [AddCommGroup C] [Module ℚ C] [AddCommGroup Y] [Module ℚ Y]
    (j : HQ J 1 ≃ₗ[ℚ] C) (q : Y →ₗ[ℚ] C) (hq : Function.Injective q)
    (A : S.H → Module.End ℚ C) (T : S.H → Module.End ℚ Y)
    (B U : Module.End ℚ Y) (hBU : B * U = 1) (hUB : U * B = 1)
    (hj : ∀ h : S.H, j.toLinearMap ∘ₗ homPullback (aut h) 1 = A h ∘ₗ j.toLinearMap)
    (hi : ∀ c, c ∈ LinearMap.range q ↔ ∀ h : S.H, S.χ h = 1 → A h c = c)
    (he : ∀ h : S.H, S.χ h = Multiplicative.ofAdd 1 → q ∘ₗ U = A h ∘ₗ q)
    (hT : ∀ h, q ∘ₗ T h = A h ∘ₗ q) :
    let V := LinearMap.ker (Polynomial.aeval B (Polynomial.cyclotomic S.m ℚ))
    ∃ E : HQ P.P 1 ≃ₗ[ℚ] V,
      (∀ v, q (E v) = j (homPullback P.proj 1 v)) ∧
      (∀ h v, T h (E v) = (E (cyc_scalar P.act.cyc_coordinates (g32p_fieldValue S h) v) : Y)) ∧
      Module.finrank ℚ V = 2 * P.k * Nat.totient S.m := by
  let V := LinearMap.ker (Polynomial.aeval B (Polynomial.cyclotomic S.m ℚ))
  let p := j.toLinearMap ∘ₗ homPullback P.proj 1
  have hp : Function.Injective p := j.injective.comp hP
  have hr : LinearMap.range (q ∘ₗ V.subtype) = LinearMap.range p := by
    rw [LinearMap.range_comp, Submodule.range_subtype]
    have hh := s0_primitive_transport_range S.χ S.surjective j q hq
      (fun h : S.H ↦ homPullback (aut h) 1) A B U hBU hUB hj hi he
    change V.map q = _ at hh
    rw [hh]
    change (g32p_primitive aut S).map j.toLinearMap = LinearMap.range p
    rw [← P.image, LinearMap.range_comp]
  have hep (h : S.H) : p ∘ₗ cyc_scalar P.act.cyc_coordinates (g32p_fieldValue S h) = A h ∘ₗ p := by
    change (j.toLinearMap ∘ₗ homPullback P.proj 1) ∘ₗ _ = _
    rw [LinearMap.comp_assoc, P.equivariant, ← LinearMap.comp_assoc, hj,
      LinearMap.comp_assoc]
  obtain ⟨E, hE, hAct⟩ := s0_equivariant_primitive_lift V p q hp hq hr
    (fun h : S.H ↦ cyc_scalar P.act.cyc_coordinates (g32p_fieldValue S h)) A T hep hT
  refine ⟨E, hE, hAct, ?_⟩
  rw [← E.finrank_eq]
  exact s0_part_finrank J aut S P

#print axioms s0_part_primitive_comparison
end HodgeLean.Foundations.Program
