import HodgeLean.Foundations.Program.SchoenTransferJ12CurveMap
import HodgeLean.Foundations.Program.SchoenTransferJ12FinitePullback
import HodgeLean.Foundations.Program.SchoenTransferJ12QuotientFinite
import HodgeLean.Foundations.Program.SchoenTransferJ12CurveMapNormalization

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 4000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open HodgeLean.Adapters HodgeLean.RealDefs HodgeLean.Foundations
namespace HodgeLean.Foundations.Program
attribute [local irreducible] homPullback

/-- Construct the C2 map on the retained curve and primitive carrier of the native square. -/
theorem s4_selected_native_curve_map
    (J : Over (Spec ↧ℂ)) [GrpObj J] [IsCommMonObj J]
    [IsIntegral J.left] [Smooth J.hom] [IsProjective J.hom]
    (aut : g32p_G → (J ⟶ J)) (S : g32p_Supplier) (P : g32p_Part J aut S)
    (Y C₀ : Over (Spec ↧ℂ))
    [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]
    [IsIntegral C₀.left] [Smooth C₀.hom] [IsProjective C₀.hom]
    (hdimY : TopologicalSpace.dim Y.left = 1)
    (a : (S.H ⧸ S.χ.ker) → (Y ⟶ Y))
    (e : (S.H ⧸ S.χ.ker) ≃* Multiplicative (ZMod S.m))
    (C : Type) [MulAction g32p_G C]
    (eC : C ≃ ComplexPoint C₀) (eY : rsq_Quot S.χ.ker C ≃ ComplexPoint Y)
    (qC : C₀ ⟶ Y) (jC : C₀ ⟶ J)
    (hqC : ∀ x, Point.map qC (eC x) = eY (rsq_proj S.χ.ker C x))
    (primitive : HQ P.P 1 ≃ₗ[ℚ] LinearMap.ker
      (Polynomial.aeval (homPullback (a (e.symm (Multiplicative.ofAdd 1))) 1)
        (Polynomial.cyclotomic S.m ℚ)))
    (hprimitive : ∀ v, homPullback qC 1 (primitive v : HQ Y 1) =
      homPullback jC 1 (homPullback P.proj 1 v))
    (hscalar : ∀ (u : S.H) v,
      homPullback (a ((QuotientGroup.mk u)⁻¹)) 1 (primitive v : HQ Y 1) =
        (primitive (cyc_scalar P.act.cyc_coordinates (g32p_fieldValue S u) v) : HQ Y 1)) :
    ∃ (N : ℕ) (fselected : Y ⟶ P.P), 0 < N ∧
      (∀ v, homPullback fselected 1 v = (N : ℚ) • (primitive v : HQ Y 1)) ∧
      Function.Injective (homPullback fselected 1) ∧
      LinearMap.range (homPullback fselected 1) = LinearMap.ker
        (Polynomial.aeval (homPullback (a (e.symm (Multiplicative.ofAdd 1))) 1)
          (Polynomial.cyclotomic S.m ℚ)) ∧
      ∀ (u : S.H) v,
        homPullback (a ((QuotientGroup.mk u)⁻¹)) 1 (homPullback fselected 1 v) =
          homPullback fselected 1 (cyc_scalar P.act.cyc_coordinates (g32p_fieldValue S u) v) := by
  classical
  letI : IsFinite qC.left := s4_selected_orbit_projection_finite
    S.χ.ker C C₀ Y qC eC eY hqC
  have hsurj : Function.Surjective (Point.map qC) := by
    intro y
    let c := Quotient.out (eY.symm y)
    refine ⟨eC c, (hqC c).trans ?_⟩
    change eY (Quotient.mk _ (Quotient.out (eY.symm y))) = y
    rw [Quotient.out_eq, eY.apply_symm_apply]
  have hdimC := s4_selected_finite_curve_source_dimension C₀ Y hdimY qC hsurj
  have hinj := s4_selected_finite_curve_pullback C₀ Y hdimY qC hsurj
  let K := LinearMap.ker
    (Polynomial.aeval (homPullback (a (e.symm (Multiplicative.ofAdd 1))) 1)
      (Polynomial.cyclotomic S.m ℚ))
  let T := K.subtype.comp primitive.toLinearMap
  have hsq : (homPullback qC 1).comp T = homPullback (jC ≫ P.proj) 1 := by
    rw [spec_homPullback_comp]
    ext v
    exact hprimitive v
  obtain ⟨N, f, hN, hf⟩ := s4_selected_curve_map_of_square C₀ Y P.P hdimC hdimY
    qC hinj (jC ≫ P.proj) T hsq
  have hf' : ∀ v, homPullback f 1 v = (N : ℚ) • (primitive v : HQ Y 1) := hf
  obtain ⟨hi, hr, ha⟩ := s4_selected_curve_map_normalization J aut S P Y a e
    primitive hscalar N hN f hf'
  exact ⟨N, f, hN, hf', hi, hr, ha⟩

#print axioms s4_selected_native_curve_map

end HodgeLean.Foundations.Program
