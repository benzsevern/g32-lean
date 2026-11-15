import HodgeLean.Foundations.Program.SchoenTransferE2Chain
import HodgeLean.Foundations.Program.SchoenTransferLinear

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
open HodgeLean.Adapters HodgeLean.RealDefs HodgeLean.Foundations
open scoped TensorProduct BigOperators
namespace HodgeLean.Foundations.Program

/-- Rational descent of the embeddingwise sum image on the retained curve power. -/
theorem s4_selected_rational_primitive_image (J : Over (Spec ↧ℂ)) [GrpObj J] [IsCommMonObj J]
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
    (cyc_classSpace (cupProductOf P.P) P.act.cyc_coordinates).map
      (homPullback (s4_sum f (2 * P.k)) (2 * P.k)) =
      s4_invariantPrimitive S Y a e (2 * P.k)
        (Nat.mul_pos (by norm_num) P.act.cyc_positive) := by
  apply Submodule.baseChange_injective (A := ℂ)
  rw [cyc_classSpace, s4_determinant_transport_baseChange]
  exact (s4_chain_embeddingwise_assembly J aut S P Y hdim a e he ha1 hamul
    hfaithful f hf himage hscalar).symm

#print axioms s4_selected_rational_primitive_image

end HodgeLean.Foundations.Program
