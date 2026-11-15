import HodgeLean.Foundations.Program.SchoenTransferCurvePairing
import HodgeLean.Foundations.Program.SchoenTransferE2ChainDefs
import HodgeLean.Foundations.Program.SchoenTransferE1ExtremeCharacters

noncomputable section
set_option maxHeartbeats 200000
set_option maxRecDepth 2048
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open scoped TensorProduct
open HodgeLean.RealDefs HodgeLean.Adapters HodgeLean.Foundations
namespace HodgeLean.Foundations.Program
attribute [local irreducible] cupProductOf homPullback

/-- The intrinsic primitive embedding space has zero internal degree-two cup product.
Source: Schoen (1988), Lemma 1.1 and Remark 1.4, pp. 5–7. -/
theorem s4_curve_character_pairing_zero
    (S : g32p_Supplier) (Y : Over (Spec ↧ℂ))
    [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]
    (hdim : TopologicalSpace.dim Y.left = 1)
    (a : (S.H ⧸ S.χ.ker) → (Y ⟶ Y))
    (e : (S.H ⧸ S.χ.ker) ≃* Multiplicative (ZMod S.m))
    (ha1 : a 1 = 𝟙 Y) (hamul : ∀ u v, a (u * v) = a u ≫ a v)
    (t : cyc_Field S.m →ₐ[ℚ] ℂ)
    {x y : ℂ ⊗[ℚ] HQ Y 1}
    (hx : x ∈ s4_e2_curveSpace S Y a e t)
    (hy : y ∈ s4_e2_curveSpace S Y a e t) :
    (cupProductOf Y).cupC (show 1 + 1 = 2 from rfl) x y = 0 := by
  obtain ⟨u, hu⟩ := S.surjective (Multiplicative.ofAdd 1)
  have hfu : g32p_fieldValue S u = IsCyclotomicExtension.zeta S.m ℚ (cyc_Field S.m) := by
    simp only [g32p_fieldValue, hu, toAdd_ofAdd,
      ZMod.val_one'' (n := S.m) (by have := S.three_le; omega), pow_one]
    rfl
  have hz : IsPrimitiveRoot (t (g32p_fieldValue S u)) S.m := by
    rw [hfu]
    exact (IsCyclotomicExtension.zeta_spec S.m ℚ (cyc_Field S.m)).map_of_injective t.injective
  letI := s4_e1_curve_action_isIso Y a ha1 hamul ((QuotientGroup.mk u)⁻¹)
  apply s4_curve_equal_character_cup_zero Y hdim (a ((QuotientGroup.mk u)⁻¹))
    (t (g32p_fieldValue S u)) (primitive_character_square_ne_one hz S.three_le)
  · exact Module.End.mem_eigenspace_iff.mp ((Submodule.mem_iInf _).mp hx.2 u)
  · exact Module.End.mem_eigenspace_iff.mp ((Submodule.mem_iInf _).mp hy.2 u)

end HodgeLean.Foundations.Program
