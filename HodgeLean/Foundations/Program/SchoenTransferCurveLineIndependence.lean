import HodgeLean.Foundations.Program.SchoenTransferCharacterSuppliers
import HodgeLean.Foundations.Program.SchoenTransferExteriorImages
import HodgeLean.Foundations.Program.SchoenTransferAlternatingCupInjection

noncomputable section
set_option maxHeartbeats 200000
set_option maxRecDepth 2048
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint MonoidalCategory
open scoped TensorProduct DirectSum BigOperators CategoryTheory.MonObj
open HodgeLean.RealDefs HodgeLean.Adapters HodgeLean.Foundations
namespace HodgeLean.Foundations.Program
/-- The intrinsic alternating images for distinct primitive embeddings are independent.
Source: Schoen (1988), Lemma 1.2 and Remark 1.4, pp. 5–7. -/
theorem s4_curve_line_independence (J : Over (Spec ↧ℂ)) [GrpObj J] [IsCommMonObj J]
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
    iSupIndep (fun t : cyc_Field S.m →ₐ[ℚ] ℂ => (LinearMap.range (exteriorPower.map (2 * P.k) (s4_e2_curveSpace S Y a e t).subtype)).map
        (s4_e2_alternatingCup Y (2 * P.k))) := by
  letI := (torusCohomology_cupProductOf P.P).finite
  have hlines := (cyc_eigenline_decomposition P.act.cyc_order
    (Nat.mul_pos (by norm_num) P.act.cyc_positive) P.act.cyc_coordinates).2
  let F := (homPullback f 1).baseChange ℂ
  let E := exteriorPower.map (2 * P.k) F
  have hF : Function.Injective F := Module.Flat.lTensor_preserves_injective_linearMap _ hf
  have hE : Function.Injective E := exteriorPower.map_injective_field hF
  have hind := (s4_e2_alternatingCup Y (2 * P.k)).iSupIndep_map
    (s4_alternatingCup_injective Y hdim (2 * P.k)) (E.iSupIndep_map hE hlines)
  have ht (t : cyc_Field S.m →ₐ[ℚ] ℂ) :
      (cyc_line P.act.cyc_coordinates t).map E =
        LinearMap.range (exteriorPower.map (2 * P.k) (s4_e2_curveSpace S Y a e t).subtype) := by
    dsimp only [E, F]
    rw [cyc_line, exterior_image_submodule]
    rw [s4_e2_curve_character_transport J aut S P Y hdim a e he ha1 hamul hfaithful f hf himage hscalar t]
    rfl
  simpa only [ht] using hind

end HodgeLean.Foundations.Program
