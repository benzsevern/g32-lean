import HodgeLean.Foundations.Program.SchoenTransferE2ChainProofs

/-! Implication from the explicit curve primitive-image and inverse-residual scalar equations
to determinant transport on the exact primitive invariant space.
HC no distance; AV milestone no distance. -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint MonoidalCategory
open scoped TensorProduct DirectSum BigOperators CategoryTheory.MonObj
open HodgeLean.RealDefs HodgeLean.Adapters HodgeLean.Foundations
namespace HodgeLean.Foundations.Program
/-- Exterior transport identifies the determinant carrier of every embedding.
Source: Schoen (1988), Hodge classes on self-products of a variety with an automorphism, Remark 1.4, pp. 6–7. -/
theorem s4_chain_curve_character_transport (J : Over (Spec ↧ℂ)) [GrpObj J] [IsCommMonObj J]
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
      (cyc_line P.act.cyc_coordinates t).map (exteriorPower.map (2 * P.k) ((homPullback f 1).baseChange ℂ)) = LinearMap.range
        (exteriorPower.map (2 * P.k) (s4_e2_curveSpace S Y a e t).subtype) :=
  s4_chain_curve_character_transport_aux J aut S P Y hdim a e he ha1 hamul hfaithful f hf himage hscalar

example := @s4_chain_curve_character_transport

/-- The sum pullback equals the factorial times the normalized alternating coordinate image on each embedding.
Source: Schoen (1988), Hodge classes on self-products of a variety with an automorphism, Remark 1.4, p. 6. -/
theorem s4_chain_sum_wedge_expansion (J : Over (Spec ↧ℂ)) [GrpObj J] [IsCommMonObj J]
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
    (Nat.factorial (2 * P.k) : ℚ) ≠ 0 ∧
      ∀ (t : cyc_Field S.m →ₐ[ℚ] ℂ)
        (x : ⋀[ℂ]^(2 * P.k) (ℂ ⊗[ℚ] HQ P.P 1)), x ∈ (cyc_line P.act.cyc_coordinates t) →
        ((homPullback (s4_sum f (2 * P.k)) (2 * P.k)).baseChange ℂ ∘ₗ
            ((cupProductOf P.P).cupWedgeMap (2 * P.k)).baseChange ℂ ∘ₗ
            (HodgeBlocks.WeilAction.exteriorPowerBaseChangeEquiv
              (V := HQ P.P 1) (2 * P.k)).symm.toLinearMap) x =
          (((Nat.factorial (2 * P.k) : ℚ) : ℂ)) •
            s4_e2_alternatingCup Y (2 * P.k) ((exteriorPower.map (2 * P.k) ((homPullback f 1).baseChange ℂ)) x) :=
  s4_chain_sum_wedge_expansion_aux J aut S P Y hdim a e he ha1 hamul hfaithful f hf himage hscalar

example := @s4_chain_sum_wedge_expansion

/-- Each transported determinant line is the intrinsic equal-character alternating image.
Source: Schoen (1988), Hodge classes on self-products of a variety with an automorphism, Lemma 1.2, pp. 5–6; Remark 1.4, pp. 6–7. -/
theorem s4_chain_embedding_line_image (J : Over (Spec ↧ℂ)) [GrpObj J] [IsCommMonObj J]
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
      (cyc_line P.act.cyc_coordinates t).map ((homPullback (s4_sum f (2 * P.k)) (2 * P.k)).baseChange ℂ ∘ₗ
            ((cupProductOf P.P).cupWedgeMap (2 * P.k)).baseChange ℂ ∘ₗ
            (HodgeBlocks.WeilAction.exteriorPowerBaseChangeEquiv
              (V := HQ P.P 1) (2 * P.k)).symm.toLinearMap) =
        (LinearMap.range (exteriorPower.map (2 * P.k) (s4_e2_curveSpace S Y a e t).subtype)).map
        (s4_e2_alternatingCup Y (2 * P.k)) :=
  s4_chain_embedding_line_image_aux J aut S P Y hdim a e he ha1 hamul hfaithful f hf himage hscalar

example := @s4_chain_embedding_line_image

/-- All intrinsic embedding images form a direct sum and exhaust the exact primitive invariant subspace.
Source: Schoen (1988), Hodge classes on self-products of a variety with an automorphism, Lemmas 1.1–1.2, pp. 5–6. -/
theorem s4_chain_embedding_sum_exact (J : Over (Spec ↧ℂ)) [GrpObj J] [IsCommMonObj J]
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
        (s4_e2_alternatingCup Y (2 * P.k))) ∧
      (⨆ t : cyc_Field S.m →ₐ[ℚ] ℂ, (LinearMap.range (exteriorPower.map (2 * P.k) (s4_e2_curveSpace S Y a e t).subtype)).map
        (s4_e2_alternatingCup Y (2 * P.k))) =
        (s4_invariantPrimitive S Y a e (2 * P.k)
          (Nat.mul_pos (by norm_num) P.act.cyc_positive)).baseChange ℂ :=
  s4_chain_embedding_sum_exact_aux J aut S P Y hdim a e he ha1 hamul hfaithful f hf himage hscalar

example := @s4_chain_embedding_sum_exact

/-- The literal embeddingwise equality follows on the specified sum, cup and exterior scalar-extension maps.
Source: Schoen (1988), Hodge classes on self-products of a variety with an automorphism, Remark 1.4, pp. 6–7. -/
theorem s4_chain_embeddingwise_assembly (J : Over (Spec ↧ℂ)) [GrpObj J] [IsCommMonObj J]
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
    (s4_invariantPrimitive S Y a e (2 * P.k) (Nat.mul_pos (by norm_num) P.act.cyc_positive)).baseChange ℂ =
      ⨆ t : cyc_Field S.m →ₐ[ℚ] ℂ,
        (cyc_line P.act.cyc_coordinates t).map
          ((homPullback (s4_sum f (2 * P.k)) (2 * P.k)).baseChange ℂ ∘ₗ
            ((cupProductOf P.P).cupWedgeMap (2 * P.k)).baseChange ℂ ∘ₗ
            (HodgeBlocks.WeilAction.exteriorPowerBaseChangeEquiv
              (V := HQ P.P 1) (2 * P.k)).symm.toLinearMap) :=
  s4_chain_embeddingwise_assembly_aux J aut S P Y hdim a e he ha1 hamul hfaithful f hf himage hscalar

example := @s4_chain_embeddingwise_assembly

end HodgeLean.Foundations.Program
