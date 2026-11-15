import HodgeLean.Foundations.Program.SchoenTransferE2ChainDefs
import HodgeLean.Foundations.Program.G32PropFourSixDefs
import HodgeLean.Foundations.Program.SchoenTransferCharacterSuppliers
import HodgeLean.Foundations.Program.SchoenTransferExteriorImages
import HodgeLean.Foundations.Program.SchoenTransferImageScaling
import HodgeLean.Foundations.Program.SchoenTransferCurveLineIndependence
import HodgeLean.Foundations.Program.SchoenTransferCoordinateExpansion
import HodgeLean.Foundations.Program.SchoenTransferAlternatingCoordinates
import HodgeLean.Foundations.Program.SchoenTransferSumComplexCup

/-! Implication from the explicit curve primitive-image and inverse-residual scalar equations
to determinant transport on the exact primitive invariant space.
HC no distance; AV milestone no distance. -/
noncomputable section
set_option maxHeartbeats 200000
set_option maxRecDepth 2048
set_option synthInstance.maxHeartbeats 200000
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint MonoidalCategory
open scoped TensorProduct DirectSum BigOperators CategoryTheory.MonObj
open HodgeLean.RealDefs HodgeLean.Adapters HodgeLean.Foundations
namespace HodgeLean.Foundations.Program
/-- Exterior transport identifies the determinant carrier of every embedding.
Source: Schoen (1988), Hodge classes on self-products of a variety with an automorphism, Remark 1.4, pp. 6–7. -/
theorem s4_chain_curve_character_transport_core (J : Over (Spec ↧ℂ)) [GrpObj J] [IsCommMonObj J]
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
        (exteriorPower.map (2 * P.k) (s4_e2_curveSpace S Y a e t).subtype) := by
  intro t
  rw [cyc_line, exterior_image_submodule]
  rw [s4_e2_curve_character_transport J aut S P Y hdim a e he ha1 hamul hfaithful f hf himage hscalar t]
  rfl

/-- The sum pullback equals the factorial times the normalized alternating coordinate image on each embedding.
Source: Schoen (1988), Hodge classes on self-products of a variety with an automorphism, Remark 1.4, p. 6. -/
theorem s4_chain_sum_wedge_expansion_core (J : Over (Spec ↧ℂ)) [GrpObj J] [IsCommMonObj J]
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
            s4_e2_alternatingCup Y (2 * P.k) ((exteriorPower.map (2 * P.k) ((homPullback f 1).baseChange ℂ)) x) := by
  letI := (torusCohomology_cupProductOf P.P).finite
  refine ⟨Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _), ?_⟩
  intro t x hx
  let U := cyc_eigenspace P.act.cyc_coordinates t
  let F := (homPullback f 1).baseChange ℂ
  let E := exteriorPower.map (2 * P.k) F
  let L := (homPullback (s4_sum f (2 * P.k)) (2 * P.k)).baseChange ℂ ∘ₗ
    ((cupProductOf P.P).cupWedgeMap (2 * P.k)).baseChange ℂ ∘ₗ
    (HodgeBlocks.WeilAction.exteriorPowerBaseChangeEquiv
      (V := HQ P.P 1) (2 * P.k)).symm.toLinearMap
  have ht := s4_e2_curve_character_transport J aut S P Y hdim a e he ha1 hamul hfaithful f hf himage hscalar t
  change U.map F = s4_e2_curveSpace S Y a e t at ht
  have hmaps : L ∘ₗ exteriorPower.map (2 * P.k) U.subtype =
      ((Nat.factorial (2 * P.k) : ℂ) • (s4_e2_alternatingCup Y (2 * P.k) ∘ₗ E)) ∘ₗ
        exteriorPower.map (2 * P.k) U.subtype := by
    apply exteriorPower.linearMap_ext
    apply AlternatingMap.ext
    intro v
    have hv (i : Fin (2 * P.k)) : F (v i) ∈ s4_e2_curveSpace S Y a e t := by
      rw [← ht]
      exact ⟨v i, (v i).property, rfl⟩
    let w : Fin (2 * P.k) → s4_e2_curveSpace S Y a e t := fun i => ⟨F (v i), hv i⟩
    simp only [LinearMap.compAlternatingMap_apply, LinearMap.comp_apply,
      exteriorPower.map_apply_ιMulti, LinearMap.smul_apply]
    dsimp only [L, E]
    rw [s4_sum_complex_cup_generators, exteriorPower.map_apply_ιMulti, s4_alternatingCup_coordinates]
    exact s4_primitive_signed_coordinate_expansion S Y hdim (2 * P.k) a e ha1 hamul t w
  obtain ⟨y, rfl⟩ := hx
  simpa only [L, E, F, U, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearMap.smul_apply, Rat.cast_natCast] using
    LinearMap.congr_fun hmaps y

/-- Each transported determinant line is the intrinsic equal-character alternating image.
Source: Schoen (1988), Hodge classes on self-products of a variety with an automorphism, Lemma 1.2, pp. 5–6; Remark 1.4, pp. 6–7. -/
theorem s4_chain_embedding_line_image_core (J : Over (Spec ↧ℂ)) [GrpObj J] [IsCommMonObj J]
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
        (s4_e2_alternatingCup Y (2 * P.k)) := by
  have htransport := s4_chain_curve_character_transport_core J aut S P Y hdim a e he ha1 hamul hfaithful f hf himage hscalar
  have hexpansion := s4_chain_sum_wedge_expansion_core J aut S P Y hdim a e he ha1 hamul hfaithful f hf himage hscalar
  intro t
  rw [← htransport t, ← Submodule.map_comp]
  apply submodule_image_of_scaled_agreement
    (c := (((Nat.factorial (2 * P.k) : ℚ) : ℂ)))
  · exact_mod_cast hexpansion.1
  · exact hexpansion.2 t

end HodgeLean.Foundations.Program
