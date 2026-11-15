import HodgeLean.Foundations.Program.SchoenTransferEmbeddingImageCore
import HodgeLean.Foundations.Program.SchoenTransferCurveGeneratorEigenspace
import HodgeLean.Foundations.Program.SchoenTransferInvariantCriterion
import HodgeLean.Foundations.Program.SchoenTransferTensorEigenImage
import HodgeLean.Foundations.Program.SchoenTransferTupleEigenAction
import HodgeLean.Foundations.Program.SchoenTransferComplexAlternation

noncomputable section
set_option maxHeartbeats 200000
set_option maxRecDepth 2048
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint MonoidalCategory
open scoped TensorProduct DirectSum BigOperators CategoryTheory.MonObj
open HodgeLean.RealDefs HodgeLean.Adapters HodgeLean.Foundations
namespace HodgeLean.Foundations.Program
attribute [local irreducible] cupProductOf homPullback
/-- Each specified intrinsic alternating embedding image lies in the actual primitive invariant space.
Source: Schoen (1988), Lemmas 1.1–1.2 and Remark 1.4, pp. 5–7. -/
theorem s4_embedding_image_le_primitive_invariant (J : Over (Spec ↧ℂ)) [GrpObj J] [IsCommMonObj J]
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
      (LinearMap.range (exteriorPower.map (2 * P.k) (s4_e2_curveSpace S Y a e t).subtype)).map
        (s4_e2_alternatingCup Y (2 * P.k)) ≤
      (s4_invariantPrimitive S Y a e (2 * P.k)
        (Nat.mul_pos (by norm_num) P.act.cyc_positive)).baseChange ℂ := by
  classical
  letI := (torusCohomology_cupProductOf P.P).finite
  have hh : 0 < 2 * P.k := Nat.mul_pos (by norm_num) P.act.cyc_positive
  intro t z hz
  obtain ⟨v, ⟨w, rfl⟩, rfl⟩ := hz
  let W := s4_e2_curveSpace S Y a e t
  let A := (homPullback (a (e.symm (.ofAdd 1))) 1).baseChange ℂ
  let ζ := IsCyclotomicExtension.zeta S.m ℚ (cyc_Field S.m)
  let r := t ζ⁻¹
  let v := exteriorPower.map (2 * P.k) W.subtype w
  let y := exteriorPower.toTensorPower ℂ (ℂ ⊗[ℚ] HQ Y 1) (2 * P.k) v
  let x := s4_e2_alternatingCup Y (2 * P.k) v
  have hWt : W = Module.End.eigenspace A r :=
    s4_curveSpace_eq_forward_eigenspace J aut S P Y hdim a e he ha1 hamul hfaithful f hf himage hscalar t
  have hpr : IsPrimitiveRoot r S.m :=
    ((IsCyclotomicExtension.zeta_spec S.m ℚ (cyc_Field S.m)).inv).map_of_injective t.injective
  have hroot : ((Polynomial.cyclotomic S.m ℚ).map (algebraMap ℚ ℂ)).IsRoot r := by
    rw [Polynomial.map_cyclotomic]
    exact Polynomial.isRoot_cyclotomic_iff.mpr hpr
  have hy : y ∈ LinearMap.range (PiTensorProduct.map (fun _ : Fin (2 * P.k) => W.subtype)) := by
    refine ⟨exteriorPower.toTensorPower ℂ W (2 * P.k) w, ?_⟩
    exact LinearMap.congr_fun (s4_tensorAlternation_map (2 * P.k) W.subtype) w
  have heigen (i : Fin (2 * P.k)) : s4_tensorCoordinate A i y = r • y := by
    rw [hWt] at hy
    exact s4_tensor_eigen_image (2 * P.k) A r hy i
  have hrepr : x = (Nat.factorial (2 * P.k) : ℂ)⁻¹ • s4_complexOneCup Y (2 * P.k) y :=
    LinearMap.congr_fun (s4_alternatingCup_eq_complex_tensor Y (2 * P.k)) v
  have hdeck (i : Fin (2 * P.k)) :
      (homPullback (s2_action S Y a e (2 * P.k) (Pi.single i 1) 1) (2 * P.k)).baseChange ℂ x = r • x := by
    calc
      _ = (Nat.factorial (2 * P.k) : ℂ)⁻¹ •
          (homPullback (s2_action S Y a e (2 * P.k) (Pi.single i 1) 1) (2 * P.k)).baseChange ℂ
            (s4_complexOneCup Y (2 * P.k) y) := by rw [hrepr, map_smul]
      _ = (Nat.factorial (2 * P.k) : ℂ)⁻¹ •
          s4_complexOneCup Y (2 * P.k) (s4_tensorCoordinate A i y) :=
        congrArg ((Nat.factorial (2 * P.k) : ℂ)⁻¹ • ·)
          (LinearMap.congr_fun (s4_curve_tensor_coordinate_action S Y a e ha1 (2 * P.k) i) y)
      _ = (Nat.factorial (2 * P.k) : ℂ)⁻¹ • (r • s4_complexOneCup Y (2 * P.k) y) := by
        rw [heigen, map_smul]
      _ = r • x := by rw [hrepr, smul_comm]
  have hperm (σ : Equiv.Perm (Fin (2 * P.k))) :
      (homPullback (s2_permute Y (2 * P.k) σ) (2 * P.k)).baseChange ℂ x = x := by
    have hximage : x ∈ (LinearMap.range (exteriorPower.map (2 * P.k) W.subtype)).map
        (s4_e2_alternatingCup Y (2 * P.k)) := ⟨v, ⟨w, rfl⟩, rfl⟩
    rw [← s4_chain_embedding_line_image_core J aut S P Y hdim a e he ha1 hamul hfaithful f hf himage hscalar t] at hximage
    obtain ⟨u, hu, hux⟩ := hximage
    have hmap : homPullback (s2_permute Y (2 * P.k) σ) (2 * P.k) ∘ₗ
        homPullback (s4_sum f (2 * P.k)) (2 * P.k) =
        homPullback (s4_sum f (2 * P.k)) (2 * P.k) :=
      LinearMap.ext (s4_sum_pullback_permute P.P Y f (2 * P.k) (2 * P.k) σ)
    have hb := congrArg (LinearMap.baseChange ℂ) hmap
    rw [LinearMap.baseChange_comp] at hb
    rw [← hux]
    change ((homPullback (s2_permute Y (2 * P.k) σ) (2 * P.k)).baseChange ℂ ∘ₗ
      (homPullback (s4_sum f (2 * P.k)) (2 * P.k)).baseChange ℂ) _ = _
    rw [hb]
    rfl
  apply (s4_primitive_baseChange_mem_iff S Y (2 * P.k) hh a e x).mpr
  constructor
  · have hd : s2_delta S (2 * P.k) hh 1 = Pi.single (⟨0, hh⟩ : Fin (2 * P.k)) 1 := by
      ext i
      simp only [s2_delta, Pi.single_apply]
    rw [baseChange_aeval, hd, Module.End.aeval_apply_of_mem_apply_eq_smul (hdeck ⟨0, hh⟩), hroot, zero_smul]
  · intro v hv σ
    let ρ := (Module.End.baseChangeHom ℚ ℂ (HQ (g3_power Y (2 * P.k)) (2 * P.k))).toMonoidHom.comp
      (s4_e1_deckPullbackRepresentation S Y a e ha1 hamul (2 * P.k) (2 * P.k))
    have hfixed := s4_sum_zero_tuple_eigen_fixed S.m ρ x r hpr.pow_eq_one hdeck v hv
    change (homPullback (s2_action S Y a e (2 * P.k) v 1) (2 * P.k)).baseChange ℂ x = x at hfixed
    rw [s4_deck_permutation_factor, spec_homPullback_comp, LinearMap.baseChange_comp,
      LinearMap.comp_apply, hfixed, hperm]

end HodgeLean.Foundations.Program
