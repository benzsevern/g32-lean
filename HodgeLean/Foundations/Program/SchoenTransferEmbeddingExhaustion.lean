import HodgeLean.Foundations.Program.SchoenTransferCurveGeneratorEigenspace
import HodgeLean.Foundations.Program.SchoenTransferPrimitiveTensorLift
import HodgeLean.Foundations.Program.SchoenTransferTensorPrimitiveDecomposition
import HodgeLean.Foundations.Program.SchoenTransferComplexAlternation

noncomputable section
set_option maxHeartbeats 200000
set_option maxRecDepth 2048
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint MonoidalCategory
open scoped TensorProduct DirectSum BigOperators CategoryTheory.MonObj
open HodgeLean.RealDefs HodgeLean.Adapters HodgeLean.Foundations
namespace HodgeLean.Foundations.Program
attribute [local irreducible] cupProductOf homPullback
/-- Every actual primitive invariant class lies in the sum of the intrinsic alternating embedding images.
Source: Schoen (1988), Lemmas 1.1–1.2 and Remark 1.4, pp. 5–7. -/
theorem s4_primitive_invariant_le_embedding_sum (J : Over (Spec ↧ℂ)) [GrpObj J] [IsCommMonObj J]
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
    (s4_invariantPrimitive S Y a e (2 * P.k)
      (Nat.mul_pos (by norm_num) P.act.cyc_positive)).baseChange ℂ ≤
      ⨆ t : cyc_Field S.m →ₐ[ℚ] ℂ,
        (LinearMap.range (exteriorPower.map (2 * P.k)
          (s4_e2_curveSpace S Y a e t).subtype)).map (s4_e2_alternatingCup Y (2 * P.k)) := by
  classical
  letI := (finbetti_finiteBetti Y).finite 1
  let A := (homPullback (a (e.symm (.ofAdd 1))) 1).baseChange ℂ
  let Q := (Polynomial.cyclotomic S.m ℚ).map (algebraMap ℚ ℂ)
  have hh : 0 < 2 * P.k := Nat.mul_pos (by norm_num) P.act.cyc_positive
  letI := Fintype.ofFinite (rootsOfUnity S.m ℂ)
  let D := s4_e1_curve_character_decomposition S Y a e ha1 hamul 1
  let b := D.collectedBasis (fun r : rootsOfUnity S.m ℂ =>
    Module.finBasis ℂ (Module.End.eigenspace A ((r : ℂˣ) : ℂ)))
  have hb (i) : A (b i) = ((i.1 : ℂˣ) : ℂ) • b i :=
    Module.End.mem_eigenspace_iff.mp (D.collectedBasis_mem _ i)
  intro z hz
  obtain ⟨y, rfl⟩ := s4_primitive_complex_tensor_preimage S Y hdim (2 * P.k) hh a e ha1 hamul hz
  have hy := s4_primitive_complex_tensor_equations S Y hdim (2 * P.k) hh a e ha1 hamul hz
  have hp := s4_primitive_complex_tensor_polynomial S Y hdim (2 * P.k) hh a e ha1 hamul hz
  have hcore := s4_primitive_tensor_exhaustion b A (fun i => ((i.1 : ℂˣ) : ℂ)) hb
    (2 * P.k) (⟨0, hh⟩ : Fin (2 * P.k)) Q hp
    (fun i => hy.1 i ⟨0, hh⟩) hy.2
  have hle : (⨆ r : {r : ℂ // Q.IsRoot r}, LinearMap.range
      ((exteriorPower.toTensorPower ℂ (ℂ ⊗[ℚ] HQ Y 1) (2 * P.k)).comp
        (exteriorPower.map (2 * P.k) (Module.End.eigenspace A r.val).subtype))) ≤
      (⨆ t : cyc_Field S.m →ₐ[ℚ] ℂ,
        (LinearMap.range (exteriorPower.map (2 * P.k)
          (s4_e2_curveSpace S Y a e t).subtype)).map (s4_e2_alternatingCup Y (2 * P.k))).comap
          (s4_complexOneCup Y (2 * P.k)) := by
    apply iSup_le
    intro r
    obtain ⟨t, ht⟩ := s4_embedding_of_cyclotomic_root S.m
      (lt_of_lt_of_le (by norm_num : 0 < 3) S.three_le) r.val r.property
    have hWt : s4_e2_curveSpace S Y a e t = Module.End.eigenspace A r.val := by
      rw [s4_curveSpace_eq_forward_eigenspace J aut S P Y hdim a e he ha1 hamul hfaithful f hf himage hscalar t]
      simpa only [A, map_inv₀] using congrArg (Module.End.eigenspace A) ht
    rw [← hWt]
    rintro _ ⟨w, rfl⟩
    change s4_complexOneCup Y (2 * P.k)
      (exteriorPower.toTensorPower ℂ (ℂ ⊗[ℚ] HQ Y 1) (2 * P.k)
        (exteriorPower.map (2 * P.k) (s4_e2_curveSpace S Y a e t).subtype w)) ∈
        (⨆ t : cyc_Field S.m →ₐ[ℚ] ℂ,
          (LinearMap.range (exteriorPower.map (2 * P.k)
            (s4_e2_curveSpace S Y a e t).subtype)).map (s4_e2_alternatingCup Y (2 * P.k)))
    rw [← LinearMap.comp_apply, s4_complexOneCup_tensorAlternation, LinearMap.smul_apply]
    apply Submodule.smul_mem
    exact Submodule.mem_iSup_of_mem t ⟨_, ⟨w, rfl⟩, rfl⟩
  exact hle hcore

end HodgeLean.Foundations.Program
