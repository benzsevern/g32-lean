import HodgeLean.Foundations.Program.G32Native.PrimitiveGenerator
import HodgeLean.Foundations.Program.SchoenTransferEmbeddingExhaustion

/-! # Primitive tensor exhaustion from the supplied linear comparison -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
set_option maxRecDepth 2048
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint MonoidalCategory
open scoped TensorProduct DirectSum BigOperators CategoryTheory.MonObj
open HodgeLean.RealDefs HodgeLean.Adapters HodgeLean.Foundations
open HodgeLean.Foundations.Program
namespace HodgeLean.Foundations.Program.G32Native.TowerOrbit
attribute [local irreducible] cupProductOf homPullback

/-- Actual primitive invariant classes lie in the intrinsic top-exterior character images. -/
theorem primitive_invariant_embedding_sum
    (S : g32p_Supplier) (Y : Over (Spec ↧ℂ))
    [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]
    (hdim : TopologicalSpace.dim Y.left = 1) (k : ℕ) (hk : 0 < k)
    [IsIntegral (g3_power Y (2 * k)).left]
    [Smooth (g3_power Y (2 * k)).hom] [IsProjective (g3_power Y (2 * k)).hom]
    (a : (S.H ⧸ S.χ.ker) → (Y ⟶ Y))
    (e : (S.H ⧸ S.χ.ker) ≃* Multiplicative (ZMod S.m))
    (he : ∀ u : S.H, e (QuotientGroup.mk u) = S.χ u)
    (ha1 : a 1 = 𝟙 Y) (hamul : ∀ u v, a (u * v) = a u ≫ a v)
    {V : Type*} [AddCommGroup V] [Module ℚ V]
    (coords : V ≃ₗ[ℚ] (Fin (2 * k) → cyc_Field S.m))
    (F : V →ₗ[ℚ] HQ Y 1) (hf : Function.Injective F)
    (himage : LinearMap.range F = LinearMap.ker
      (Polynomial.aeval (homPullback (a (e.symm (Multiplicative.ofAdd 1))) 1)
        (Polynomial.cyclotomic S.m ℚ)))
    (hscalar : ∀ (u : S.H) v,
      homPullback (a ((QuotientGroup.mk u)⁻¹)) 1 (F v) =
        F (cyc_scalar coords (g32p_fieldValue S u) v)) :
    (s4_invariantPrimitive S Y a e (2 * k)
      (Nat.mul_pos (by norm_num) hk)).baseChange ℂ ≤
      ⨆ t : cyc_Field S.m →ₐ[ℚ] ℂ,
        (LinearMap.range (exteriorPower.map (2 * k)
          (s4_e2_curveSpace S Y a e t).subtype)).map (s4_e2_alternatingCup Y (2 * k)) := by
  classical
  letI := (finbetti_finiteBetti Y).finite 1
  let A := (homPullback (a (e.symm (.ofAdd 1))) 1).baseChange ℂ
  let Q := (Polynomial.cyclotomic S.m ℚ).map (algebraMap ℚ ℂ)
  have hh : 0 < 2 * k := Nat.mul_pos (by norm_num) hk
  letI := Fintype.ofFinite (rootsOfUnity S.m ℂ)
  let D := s4_e1_curve_character_decomposition S Y a e ha1 hamul 1
  let b := D.collectedBasis (fun r : rootsOfUnity S.m ℂ =>
    Module.finBasis ℂ (Module.End.eigenspace A ((r : ℂˣ) : ℂ)))
  have hb (i) : A (b i) = ((i.1 : ℂˣ) : ℂ) • b i :=
    Module.End.mem_eigenspace_iff.mp (D.collectedBasis_mem _ i)
  intro z hz
  obtain ⟨y, rfl⟩ := s4_primitive_complex_tensor_preimage S Y hdim (2 * k) hh a e ha1 hamul hz
  have hy := s4_primitive_complex_tensor_equations S Y hdim (2 * k) hh a e ha1 hamul hz
  have hp := s4_primitive_complex_tensor_polynomial S Y hdim (2 * k) hh a e ha1 hamul hz
  have hcore := s4_primitive_tensor_exhaustion b A (fun i => ((i.1 : ℂˣ) : ℂ)) hb
    (2 * k) (⟨0, hh⟩ : Fin (2 * k)) Q hp
    (fun i => hy.1 i ⟨0, hh⟩) hy.2
  have hle : (⨆ r : {r : ℂ // Q.IsRoot r}, LinearMap.range
      ((exteriorPower.toTensorPower ℂ (ℂ ⊗[ℚ] HQ Y 1) (2 * k)).comp
        (exteriorPower.map (2 * k) (Module.End.eigenspace A r.val).subtype))) ≤
      (⨆ t : cyc_Field S.m →ₐ[ℚ] ℂ,
        (LinearMap.range (exteriorPower.map (2 * k)
          (s4_e2_curveSpace S Y a e t).subtype)).map (s4_e2_alternatingCup Y (2 * k))).comap
          (s4_complexOneCup Y (2 * k)) := by
    apply iSup_le
    intro r
    obtain ⟨t, ht⟩ := s4_embedding_of_cyclotomic_root S.m
      (lt_of_lt_of_le (by norm_num : 0 < 3) S.three_le) r.val r.property
    have hWt : s4_e2_curveSpace S Y a e t = Module.End.eigenspace A r.val := by
      rw [primitive_generator_eigenspace S Y a e he ha1 hamul (2 * k) coords F hf himage hscalar t]
      simpa only [A, map_inv₀] using congrArg (Module.End.eigenspace A) ht
    rw [← hWt]
    rintro _ ⟨w, rfl⟩
    change s4_complexOneCup Y (2 * k)
      (exteriorPower.toTensorPower ℂ (ℂ ⊗[ℚ] HQ Y 1) (2 * k)
        (exteriorPower.map (2 * k) (s4_e2_curveSpace S Y a e t).subtype w)) ∈
        (⨆ t : cyc_Field S.m →ₐ[ℚ] ℂ,
          (LinearMap.range (exteriorPower.map (2 * k)
            (s4_e2_curveSpace S Y a e t).subtype)).map (s4_e2_alternatingCup Y (2 * k)))
    rw [← LinearMap.comp_apply, s4_complexOneCup_tensorAlternation, LinearMap.smul_apply]
    apply Submodule.smul_mem
    exact Submodule.mem_iSup_of_mem t ⟨_, ⟨w, rfl⟩, rfl⟩
  exact hle hcore

#print axioms primitive_invariant_embedding_sum
end HodgeLean.Foundations.Program.G32Native.TowerOrbit
