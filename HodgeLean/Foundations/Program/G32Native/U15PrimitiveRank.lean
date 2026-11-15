import HodgeLean.Foundations.Program.G32Native.U15PrimitiveExhaustion
import HodgeLean.Foundations.Program.SchoenTransferExteriorImages
import HodgeLean.Foundations.Program.CyclotomicWeilLinear

/-! # The middle-degree primitive rank on the retained curve power -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
set_option maxRecDepth 2048
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open scoped TensorProduct BigOperators
open HodgeLean.RealDefs HodgeLean.Adapters HodgeLean.Foundations
open HodgeLean.Foundations.Program
namespace HodgeLean.Foundations.Program.G32Native
attribute [local irreducible] cupProductOf homPullback

/-- The primitive invariant middle-degree space has rank at most the cyclotomic degree. -/
theorem primitive_invariant_rank_bound
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
    Module.finrank ℚ (s4_invariantPrimitive S Y a e (2 * k)
      (Nat.mul_pos (by norm_num) hk)) ≤ Nat.totient S.m := by
  letI : Module.Finite ℚ V := Module.Finite.equiv coords.symm
  let U := s4_invariantPrimitive S Y a e (2 * k) (Nat.mul_pos (by norm_num) hk)
  let E := exteriorPower.map (2 * k) (F.baseChange ℂ)
  let L := (s4_e2_alternatingCup Y (2 * k)).comp E
  have hline (t : cyc_Field S.m →ₐ[ℚ] ℂ) :
      (cyc_line coords t).map E = LinearMap.range
        (exteriorPower.map (2 * k) (s4_e2_curveSpace S Y a e t).subtype) := by
    rw [cyc_line, exterior_image_submodule,
      primitive_character_map S Y a e (2 * k) coords F hf himage hscalar t]
  have hle : U.baseChange ℂ ≤ (cyc_topLines coords).map L := by
    have h := primitive_invariant_embedding_sum S Y hdim k hk a e he ha1 hamul
      coords F hf himage hscalar
    dsimp only [L]
    rw [Submodule.map_comp]
    rw [cyc_topLines, Submodule.map_iSup, Submodule.map_iSup]
    simpa only [hline] using h
  have hdimU : Module.finrank ℂ (U.baseChange ℂ) = Module.finrank ℚ U := by
    have hi : Function.Injective (U.subtype.baseChange ℂ) :=
      Module.Flat.lTensor_preserves_injective_linearMap U.subtype U.subtype_injective
    rw [Submodule.baseChange, LinearMap.finrank_range_of_inj hi, Module.finrank_baseChange]
  calc
    Module.finrank ℚ U = Module.finrank ℂ (U.baseChange ℂ) := hdimU.symm
    _ ≤ Module.finrank ℂ ((cyc_topLines coords).map L) := Submodule.finrank_mono hle
    _ ≤ Module.finrank ℂ (cyc_topLines coords) := Submodule.finrank_map_le L _
    _ = Nat.totient S.m := (cyc_finrank_topLines (Nat.mul_pos (by norm_num) hk) coords).trans cyc_finrank_field

#print axioms primitive_invariant_rank_bound
end HodgeLean.Foundations.Program.G32Native
