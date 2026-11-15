import HodgeLean.Foundations.Program.SchoenTransferE2ChainDefs
import HodgeLean.Foundations.Program.SchoenTransferCharacterSuppliers

/-! # Character transport for the specified linear primitive comparison -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
set_option maxRecDepth 2048
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open scoped TensorProduct BigOperators
open HodgeLean.RealDefs HodgeLean.Adapters HodgeLean.Foundations
open HodgeLean.Foundations.Program
namespace HodgeLean.Foundations.Program.G32Native.TowerOrbit

/-- The supplied linear primitive comparison transports every cyclotomic character space. -/
theorem primitive_character_map
    (S : g32p_Supplier) (Y : Over (Spec ↧ℂ))
    [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]
    (a : (S.H ⧸ S.χ.ker) → (Y ⟶ Y))
    (e : (S.H ⧸ S.χ.ker) ≃* Multiplicative (ZMod S.m))
    {V : Type*} [AddCommGroup V] [Module ℚ V] (d : ℕ)
    (b : V ≃ₗ[ℚ] (Fin d → cyc_Field S.m))
    (F : V →ₗ[ℚ] HQ Y 1) (hf : Function.Injective F)
    (himage : LinearMap.range F = LinearMap.ker
      (Polynomial.aeval (homPullback (a (e.symm (Multiplicative.ofAdd 1))) 1)
        (Polynomial.cyclotomic S.m ℚ)))
    (hscalar : ∀ (u : S.H) v,
      homPullback (a ((QuotientGroup.mk u)⁻¹)) 1 (F v) =
        F (cyc_scalar b (g32p_fieldValue S u) v)) :
    ∀ t : cyc_Field S.m →ₐ[ℚ] ℂ,
      (cyc_eigenspace b t).map (F.baseChange ℂ) =
        s4_e2_curveSpace S Y a e t := by
  intro t
  have hinj : Function.Injective (F.baseChange ℂ) :=
    Module.Flat.lTensor_preserves_injective_linearMap F hf
  have hr : LinearMap.range (F.baseChange ℂ) = (LinearMap.range F).baseChange ℂ := by
    let E := LinearEquiv.ofInjective F hf
    have hF : F = (LinearMap.range F).subtype ∘ₗ E.toLinearMap := rfl
    rw [hF, LinearMap.baseChange_comp, LinearMap.range_comp_of_range_eq_top]
    · rfl
    · exact LinearMap.range_eq_top.mpr (E.baseChange ℚ ℂ _ _).surjective
  rw [himage] at hr
  have hc (u : S.H) :
      (homPullback (a ((QuotientGroup.mk u)⁻¹)) 1).baseChange ℂ ∘ₗ F.baseChange ℂ =
        F.baseChange ℂ ∘ₗ (cyc_scalar b (g32p_fieldValue S u)).baseChange ℂ := by
    have h : homPullback (a ((QuotientGroup.mk u)⁻¹)) 1 ∘ₗ F =
        F ∘ₗ cyc_scalar b (g32p_fieldValue S u) :=
      LinearMap.ext (hscalar u)
    simpa only [LinearMap.baseChange_comp] using congrArg (LinearMap.baseChange ℂ) h
  apply le_antisymm
  · rintro _ ⟨v, hv, rfl⟩
    refine ⟨hr ▸ ⟨v, rfl⟩, ?_⟩
    apply (Submodule.mem_iInf _).mpr
    intro u
    apply Module.End.mem_eigenspace_iff.mpr
    have hs := Module.End.mem_eigenspace_iff.mp
      ((Submodule.mem_iInf _).mp hv (g32p_fieldValue S u))
    exact (LinearMap.congr_fun (hc u) v).trans (by
      change F.baseChange ℂ ((cyc_scalar b (g32p_fieldValue S u)).baseChange ℂ v) = _
      rw [hs, map_smul])
  · rintro v ⟨hv, heig⟩
    obtain ⟨w, rfl⟩ := hr.symm ▸ hv
    refine ⟨w, ?_, rfl⟩
    rw [g32y_cyclotomic_eigenspace_generator]
    apply Module.End.mem_eigenspace_iff.mpr
    apply hinj
    rw [map_smul]
    obtain ⟨u, hu⟩ := S.surjective (Multiplicative.ofAdd 1)
    have hfu : g32p_fieldValue S u = IsCyclotomicExtension.zeta S.m ℚ (cyc_Field S.m) := by
      simp only [g32p_fieldValue, hu, toAdd_ofAdd,
        ZMod.val_one'' (n := S.m) (by have := S.three_le; omega), pow_one]
      rfl
    rw [← hfu]
    exact (LinearMap.congr_fun (hc u) w).symm.trans
      (Module.End.mem_eigenspace_iff.mp ((Submodule.mem_iInf _).mp heig u))

#print axioms primitive_character_map
/-- The intrinsic character dimension equals the supplied cyclotomic coordinate rank. -/
theorem primitive_character_finrank
    (S : g32p_Supplier) (Y : Over (Spec ↧ℂ))
    [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]
    (a : (S.H ⧸ S.χ.ker) → (Y ⟶ Y))
    (e : (S.H ⧸ S.χ.ker) ≃* Multiplicative (ZMod S.m))
    {V : Type*} [AddCommGroup V] [Module ℚ V] (d : ℕ)
    (b : V ≃ₗ[ℚ] (Fin d → cyc_Field S.m))
    (F : V →ₗ[ℚ] HQ Y 1) (hf : Function.Injective F)
    (himage : LinearMap.range F = LinearMap.ker
      (Polynomial.aeval (homPullback (a (e.symm (Multiplicative.ofAdd 1))) 1)
        (Polynomial.cyclotomic S.m ℚ)))
    (hscalar : ∀ (u : S.H) v,
      homPullback (a ((QuotientGroup.mk u)⁻¹)) 1 (F v) =
        F (cyc_scalar b (g32p_fieldValue S u) v))
    [Module.Finite ℚ V] (t : cyc_Field S.m →ₐ[ℚ] ℂ) :
    Module.finrank ℂ (s4_e2_curveSpace S Y a e t) = d := by
  rw [← primitive_character_map S Y a e d b F hf himage hscalar t]
  have hi : Function.Injective (F.baseChange ℂ) :=
    Module.Flat.lTensor_preserves_injective_linearMap F hf
  rw [← (Submodule.equivMapOfInjective (F.baseChange ℂ) hi (cyc_eigenspace b t)).finrank_eq]
  exact cyc_finrank_eigenspace b t

#print axioms primitive_character_finrank
end HodgeLean.Foundations.Program.G32Native.TowerOrbit
