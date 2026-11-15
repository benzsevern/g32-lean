import HodgeLean.Foundations.Program.G32SelectedRealizationPrimitiveHodge
import HodgeLean.Foundations.Program.G32SelectedRealizationPreserves

noncomputable section
set_option maxRecDepth 2000
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open HodgeLean.RealDefs HodgeLean.Adapters HodgeLean.Papers HodgeLean.Foundations
open scoped TensorProduct CategoryTheory.MonObj
namespace HodgeLean.Foundations.Program

theorem g32y_supplier_action_preserves (J : Over (Spec ↧ℂ))
    [GrpObj J] [IsCommMonObj J] [IsIntegral J.left] [Smooth J.hom] [IsProjective J.hom]
    (f : g32p_G → AbelianEnd J) (S : g32p_Supplier) {d : ℕ}
    (e : g32p_primitive (fun a ↦ (f a).hom) S ≃ₗ[ℚ] (Fin d → cyc_Field S.m))
    (he : ∀ h : S.H,
      (g32p_primitive (fun a ↦ (f a).hom) S).subtype ∘ₗ cyc_scalar e (g32p_fieldValue S h) =
        homPullback (f h).hom 1 ∘ₗ (g32p_primitive (fun a ↦ (f a).hom) S).subtype) :
    ∀ a pq, ((cohomologyHodgePiece J 1 pq).comap
      ((g32p_primitive (fun a ↦ (f a).hom) S).subtype.baseChange ℂ)).map
        ((cyc_scalar e a).baseChange ℂ) ≤
      (cohomologyHodgePiece J 1 pq).comap
        ((g32p_primitive (fun a ↦ (f a).hom) S).subtype.baseChange ℂ) := by
  intro a pq
  let V := g32p_primitive (fun a ↦ (f a).hom) S
  let W := (cohomologyHodgePiece J 1 pq).comap (V.subtype.baseChange ℂ)
  have hg : ∀ v ∈ W,
      (cyc_scalar e (IsCyclotomicExtension.zeta S.m ℚ (cyc_Field S.m))).baseChange ℂ v ∈ W := by
    obtain ⟨h, hh⟩ := S.surjective (Multiplicative.ofAdd 1)
    have hz : g32p_fieldValue S h = IsCyclotomicExtension.zeta S.m ℚ (cyc_Field S.m) := by
      rw [g32p_fieldValue, hh, toAdd_ofAdd,
        ZMod.val_one'' (by have := S.three_le; omega), pow_one]
      rfl
    have hc : V.subtype.baseChange ℂ ∘ₗ
        (cyc_scalar e (IsCyclotomicExtension.zeta S.m ℚ (cyc_Field S.m))).baseChange ℂ =
          (homPullback (f h).hom 1).baseChange ℂ ∘ₗ V.subtype.baseChange ℂ := by
      simpa only [LinearMap.baseChange_comp, hz] using
        congrArg (LinearMap.baseChange ℂ) (he h)
    intro v hv
    change V.subtype.baseChange ℂ
      ((cyc_scalar e (IsCyclotomicExtension.zeta S.m ℚ (cyc_Field S.m))).baseChange ℂ v) ∈
        cohomologyHodgePiece J 1 pq
    have hc' := LinearMap.congr_fun hc v
    simp only [LinearMap.comp_apply] at hc'
    rw [hc']
    exact spec_homPullback_hodgePiece_one (f h).hom pq (Submodule.mem_map_of_mem hv)
  rintro _ ⟨v, hv, rfl⟩
  exact g32y_cyclotomic_preserves e W hg a v hv

theorem g32y_primitive_hodge_coordinates {c : Fin 10 → ℂ} {g : Fin 13 → b4b_Group}
    (D : b65z_SharedFamily c g) (t : b6t_polydisc c)
    (f : g32p_G → AbelianEnd (g32x_J D t))
    (hf : ∀ a, homPullback (f a).hom 1 = g32x_deck D t a)
    (S : g32p_Supplier) :
    let V := g32p_primitive (fun a ↦ (f a).hom) S
    let M := (abelianVarietyCohomologyOf (finiteBetti_abelian (g32x_J D t))
      (spec_bettiDeRhamIso_abelian (g32x_J D t))
      (hodgeDecomposition_of_abelian (g32x_J D t))
      (torusCohomology_cupProductOf (g32x_J D t))).weight1
    ∃ d : ℕ, ∃ e : V ≃ₗ[ℚ] (Fin d → cyc_Field S.m),
      (∀ h : S.H, V.subtype ∘ₗ cyc_scalar e (g32p_fieldValue S h) =
        homPullback (f h).hom 1 ∘ₗ V.subtype) ∧
      ∀ a pq, ((M.H pq).comap (V.subtype.baseChange ℂ)).map
        ((cyc_scalar e a).baseChange ℂ) ≤ (M.H pq).comap (V.subtype.baseChange ℂ) := by
  obtain ⟨d, e, he⟩ := g32y_primitive_coordinates D t f hf S
  exact ⟨d, e, he, g32y_supplier_action_preserves (g32x_J D t) f S e he⟩

end HodgeLean.Foundations.Program
