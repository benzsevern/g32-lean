import HodgeLean.Foundations.Program.G32SelectedRealizationCharacterHodge
import HodgeLean.Foundations.Program.G32SelectedRealizationPrimitiveEigenspace
import HodgeLean.Foundations.Program.G32SelectedRealizationSupplierCharacter
import HodgeLean.Foundations.Program.G32SelectedRealizationIntersectionRank

noncomputable section
set_option maxRecDepth 2000
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint TopologicalSpace
open HodgeLean.RealDefs HodgeLean.Adapters HodgeLean.Papers HodgeLean.Foundations
open scoped TensorProduct CategoryTheory.MonObj Manifold ContDiff
namespace HodgeLean.Foundations.Program
attribute [local instance] b65z_SharedFamily.topC b65z_SharedFamily.chartC
  b65z_SharedFamily.manC b65z_SharedFamily.t2C b65z_SharedFamily.compactC
  b65z_SharedFamily.connectedC b65z_SharedFamily.actionC b65z_SharedFamily.fibreChart
  b65z_SharedFamily.fibreMan b65z_SharedFamily.fibreT2 b65z_SharedFamily.fibreCompact
  b65z_SharedFamily.fibreConnected b65z_SharedFamily.totalChart b65z_SharedFamily.totalMan

theorem g32y_primitive_hodge_character_dimension {c : Fin 10 → ℂ} {g : Fin 13 → b4b_Group}
    (D : b65z_SharedFamily c g) (t : b6t_polydisc c)
    (f : g32p_G → AbelianEnd (g32x_J D t))
    (hf : ∀ a, homPullback (f a).hom 1 = g32x_deck D t a)
    (S : g32p_Supplier) {d : ℕ}
    (e : g32p_primitive (fun a ↦ (f a).hom) S ≃ₗ[ℚ] (Fin d → cyc_Field S.m))
    (he : ∀ h : S.H, (g32p_primitive (fun a ↦ (f a).hom) S).subtype ∘ₗ
      cyc_scalar e (g32p_fieldValue S h) =
        homPullback (f h).hom 1 ∘ₗ (g32p_primitive (fun a ↦ (f a).hom) S).subtype)
    (σ : cyc_Field S.m →ₐ[ℚ] ℂ) :
    ∃ χ : S.H →* ℂˣ, (∀ h, (χ h : ℂ) = σ (g32p_fieldValue S h)) ∧
      (∃ h, χ h ≠ 1) ∧
      Module.finrank ℂ ↥(cyc_eigenspace e σ ⊓
        (cohomologyHodgePiece (g32x_J D t) 1 (1, 0)).comap
          ((g32p_primitive (fun a ↦ (f a).hom) S).subtype.baseChange ℂ)) =
        Module.finrank ℂ (b4_HomG (papersLinRep χ).ρ
          (fun h : S.H ↦ b4_formAct ℂ (C := b65z_fibre c D.C t) h)
          (b3_HolForm ℂ (b65z_fibre c D.C t))) := by
  obtain ⟨χ, hχ, hχn⟩ := g32y_supplier_complex_character S σ
  refine ⟨χ, hχ, hχn, ?_⟩
  let V := g32p_primitive (fun a ↦ (f a).hom) S
  let T := fun h : S.H ↦ homPullback (f h).hom 1
  have hEig := g32y_primitive_character_eigenspace S T V rfl e he σ
  have hinj : Function.Injective (V.subtype.baseChange ℂ) :=
    Module.Flat.lTensor_preserves_injective_linearMap V.subtype Subtype.val_injective
  have hd := g32y_intersection_finrank_image (V.subtype.baseChange ℂ) hinj
    (cyc_eigenspace e σ) (cohomologyHodgePiece (g32x_J D t) 1 (1, 0))
  rw [hEig] at hd
  have hh := g32y_jacobian_character_hodge_dimension D t f hf S χ
  have hχEig : (⨅ h : S.H, Module.End.eigenspace
      ((homPullback (f h).hom 1).baseChange ℂ) (χ h : ℂ)) =
        ⨅ h : S.H, Module.End.eigenspace
          ((homPullback (f h).hom 1).baseChange ℂ) (σ (g32p_fieldValue S h)) := by
    apply iInf_congr
    intro h
    rw [hχ h]
  rw [hχEig] at hh
  exact hd.trans hh

end HodgeLean.Foundations.Program
