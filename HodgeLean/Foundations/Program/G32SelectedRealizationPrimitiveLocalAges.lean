import HodgeLean.Foundations.Program.G32SelectedRealizationPrimitiveHodgeMultiplicity
import HodgeLean.Foundations.Program.G32SelectedRealizationResidueAge

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

attribute [local instance] b65z_SharedFamily.fibreFaithful

theorem g32y_primitive_signature_local_ages {c : Fin 10 → ℂ} {g : Fin 13 → b4b_Group}
    (D : b65z_SharedFamily c g) (t : b6t_polydisc c)
    (f : g32p_G → AbelianEnd (g32x_J D t))
    (hf : ∀ a, homPullback (f a).hom 1 = g32x_deck D t a)
    (S : g32p_Supplier) {d : ℕ}
    (e : g32p_primitive (fun a ↦ (f a).hom) S ≃ₗ[ℚ] (Fin d → cyc_Field S.m))
    (he : ∀ h : S.H, (g32p_primitive (fun a ↦ (f a).hom) S).subtype ∘ₗ
      cyc_scalar e (g32p_fieldValue S h) =
        homPullback (f h).hom 1 ∘ₗ (g32p_primitive (fun a ↦ (f a).hom) S).subtype)
    (h : b65z_fibre c D.C t → S.H) (hh : ∀ x, b4_IsRotGen ℂ x (h x))
    (σ : cyc_Field S.m →ₐ[ℚ] ℂ) :
    letI : Fintype S.H := Fintype.ofFinite S.H
    ∃ u : (ZMod S.m)ˣ,
      (Module.finrank ℂ ↥(cyc_eigenspace e σ ⊓
        (cohomologyHodgePiece (g32x_J D t) 1 (1, 0)).comap
          ((g32p_primitive (fun a ↦ (f a).hom) S).subtype.baseChange ℂ)) : ℝ) =
        (Module.finrank ℂ (Representation.invariants
          (b4_formRepresentation (fun h : S.H ↦ D.hG t h))) : ℝ) - 1 +
          ∑ᶠ x : b65z_fibre c D.C t,
            (Nat.card (MulAction.stabilizer S.H x) : ℝ) / Fintype.card S.H *
              (((u : ZMod S.m) * Multiplicative.toAdd (S.χ (h x))).val : ℝ) / S.m := by
  classical
  letI : Fintype S.H := Fintype.ofFinite S.H
  obtain ⟨χ, hχ, hn, hd⟩ := g32y_primitive_hodge_character_dimension D t f hf S e he σ
  obtain ⟨u, hu⟩ := g32y_fieldValue_residue_angle S σ
  refine ⟨u, ?_⟩
  rw [hd, g32y_linear_character_multiplicity]
  have hc := g32y_character_holomorphic_dimension (by simp : Module.finrank ℂ ℂ = 1)
    (fun h : S.H ↦ D.hG t h) h hh χ hn
  apply hc.trans
  apply congrArg (fun z : ℝ ↦
    (Module.finrank ℂ (Representation.invariants
      (b4_formRepresentation (fun h : S.H ↦ D.hG t h))) : ℝ) - 1 + z)
  apply finsum_congr
  intro x
  rw [hχ, hu]
  ring

end HodgeLean.Foundations.Program
