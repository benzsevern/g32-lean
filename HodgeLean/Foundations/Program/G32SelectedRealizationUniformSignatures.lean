import HodgeLean.Foundations.Program.G32SelectedRealizationPrimitiveLocalAges
import HodgeLean.Foundations.Program.G32SelectedRealizationFamilyAges
import HodgeLean.Foundations.Program.G32SelectedRealizationRealAges

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

theorem g32y_primitive_signatures_equal {c : Fin 10 → ℂ} {g : Fin 13 → b4b_Group}
    (D : b65z_SharedFamily c g) (t : b6t_polydisc c)
    (hg : g32h_Nielsen (fun j ↦ b4b_toMatrix (g j)))
    (f : g32p_G → AbelianEnd (g32x_J D t))
    (hf : ∀ a, homPullback (f a).hom 1 = g32x_deck D t a)
    (S : g32p_Supplier) (hS : g32p_Admissible (fun a ↦ (f a).hom) S) {d : ℕ}
    (e : g32p_primitive (fun a ↦ (f a).hom) S ≃ₗ[ℚ] (Fin d → cyc_Field S.m))
    (he : ∀ h : S.H, (g32p_primitive (fun a ↦ (f a).hom) S).subtype ∘ₗ
      cyc_scalar e (g32p_fieldValue S h) =
        homPullback (f h).hom 1 ∘ₗ (g32p_primitive (fun a ↦ (f a).hom) S).subtype)
    (σ τ : cyc_Field S.m →ₐ[ℚ] ℂ) :
    Module.finrank ℂ ↥(cyc_eigenspace e σ ⊓
      (cohomologyHodgePiece (g32x_J D t) 1 (1, 0)).comap
        ((g32p_primitive (fun a ↦ (f a).hom) S).subtype.baseChange ℂ)) =
    Module.finrank ℂ ↥(cyc_eigenspace e τ ⊓
      (cohomologyHodgePiece (g32x_J D t) 1 (1, 0)).comap
        ((g32p_primitive (fun a ↦ (f a).hom) S).subtype.baseChange ℂ)) := by
  classical
  letI : NeZero S.m := ⟨by have := S.three_le; omega⟩
  letI : Fintype S.H := Fintype.ofFinite S.H
  let r : b65z_fibre c D.C t → S.H := fun x ↦
    Classical.choose (b4_exists_rotGen (by simp : Module.finrank ℂ ℂ = 1)
      (fun h : S.H ↦ D.hG t h) x)
  have hr (x) : b4_IsRotGen ℂ x (r x) := Classical.choose_spec
    (b4_exists_rotGen (by simp : Module.finrank ℂ ℂ = 1) (fun h : S.H ↦ D.hG t h) x)
  have hlocal (u : (ZMod S.m)ˣ) :
      2 * (∑ᶠ x : b65z_fibre c D.C t,
        (Nat.card (MulAction.stabilizer S.H x) : ℝ) / Fintype.card S.H *
          (((u : ZMod S.m) * Multiplicative.toAdd (S.χ (r x))).val : ℝ) / S.m) =
          ((g32p_exponents S).length : ℝ) := by
    have hh := g32y_family_exponent_weights D t hg S
      (fun z ↦ (((u : ZMod S.m) * z).val : ℝ) / S.m) (by simp) r hr
    have hsum := g32y_supplier_real_residue_sum S.H S.χ g32p_classList hS.1 u
    have hc : (∑ᶠ x : b65z_fibre c D.C t,
        (Nat.card (MulAction.stabilizer S.H x) : ℝ) / Fintype.card S.H *
          (((u : ZMod S.m) * Multiplicative.toAdd (S.χ (r x))).val : ℝ) / S.m) =
        ∑ᶠ x : b65z_fibre c D.C t,
        (Nat.card (MulAction.stabilizer S.H x) : ℝ) / Nat.card S.H *
          ((((u : ZMod S.m) * Multiplicative.toAdd (S.χ (r x))).val : ℝ) / S.m) := by
      apply finsum_congr
      intro x
      simp only [Nat.card_eq_fintype_card]
      ring
    rw [hc, hh]
    exact hsum
  obtain ⟨u, hu⟩ := g32y_primitive_signature_local_ages D t f hf S e he r hr σ
  obtain ⟨v, hv⟩ := g32y_primitive_signature_local_ages D t f hf S e he r hr τ
  have hreal : (Module.finrank ℂ ↥(cyc_eigenspace e σ ⊓
      (cohomologyHodgePiece (g32x_J D t) 1 (1, 0)).comap
        ((g32p_primitive (fun a ↦ (f a).hom) S).subtype.baseChange ℂ)) : ℝ) =
    (Module.finrank ℂ ↥(cyc_eigenspace e τ ⊓
      (cohomologyHodgePiece (g32x_J D t) 1 (1, 0)).comap
        ((g32p_primitive (fun a ↦ (f a).hom) S).subtype.baseChange ℂ)) : ℝ) := by
    rw [hu, hv]
    have hu' := hlocal u
    have hv' := hlocal v
    linarith
  exact_mod_cast hreal

end HodgeLean.Foundations.Program
