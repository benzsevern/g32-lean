import HodgeLean.Foundations.Program.SchoenSelectedGeometryPartHodge
import HodgeLean.Foundations.Program.G32SelectedRealizationPrimitiveLocalAges

noncomputable section
set_option maxRecDepth 2000
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open HodgeLean.RealDefs HodgeLean.Adapters HodgeLean.Papers HodgeLean.Foundations
open HodgeLean.Foundations.Symplectic
open scoped Manifold ContDiff TensorProduct CategoryTheory.MonObj
namespace HodgeLean.Foundations.Program
attribute [local instance] b65z_SharedFamily.topC b65z_SharedFamily.chartC
  b65z_SharedFamily.manC b65z_SharedFamily.t2C b65z_SharedFamily.compactC
  b65z_SharedFamily.connectedC b65z_SharedFamily.actionC b65z_SharedFamily.fibreChart
  b65z_SharedFamily.fibreMan b65z_SharedFamily.fibreT2 b65z_SharedFamily.fibreCompact
  b65z_SharedFamily.fibreConnected b65z_SharedFamily.fibreFaithful b65z_SharedFamily.totalChart b65z_SharedFamily.totalMan

/-- Each embedding expresses the part signature by invariant forms and local rotation angles. -/
theorem s0_part_rotation_signature
    {c : Fin 10 → ℂ} {g : Fin 13 → b4b_Group}
    (D : b65z_SharedFamily c g) (t : b6t_polydisc c)
    (f : g32p_G → AbelianEnd (g32x_J D t))
    (hf : ∀ a, homPullback (f a).hom 1 = g32x_deck D t a)
    (S : g32p_Supplier) (P : g32p_Part (g32x_J D t) (fun a ↦ (f a).hom) S)
    (r : b65z_fibre c D.C t → S.H) (hr : ∀ x, b4_IsRotGen ℂ x (r x))
    (σ : cyc_Field S.m →ₐ[ℚ] ℂ) :
    (P.k : ℝ) =
      (Module.finrank ℂ (Representation.invariants
        (b4_formRepresentation (fun h : S.H ↦ D.hG t h))) : ℝ) - 1 +
        ∑ᶠ x : b65z_fibre c D.C t,
          (Nat.card (MulAction.stabilizer S.H x) : ℝ) / Nat.card S.H *
            g32h_angle (σ (g32p_fieldValue S (r x))) := by
  classical
  letI : Fintype S.H := Fintype.ofFinite S.H
  obtain ⟨e, he, hs⟩ := s0_part_primitive_hodge_coordinates (g32x_J D t)
    (fun a ↦ (f a).hom) S P
  obtain ⟨χ, hχ, hn, hd⟩ := g32y_primitive_hodge_character_dimension D t f hf S e he σ
  have hdim := hs σ
  rw [hd, g32y_linear_character_multiplicity] at hdim
  have h := g32y_character_holomorphic_dimension (Module.finrank_self ℂ)
    (fun h : S.H ↦ D.hG t h) r hr χ hn
  rw [hdim] at h
  simpa only [hχ, Nat.card_eq_fintype_card] using h

#print axioms s0_part_rotation_signature
end HodgeLean.Foundations.Program
