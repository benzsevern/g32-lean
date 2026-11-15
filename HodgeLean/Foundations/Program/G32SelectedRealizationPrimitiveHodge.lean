import HodgeLean.Foundations.Program.G32SelectedRealization
import HodgeLean.Foundations.Program.G32SelectedRealizationPrimitiveCoordinates
import HodgeLean.Foundations.Program.G32SelectedRealizationAges

noncomputable section
set_option maxRecDepth 2000
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open HodgeLean.RealDefs HodgeLean.Adapters HodgeLean.Papers HodgeLean.Foundations
open scoped TensorProduct CategoryTheory.MonObj
namespace HodgeLean.Foundations.Program
attribute [local instance] b65z_SharedFamily.topC b65z_SharedFamily.chartC
  b65z_SharedFamily.manC b65z_SharedFamily.t2C b65z_SharedFamily.compactC
  b65z_SharedFamily.connectedC b65z_SharedFamily.actionC b65z_SharedFamily.fibreChart
  b65z_SharedFamily.fibreMan b65z_SharedFamily.fibreT2 b65z_SharedFamily.fibreCompact
  b65z_SharedFamily.fibreConnected

theorem g32y_primitive_coordinates {c : Fin 10 → ℂ} {g : Fin 13 → b4b_Group}
    (D : b65z_SharedFamily c g) (t : b6t_polydisc c)
    (f : g32p_G → AbelianEnd (g32x_J D t))
    (hf : ∀ a, homPullback (f a).hom 1 = g32x_deck D t a)
    (S : g32p_Supplier) :
    let V := g32p_primitive (fun a ↦ (f a).hom) S
    ∃ d : ℕ, ∃ e : V ≃ₗ[ℚ] (Fin d → cyc_Field S.m),
      ∀ h : S.H, V.subtype ∘ₗ cyc_scalar e (g32p_fieldValue S h) =
        homPullback (f h).hom 1 ∘ₗ V.subtype := by
  obtain ⟨h1, hmul⟩ := g32x_deck_laws D t f hf
  let := (torusCohomology_cupProductOf (g32x_J D t)).finite
  let R : Representation ℚ S.H (HQ (g32x_J D t) 1) := {
    toFun := fun h ↦ homPullback (f h).hom 1
    map_one' := by
      change homPullback (f 1).hom 1 = 1
      rw [h1, spec_homPullback_id]
      rfl
    map_mul' := by
      intro a b
      change homPullback (f ((a : g32p_G) * (b : g32p_G))).hom 1 = _
      rw [hmul, spec_homPullback_comp]
      rfl }
  exact g32y_relation_cyclotomic_coordinates R S.χ S.surjective

end HodgeLean.Foundations.Program
