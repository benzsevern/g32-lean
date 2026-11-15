import HodgeLean.Foundations.Program.SchoenSelectedGeometryPartAngles
import HodgeLean.Foundations.Program.G32SelectedRealizationFamilyAges

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

/-- The part signature is expressed by the literal supplier exponent list. -/
theorem s0_part_exponent_signature
    {c : Fin 10 → ℂ} {g : Fin 13 → b4b_Group}
    (D : b65z_SharedFamily c g) (t : b6t_polydisc c)
    (hg : g32h_Nielsen (fun j ↦ b4b_toMatrix (g j)))
    (f : g32p_G → AbelianEnd (g32x_J D t))
    (hf : ∀ a, homPullback (f a).hom 1 = g32x_deck D t a)
    (S : g32p_Supplier) (P : g32p_Part (g32x_J D t) (fun a ↦ (f a).hom) S)
    (σ : cyc_Field S.m →ₐ[ℚ] ℂ) :
    (P.k : ℝ) =
      (Module.finrank ℂ (Representation.invariants
        (b4_formRepresentation (fun h : S.H ↦ D.hG t h))) : ℝ) - 1 +
        ((g32p_exponents S).map fun a : ℕ ↦
          g32h_angle (σ (g32p_zeta S) ^ (a : ZMod S.m).val)).sum := by
  classical
  choose r hr using (fun x : b65z_fibre c D.C t ↦
    b4_exists_rotGen (Module.finrank_self ℂ) (fun h : S.H ↦ D.hG t h) x)
  have hs := s0_part_rotation_signature D t f hf S P r hr σ
  have hw : g32h_angle (σ (g32p_zeta S) ^ (0 : ZMod S.m).val) = 0 := by
    simp [g32h_angle]
  have he := g32y_family_exponent_weights D t hg S
    (fun a ↦ g32h_angle (σ (g32p_zeta S) ^ a.val)) hw r hr
  simp only [g32p_fieldValue, map_pow] at hs
  rw [he] at hs
  exact hs

#print axioms s0_part_exponent_signature
end HodgeLean.Foundations.Program
