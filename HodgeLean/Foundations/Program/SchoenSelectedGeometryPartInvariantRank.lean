import HodgeLean.Foundations.Program.SchoenSelectedGeometryPartExponentSignature
import HodgeLean.Foundations.Program.SchoenSelectedGeometryConjugateAngles
import HodgeLean.Papers.PapersSupplyProofs

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

/-- The primitive field rank is determined by invariant forms and the supplier exponent count. -/
theorem s0_part_invariant_rank
    {c : Fin 10 → ℂ} {g : Fin 13 → b4b_Group}
    (D : b65z_SharedFamily c g) (t : b6t_polydisc c)
    (hg : g32h_Nielsen (fun j ↦ b4b_toMatrix (g j)))
    (f : g32p_G → AbelianEnd (g32x_J D t))
    (hf : ∀ a, homPullback (f a).hom 1 = g32x_deck D t a)
    (S : g32p_Supplier) (P : g32p_Part (g32x_J D t) (fun a ↦ (f a).hom) S) :
    2 * P.k + 2 =
      2 * Module.finrank ℂ (Representation.invariants
        (b4_formRepresentation (fun h : S.H ↦ D.hG t h))) + (g32p_exponents S).length := by
  have hs := s0_part_exponent_signature D t hg f hf S P (g32p_complexEmbedding S)
  have ht := s0_part_exponent_signature D t hg f hf S P (cmConjEmbedding (g32p_complexEmbedding S))
  have hbar : cmConjEmbedding (g32p_complexEmbedding S) (g32p_zeta S) = star (g32p_root S.m) := by
    change star (g32p_complexEmbedding S (g32p_zeta S)) = _
    rw [g32p_complexEmbedding_zeta]
  rw [g32p_complexEmbedding_zeta] at hs
  rw [hbar] at ht
  simp only [← star_pow] at ht
  let w := fun a : ℕ ↦ g32h_angle (g32p_root S.m ^ (a : ZMod S.m).val)
  let w' := fun a : ℕ ↦ g32h_angle (star (g32p_root S.m ^ (a : ZMod S.m).val))
  have hnz (a : ℕ) (ha : a ∈ g32p_exponents S) : (a : ZMod S.m) ≠ 0 := by
    change a ∈ papersExpsList S.H S.χ g32p_classList at ha
    rw [papersExpsList, Multiset.mem_toList, Multiset.mem_map] at ha
    obtain ⟨b, hb, rfl⟩ := ha
    simpa only [ZMod.natCast_zmod_val] using papersExpsTuple_ne_zero S.H S.χ g32p_classList b hb
  have hsum (l : List ℕ) (hl : ∀ a ∈ l, (a : ZMod S.m) ≠ 0) :
      (l.map w).sum + (l.map w').sum = (l.length : ℝ) := by
    induction l with
    | nil => simp
    | cons a l ih =>
      have ha := s0_residue_conjugate_angle_sum S (a : ZMod S.m) (hl a (by simp))
      have hh := ih (fun b hb ↦ hl b (by simp [hb]))
      simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.cast_add, Nat.cast_one]
      change w a + (l.map w).sum + (w' a + (l.map w').sum) = (l.length : ℝ) + 1
      change w a + w' a = 1 at ha
      linarith
  have htotal := hsum (g32p_exponents S) hnz
  have hreal : ((2 * P.k + 2 : ℕ) : ℝ) =
      ((2 * Module.finrank ℂ (Representation.invariants
        (b4_formRepresentation (fun h : S.H ↦ D.hG t h))) + (g32p_exponents S).length : ℕ) : ℝ) := by
    push_cast
    dsimp only [w, w'] at htotal
    linarith
  exact_mod_cast hreal

#print axioms s0_part_invariant_rank
end HodgeLean.Foundations.Program
