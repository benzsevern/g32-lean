import HodgeLean.Foundations.Program.SchoenTransferR2PairingAction
import HodgeLean.Foundations.Program.SchoenTransferQ2cApplications
import HodgeLean.Foundations.Program.SchoenCycleC1MixedActionIso
import HodgeLean.Foundations.Program.SchoenCycleC2PowerDimensionHelpers

/-! # Invariant pairing on the actual finite quotient

HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry AlgebraicTopology.Singular
open HodgeLean.Adapters HodgeLean.Foundations
namespace HodgeLean.Foundations.Program

/-- The specified mixed action has identity top action on its finite quotient.
Source: Schoen (1988), §1, finite quotient; Hatcher, Algebraic Topology, Theorem 3.26.
HC no distance; AV milestone no distance. -/
theorem s4_assembly_curve_quotient_top_action
    (S : g32p_Supplier) (Y : Over (Spec ↧ℂ))
    [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]
    (hdimY : TopologicalSpace.dim Y.left = 1)
    (a : (S.H ⧸ S.χ.ker) → (Y ⟶ Y))
    (e : (S.H ⧸ S.χ.ker) ≃* Multiplicative (ZMod S.m))
    (ha1 : a 1 = 𝟙 Y) (hamul : ∀ u v, a (u * v) = a v ≫ a u)
    (N : ℕ) (W : Over (Spec ↧ℂ)) [IsIntegral W.left] [IsProjective W.hom]
    (q : g3_power Y N ⟶ W) [IsFinite q.left]
    (hqsurj : Function.Surjective (Point.map q))
    (hqinv : ∀ (v : Fin N → ZMod S.m) (s : Equiv.Perm (Fin N)),
      ∑ i, v i = 0 → s2_action S Y a e N v s ≫ q = q)
    (hquot : ∀ (Z : Over (Spec ↧ℂ)) (f : g3_power Y N ⟶ Z),
      (∀ (v : Fin N → ZMod S.m) (s : Equiv.Perm (Fin N)),
        ∑ i, v i = 0 → s2_action S Y a e N v s ≫ f = f) →
      ∃! g : W ⟶ Z, q ≫ g = f)
    (v : Fin N → ZMod S.m) (s : Equiv.Perm (Fin N))
    (d : W ⟶ W) (hd : s2_action S Y a e N v s ≫ q = q ≫ d) :
    s2e_pullback ℚ d (2 * N) = LinearMap.id := by
  letI : GeometricallyIntegral Y.hom := spec_g3b_geometricallyIntegral Y
  letI : IsIntegral (g3_power Y N).left := spec_g3b_isIntegral_power Y N
  letI : SmoothOfRelativeDimension 1 Y.hom := by
    simpa only [hdimY] using
      (inferInstance : SmoothOfRelativeDimension (TopologicalSpace.dim Y.left) Y.hom)
  letI : SmoothOfRelativeDimension N (g3_power Y N).hom := by
    simpa only [Nat.mul_one] using spec_g3_smoothOfRelativeDimension_power Y 1 N
  letI := s2e_c1_mixed_action_isIso S Y a e ha1 hamul N v s
  apply s4_assembly_quotient_top_action (g3_power Y N) W N q
    (asIso (s2_action S Y a e N v s)) d hd
  exact (Q2.q2c_invariant_range_application S Y a e ha1 hamul N W q hqsurj hqinv hquot
    (2 * N)).1

#print axioms s4_assembly_curve_quotient_top_action
end HodgeLean.Foundations.Program
