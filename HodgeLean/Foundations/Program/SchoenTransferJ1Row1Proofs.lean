import HodgeLean.Foundations.WitnessSelection.StageTwo.Defs
import HodgeLean.Foundations.Program.SchoenTransferQ2cApplications
/-! # S4 selected witness applications

Implications from the literal retained S2 alternatives and realization choices.
HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxRecDepth 4000
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open HodgeLean.Adapters HodgeLean.RealDefs HodgeLean.Foundations HodgeLean.Papers
open scoped BigOperators Manifold ContDiff OnePoint TensorProduct
namespace HodgeLean.Foundations.Program
/-- Contract J1.1, on the specified native witnesses.
Source: Schoen (1988), Theorem 2.0 and Corollary 3.1; s4-chain-contract.md, J1 row 1.
Example: SchoenTransferJ1Checks.row1_construction.
HC no distance; AV milestone no distance. -/
theorem s4_chain_selected_quotient_fibre_orbits_aux (S : g32p_Supplier) (Y : Over (Spec ↧ℂ))
    [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]
    (a : (S.H ⧸ S.χ.ker) → (Y ⟶ Y))
    (e : (S.H ⧸ S.χ.ker) ≃* Multiplicative (ZMod S.m))
    (ha1 : a 1 = 𝟙 Y) (hamul : ∀ u v, a (u * v) = a v ≫ a u)
    (h : ℕ)
    [IsIntegral (g3_power Y h).left] [Smooth (g3_power Y h).hom]
    [IsProjective (g3_power Y h).hom]
    (W : Over (Spec ↧ℂ)) [IsIntegral W.left] [IsProjective W.hom]
    (q : g3_power Y h ⟶ W) [IsFinite q.left]
    (hqsurj : Function.Surjective (Point.map q))
    (hqinv : ∀ (v : Fin h → ZMod S.m) (σ : Equiv.Perm (Fin h)),
      ∑ i, v i = 0 → s2_action S Y a e h v σ ≫ q = q)
    (hquot : ∀ (Z : Over (Spec ↧ℂ)) (f : g3_power Y h ⟶ Z),
      (∀ (v : Fin h → ZMod S.m) (σ : Equiv.Perm (Fin h)),
        ∑ i, v i = 0 → s2_action S Y a e h v σ ≫ f = f) →
      ∃! g : W ⟶ Z, q ≫ g = f) :
    ∀ x y : ComplexPoint (g3_power Y h),
      Point.map q x = Point.map q y →
        ∃ (v : Fin h → ZMod S.m) (τ : Equiv.Perm (Fin h)),
          (∑ i, v i) = 0 ∧ Point.map (s2_action S Y a e h v τ) x = y := by
  intro x y hxy
  obtain ⟨g, hg⟩ := (Q2.q2c_orbit_fibres_application S Y a e ha1 hamul h W q
    hqsurj hqinv hquot x y).mp hxy
  exact ⟨g.vector, g.perm, g.zero_sum, hg⟩

end HodgeLean.Foundations.Program
