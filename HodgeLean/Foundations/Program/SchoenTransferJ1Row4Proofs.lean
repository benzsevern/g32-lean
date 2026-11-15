import HodgeLean.Foundations.WitnessSelection.StageTwo.Defs
import HodgeLean.Foundations.Program.SchoenTransferQ2cApplications
import HodgeLean.Foundations.Program.SchoenTransferQ3c
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
/-- Contract J1.4, on the specified native witnesses.
Source: Schoen (1988), Theorem 2.0 and Corollary 3.1; s4-chain-contract.md, J1 row 4.
Example: SchoenTransferJ1Checks.row4_construction.
HC no distance; AV milestone no distance. -/
theorem s4_chain_selected_curve_invariant_cycles_aux (S : g32p_Supplier)
    (Y : Over (Spec ↧ℂ)) [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]
    (hdim : TopologicalSpace.dim Y.left = 1) (k : ℕ) (hk : 0 < k)
    [IsIntegral (g3_power Y (2 * k)).left]
    [Smooth (g3_power Y (2 * k)).hom] [IsProjective (g3_power Y (2 * k)).hom]
    (a : (S.H ⧸ S.χ.ker) → (Y ⟶ Y))
    (e : (S.H ⧸ S.χ.ker) ≃* Multiplicative (ZMod S.m))
    (ha1 : a 1 = 𝟙 Y) (hamul : ∀ u v, a (u * v) = a u ≫ a v)
    (W : Over (Spec ↧ℂ)) [IsIntegral W.left] [IsProjective W.hom]
    (q : g3_power Y (2 * k) ⟶ W) [IsFinite q.left]
    (hqsurj : Function.Surjective (Point.map q))
    (hqinv : ∀ (v : Fin (2 * k) → ZMod S.m) (σ : Equiv.Perm (Fin (2 * k))),
      (∑ i, v i) = 0 → s2_action S Y a e (2 * k) v σ ≫ q = q)
    (hqfib : ∀ x y : ComplexPoint (g3_power Y (2 * k)),
      Point.map q x = Point.map q y →
        ∃ (v : Fin (2 * k) → ZMod S.m) (σ : Equiv.Perm (Fin (2 * k))),
          (∑ i, v i) = 0 ∧ Point.map (s2_action S Y a e (2 * k) v σ) x = y)
    (d : W ⟶ W)
    (hd : s2_action S Y a e (2 * k) (s2_delta S (2 * k) (by omega) 1) 1 ≫ q = q ≫ d)
    (b : Fin (Nat.totient S.m) →
      AlgebraicTopology.Singular.Cohomology ℚ (TopCat.of (ComplexPoint W)) (2 * k))
    (hb : Submodule.span ℚ (Set.range b) = LinearMap.ker
      (Polynomial.aeval (s4_singularPullback d (2 * k)) (Polynomial.cyclotomic S.m ℚ)))
    (hS2Cycle : ∀ i, ∃ zcycle : AlgebraicCycle W.left ℚ,
      (∀ x ∈ zcycle.support, Order.coheight x = k ∧
        ∃ U : W.left.Opens, x ∈ U ∧ Smooth (U.ι ≫ W.hom)) ∧
      ∃ c, a3b4_IsCycleClass W.hom zcycle k c ∧ s2e_classToAbsolute W zcycle k c = b i) :
    (LinearMap.ker (Polynomial.aeval (s4_singularPullback d (2 * k))
      (Polynomial.cyclotomic S.m ℚ))).map (s4_quotientPullback q (2 * k)) =
        s4_invariantPrimitive S Y a e (2 * k) (by omega) ∧
    s4_invariantPrimitive S Y a e (2 * k) (by omega) ≤
      cfd_cycleSpan (g3_power Y (2 * k)) k := by
  exact s4_q3c_quotient_cycles S Y hdim k hk a e ha1 hamul W q
    hqsurj hqinv hqfib d hd b hb hS2Cycle

end HodgeLean.Foundations.Program
