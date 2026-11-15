import HodgeLean.Foundations.Program.SchoenTransferQ3cChecks
import HodgeLean.Foundations.Program.SchoenTransferQ3cProofs

/-! Retained finite-map cycle comparison, as an implication from the displayed geometric inputs.
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open AlgebraicTopology.Singular TopologicalSpace HodgeLean.Adapters HodgeLean.RealDefs
open AlgebraicGeometry.SingularCycles
open scoped BigOperators Classical
namespace HodgeLean.Foundations.Program
/-- Retained Q3c comparison on the actual inverse-image cycle.
Source: Fulton, Intersection Theory, second edition, §§19.1–19.2; S4 chain Q3.3–4. -/
theorem s4_q3c_absolute_pullback (S : g32p_Supplier)
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
    (z : AlgebraicCycle W.left ℚ)
    (hz : ∀ x ∈ z.support, Order.coheight x = k ∧
      ∃ U : W.left.Opens, x ∈ U ∧ Smooth (U.ι ≫ W.hom))
    (c : s2e_supportedClass W z k) (hc : a3b4_IsCycleClass W.hom z k c) :
    ∃ (γ : AlgebraicCycle (g3_power Y (2 * k)).left ℚ) (β : s2e_supportedClass (g3_power Y (2 * k)) γ k),
      γ = ccm3_flatPullback q.left z ∧
      (∀ x ∈ γ.support, Order.coheight x = k) ∧
      a3b4_IsCycleClass (g3_power Y (2 * k)).hom γ k β ∧
      s4_singularPullback q (2 * k) (s2e_classToAbsolute W z k c) =
        s2e_classToAbsolute (g3_power Y (2 * k)) γ k β ∧
      s4_quotientPullback q (2 * k) (s2e_classToAbsolute W z k c) ∈ cfd_cycleSpan (g3_power Y (2 * k)) k :=
  s4_q3c_absolute_pullback_aux S Y hdim k hk a e ha1 hamul W q hqsurj hqinv hqfib z hz c hc

example := s4_q3c_absolute_pullback_falsification


/-- Retained Q3c comparison on the actual inverse-image cycle.
Source: Schoen, Hodge classes on self-products of a variety with an automorphism, Compositio Mathematica 65 (1988), Theorem 2.0; S4 chain Q3.5. -/
theorem s4_q3c_quotient_cycles (S : g32p_Supplier)
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
      cfd_cycleSpan (g3_power Y (2 * k)) k :=
  s4_q3c_quotient_cycles_aux S Y hdim k hk a e ha1 hamul W q hqsurj hqinv hqfib d hd b hb hS2Cycle
example := s4_q3c_quotient_cycles_falsification


end HodgeLean.Foundations.Program
