import HodgeLean.Foundations.Program.SchoenTransferQ3aChecks
import HodgeLean.Foundations.Program.SchoenTransferQ3aProofs

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
/-- Retained Q3a comparison on the actual inverse-image cycle.
Source: Fulton, Intersection Theory, second edition, §§1.7 and 19.1–19.2; S4 chain Q3.1–2. -/
theorem s4_q3a_local_multiplicities (S : g32p_Supplier)
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
    ∃ (U : W.left.Opens),
      Dense (U : Set W.left) ∧ Smooth (U.ι ≫ W.hom) ∧ Flat (q.left ∣_ U) ∧
      (∀ x ∈ z.support, x ∈ U) ∧
      ∃ (γ : AlgebraicCycle (g3_power Y (2 * k)).left ℚ), γ = ccm3_flatPullback q.left z ∧
      (∀ x ∈ γ.support, Order.coheight x = k) ∧
      (∀ x ∈ z.support,
        ∀ (y : (ccm3_inverseIdeal q.left x).subscheme)
          (hy : closure ({y} : Set (ccm3_inverseIdeal q.left x).subscheme) ∈
            irreducibleComponents (ccm3_inverseIdeal q.left x).subscheme),
          γ ((ccm3_inverseIdeal q.left x).subschemeι y) =
            z x * (genericMultiplicity q.left x y
              (ccm3_genericLength_finite_pos q x y hy).2 : ℚ)) ∧
      (AlgebraicCycle.map q.left (fun _ => k) (fun _ => k) γ =
        ∑ᶠ y : (g3_power Y (2 * k)).left,
          Function.locallyFinsuppWithin.single (q.left y)
            ((q.left.residueDegree y : ℚ) * γ y)) ∧
      a3b4_cycleSupport (g3_power Y (2 * k)).hom γ = Point.map q ⁻¹' a3b4_cycleSupport W.hom z ∧
      ∃ (hS : ∀ x, Point.map q x ∈ a3b4_cycleSupport W.hom z →
        x ∈ a3b4_cycleSupport (g3_power Y (2 * k)).hom γ),
      let β := relativeCohomologyMap ℚ (2 * k)
        (a3b4_supportPairMap (TopCat.ofHom (Point.continuousMap q))
          (a3b4_cycleSupport (g3_power Y (2 * k)).hom γ) (a3b4_cycleSupport W.hom z) hS) c
      ∀ (r : ℕ)
        (e : OpenPartialHomeomorph (ComplexPoint (g3_power Y (2 * k))) ((Fin r → ℂ) × (Fin k → ℂ)))
        (hflat : ∀ y ∈ e.source, y ∈ a3b4_cycleSupport (g3_power Y (2 * k)).hom γ ↔ (e y).2 = 0)
        (x : ComplexPoint (g3_power Y (2 * k))),
        x ∈ e.source → x ∈ a3b4_cycleSupport (g3_power Y (2 * k)).hom γ →
        (Point.map q x).underlying ∈ U → a3b4_IsHolChart (g3_power Y (2 * k)).hom e →
        ∃ (V : Set (ComplexPoint (g3_power Y (2 * k)))) (hV : V ⊆ e.source), IsOpen V ∧ x ∈ V ∧
          (∀ y ∈ V, (Point.map q y).underlying ∈ U) ∧
          relativeCohomologyMap ℚ (2 * k)
            (a3b4_neighborhoodPairMap V (a3b4_cycleSupport (g3_power Y (2 * k)).hom γ)) β =
          a3b4_multiplicity (g3_power Y (2 * k)).hom γ x •
            chartNormalProjectionCoclass (Fin r → ℂ) k e
              (a3b4_cycleSupport (g3_power Y (2 * k)).hom γ) hflat V hV :=
  s4_q3a_local_multiplicities_aux S Y hdim k hk a e ha1 hamul W q hqsurj hqinv hqfib z hz c hc

example := s4_q3a_local_multiplicities_falsification


end HodgeLean.Foundations.Program
