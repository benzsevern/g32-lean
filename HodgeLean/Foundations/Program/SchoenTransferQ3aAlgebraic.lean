import HodgeLean.Foundations.Program.SchoenTransferQ3CycleCodimension
import HodgeLean.Foundations.Program.SchoenTransferQ3RetainedSupport
import HodgeLean.Foundations.Program.SchoenTransferQ3Pushforward

/-! Algebraic clauses of Q3a from the original retained orbit geometry. -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint TopologicalSpace
open HodgeLean.Adapters AlgebraicGeometry.SingularCycles
open scoped BigOperators Classical
namespace HodgeLean.Foundations.Program

/-- The actual retained inverse cycle has pure codimension, the unreduced
multiplicities, the residue-degree pushforward and the entire inverse support. -/
theorem s4_q3a_retained_algebraic_comparison (S : g32p_Supplier)
    (Y : Over (Spec ↧ℂ)) (k : ℕ)
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
    (z : AlgebraicCycle W.left ℚ) (hz : ∀ x ∈ z.support, Order.coheight x = k) :
    let γ := ccm3_flatPullback q.left z
    (∀ p ∈ γ.support, Order.coheight p = k) ∧
    (∀ x ∈ z.support,
      ∀ (y : (ccm3_inverseIdeal q.left x).subscheme)
        (hy : closure ({y} : Set (ccm3_inverseIdeal q.left x).subscheme) ∈
          irreducibleComponents (ccm3_inverseIdeal q.left x).subscheme),
        γ ((ccm3_inverseIdeal q.left x).subschemeι y) =
          z x * (genericMultiplicity q.left x y
            (ccm3_genericLength_finite_pos q x y hy).2 : ℚ)) ∧
    (AlgebraicCycle.map q.left (fun _ => k) (fun _ => k) γ =
      ∑ᶠ y : (g3_power Y (2 * k)).left,
        Function.locallyFinsuppWithin.single (q.left y) ((q.left.residueDegree y : ℚ) * γ y)) ∧
    a3b4_cycleSupport (g3_power Y (2 * k)).hom γ =
      Point.map q ⁻¹' a3b4_cycleSupport W.hom z := by
  let X := g3_power Y (2 * k)
  letI : IsLocallyNoetherian X.left := LocallyOfFiniteType.isLocallyNoetherian X.hom
  letI : CompactSpace X.left := QuasiCompact.compactSpace_of_compactSpace X.hom
  letI : IsNoetherian X.left := {}
  have hopen := s4_q3_retained_schemeMap_isOpenMap S Y (2 * k) a e ha1 hamul
    W q hqsurj hqinv hqfib
  exact ⟨s4_q3_flatPullback_pure_coheight q hopen z k hz,
    fun x _ y hy => s4_q3_inverse_component_coefficient q hopen z x y hy,
    s4_q3_constant_weight_pushforward q.left k _,
    s4_q3_flatPullback_support_preimage q hopen z⟩

end HodgeLean.Foundations.Program
