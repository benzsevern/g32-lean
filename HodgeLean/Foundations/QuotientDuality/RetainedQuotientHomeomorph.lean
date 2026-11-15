import HodgeLean.Foundations.QuotientDuality.RetainedCoordinateOrbits
import HodgeLean.Foundations.QuotientDuality.LocalOrbitHomeomorph
import HodgeConjecture.Lemmas.AlgebraicGeometry.ComplexPoint.ProjectiveCompact
import HodgeConjecture.Lemmas.AlgebraicGeometry.ComplexPoint.ProjectiveHausdorff

/-! The actual retained initial quotient is the finite coordinate orbit space. -/
noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint HodgeLean.Adapters
open HodgeLean.Foundations.Program HodgeLean.Foundations
open scoped BigOperators
namespace HodgeLean.Foundations.QuotientDuality

theorem retained_coordinate_quotient_homeomorph
    (S : g32p_Supplier) (Y W : Over (Spec ↧ℂ))
    [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]
    [IsIntegral W.left] [IsProjective W.hom]
    (a : (S.H ⧸ S.χ.ker) → (Y ⟶ Y))
    (e : (S.H ⧸ S.χ.ker) ≃* Multiplicative (ZMod S.m))
    (ha1 : a 1 = 𝟙 Y) (hamul : ∀ u v, a (u * v) = a v ≫ a u)
    (n : ℕ) (q : g3_power Y n ⟶ W) [IsFinite q.left]
    (hsurj : Function.Surjective (Point.map q))
    (hinv : ∀ (v : Fin n → ZMod S.m) (σ : Equiv.Perm (Fin n)),
      ∑ i, v i = 0 → s2_action S Y a e n v σ ≫ q = q)
    (hquot : ∀ (T : Over (Spec ↧ℂ)) (f : g3_power Y n ⟶ T),
      (∀ (v : Fin n → ZMod S.m) (σ : Equiv.Perm (Fin n)),
        ∑ i, v i = 0 → s2_action S Y a e n v σ ≫ f = f) →
      ∃! u : W ⟶ T, q ≫ u = f)
    : ∃ H : Quotient (MulAction.orbitRel
        (retainedCoordinateSubgroup S Y a e ha1 hamul n) (ComplexPoint (g3_power Y n))) ≃ₜ
        ComplexPoint W,
      ∀ x, H (Quotient.mk _ x) = Point.map q x := by
  let G := retainedCoordinateSubgroup S Y a e ha1 hamul n
  apply compact_orbit_quotient_homeomorph G (ComplexPoint (g3_power Y n)) (ComplexPoint W)
    (Point.map q) (Point.continuous_map q) hsurj
  · intro g x
    obtain ⟨v, hv, σ, hg⟩ := g.property
    change Point.map q (Point.map g.val.asIso.hom x) = Point.map q x
    rw [hg, ← Point.map_comp_apply, hinv v σ hv]
  · intro x y hxy
    exact (retained_coordinate_quotient_orbits S Y W a e ha1 hamul n q hsurj hinv hquot x y).mp hxy

#print axioms retained_coordinate_quotient_homeomorph
end HodgeLean.Foundations.QuotientDuality
