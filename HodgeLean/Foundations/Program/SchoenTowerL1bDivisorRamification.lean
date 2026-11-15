import HodgeLean.Foundations.Program.SchoenTowerL1bDivisorNormDescent
import HodgeLean.Foundations.Program.SchoenTowerL1bDivisorFixedBase
import HodgeLean.Foundations.Program.SchoenTowerL1bDivisorInvariantOrder
import HodgeLean.Foundations.Program.SchoenSelectedGeometryDominantStalk

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- A primitive stabilizer rescaling and invariant jet descent determine actual ramification. -/
theorem s2v_l1b_divisor_ramification_order
    (X Y : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [IsIntegral Y.left]
    (G : Type) [Group G] [Finite G]
    (a : G → (X ⟶ X)) (ha1 : a 1 = 𝟙 X)
    (hamul : ∀ u v, a (u * v) = a v ≫ a u)
    (q : X ⟶ Y) [IsFinite q.left] [Surjective q.left] [IsDominant q.left]
    (hinv : ∀ u, a u ≫ q = q)
    (hquot : ∀ (T : Over (Spec ↧ℂ)) (v : X ⟶ T),
      (∀ u, a u ≫ v = v) → ∃! w : Y ⟶ T, q ≫ w = v)
    (x : ComplexPoint X) (hclosed : IsClosed ({x.underlying} : Set X.left))
    (H : Subgroup G) (hH : ∀ g, Point.map (a g) x = x ↔ g ∈ H)
    [IsDiscreteValuationRing (X.left.presheaf.stalk x.underlying)]
    [IsDiscreteValuationRing (Y.left.presheaf.stalk (q.left x.underlying))]
    (ι : X.left.presheaf.stalk x.underlying →+* PowerSeries ℂ) (hι : Function.Injective ι)
    (t : X.left.presheaf.stalk x.underlying) (ht : Irreducible t)
    (htX : ι t = PowerSeries.X)
    (g : G) (hg : g ∈ H) (ζ : ℂ) (hζ : IsPrimitiveRoot ζ (Nat.card H))
    (hcomparison : ∀ v, ι (s2e_fixed_point_stalkPullback X.left (a g).left x.underlying
      (s2e_complex_point_fixed_underlying X (a g) x ((hH g).mpr hg)) v) =
        PowerSeries.rescale ζ (ι v))
    (p : Y.left.presheaf.stalk (q.left x.underlying)) (hp : Prime p) :
    (ι ((q.left.stalkMap x.underlying).hom p)).order.toNat = Nat.card H := by
  let β := ι.comp (q.left.stalkMap x.underlying).hom
  have hβ : Function.Injective β :=
    hι.comp (s0_dominant_stalkMap_injective q.left x.underlying)
  have hlocal (v : Y.left.presheaf.stalk (q.left x.underlying)) (hv : ¬ p ∣ v) :
      (β v).constantCoeff ≠ 0 := by
    have hvunit : IsUnit v := by
      by_contra hn
      have hm : v ∈ IsLocalRing.maximalIdeal _ := hn
      rw [hp.irreducible.maximalIdeal_eq, Ideal.mem_span_singleton] at hm
      exact hv hm
    exact (PowerSeries.isUnit_constantCoeff _ (hvunit.map β)).ne_zero
  obtain ⟨c, hc⟩ := s2v_l1b_divisor_norm_descent X Y G a ha1 hamul q hinv hquot
    x hclosed H hH ι t ht htX
  apply s2v_l1b_divisor_parameter_order_of_descended_element β hβ p hp hlocal hζ
    (c := c) (hc := hc)
  change PowerSeries.rescale ζ (ι ((q.left.stalkMap x.underlying).hom p)) = _
  rw [← hcomparison, s2v_l1b_divisor_fixed_base_stalk q.left (a g).left
    (congrArg Over.Hom.left (hinv g))]
  rfl

end HodgeLean.Foundations.Program
