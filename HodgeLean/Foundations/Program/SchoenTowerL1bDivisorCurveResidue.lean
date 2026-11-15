import HodgeLean.Foundations.Program.SchoenTowerL1bDivisorRamification
import HodgeLean.Foundations.Program.SchoenTowerL1bDivisorGenericStalk
import HodgeLean.Foundations.Program.SchoenTowerL1bDivisorLocalCalculation

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- The original quotient's actual ramification computes every rational base presentation's residue. -/
theorem s2v_l1b_divisor_curve_residue
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
    (g : G) (hg : g ∈ H) (ξ : ℂ) {m w k : ℕ} (hm : m ≠ 0)
    (hme : m = Nat.card H * w) (hξ : IsPrimitiveRoot ξ m)
    (hcomparison : ∀ v, ι (s2e_fixed_point_stalkPullback X.left (a g).left x.underlying
      (s2e_complex_point_fixed_underlying X (a g) x ((hH g).mpr hg)) v) =
        PowerSeries.rescale (ξ ^ w) (ι v))
    (c : X.left.presheaf.stalk x.underlying) (hc : ι c = PowerSeries.C (ξ ^ k))
    (u : X.left.functionField) (hu : u ≠ 0)
    (heigen : letI : IsIso (a g).left := (by
      change IsIso ((s2v_l1b_divisor_actionAut X G a ha1 hamul g).asIso.hom.left)
      infer_instance)
      s2v_l1b_functionFieldPullback (a g).left u =
        algebraMap (X.left.presheaf.stalk x.underlying) X.left.functionField c * u)
    (A B : Y.left.presheaf.stalk (q.left x.underlying)) (hA : A ≠ 0) (hB : B ≠ 0)
    (hpow : u ^ m = s2v_l1b_functionFieldPullback q.left
      (algebraMap _ Y.left.functionField A / algebraMap _ Y.left.functionField B))
    (p : Y.left.presheaf.stalk (q.left x.underlying)) (hp : Prime p) :
    Int.ModEq (m : ℤ)
      (((emultiplicity p A).toNat : ℤ) - ((emultiplicity p B).toNat : ℤ)) (k : ℤ) := by
  letI : IsIso (a g).left := by
    change IsIso ((s2v_l1b_divisor_actionAut X G a ha1 hamul g).asIso.hom.left)
    infer_instance
  let φ := (q.left.stalkMap x.underlying).hom
  have hφ := s0_dominant_stalkMap_injective q.left x.underlying
  have hlocal (v : Y.left.presheaf.stalk (q.left x.underlying)) (hv : ¬ p ∣ v) :
      (ι (φ v)).constantCoeff ≠ 0 := by
    have hvunit : IsUnit v := by
      by_contra hn
      have hm : v ∈ IsLocalRing.maximalIdeal _ := hn
      rw [hp.irreducible.maximalIdeal_eq, Ideal.mem_span_singleton] at hm
      exact hv hm
    exact (PowerSeries.isUnit_constantCoeff _ ((hvunit.map φ).map ι)).ne_zero
  have heorder := s2v_l1b_divisor_ramification_order X Y G a ha1 hamul q hinv hquot
    x hclosed H hH ι hι t ht htX g hg (ξ ^ w)
    (IsPrimitiveRoot.pow (Nat.pos_of_ne_zero hm) hξ (hme.trans (mul_comm _ _))) hcomparison p hp
  apply s2v_l1b_divisor_local_calculation φ hφ ι hι
    (s2e_fixed_point_stalkPullback X.left (a g).left x.underlying
      (s2e_complex_point_fixed_underlying X (a g) x ((hH g).mpr hg)))
    (s2v_l1b_functionFieldPullback (a g).left).hom ξ
    (s2v_l1b_transport_generic_stalk_pullback X.left (a g).left x.underlying _)
    hm (Nat.card_pos.ne') hme hξ hcomparison c hc u hu heigen p hp hlocal heorder A B hA hB
  rw [hpow, map_div₀, s2v_l1b_divisor_generic_stalk, s2v_l1b_divisor_generic_stalk]

end HodgeLean.Foundations.Program
