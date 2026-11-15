import HodgeLean.Foundations.Program.SchoenTowerI2aDiagonalTranslations
import Mathlib.AlgebraicGeometry.AlgClosed.Basic

/-! # Full order of the retained residual deck map
HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
open HodgeLean.Adapters
open scoped BigOperators
namespace HodgeLean.Foundations.Program

/-- Every period of the residual scheme deck map is divisible by the supplier order.
Source: Schoen (1988), section 1, the sum-kernel quotient; Mathlib, determination of reduced separated scheme maps on closed points. -/
theorem s2v_i2a_residual_period_dvd
    (S : g32p_Supplier) (Y W : Over (Spec ↧ℂ))
    [IsReduced Y.left] [IsSeparated Y.hom] [LocallyOfFiniteType Y.hom]
    (a : (S.H ⧸ S.χ.ker) → (Y ⟶ Y))
    (e : (S.H ⧸ S.χ.ker) ≃* Multiplicative (ZMod S.m))
    (ha1 : a 1 = 𝟙 Y) (hamul : ∀ u v, a (u * v) = a v ≫ a u)
    (hinj : Function.Injective a)
    (n : ℕ) (hn : 0 < n) (q : g3_power Y n ⟶ W)
    (hq : ∀ x z : ComplexPoint (g3_power Y n),
      Point.map q x = Point.map q z →
        ∃ (v : Fin n → ZMod S.m) (τ : Equiv.Perm (Fin n)),
          (∑ i, v i = 0) ∧ Point.map (s2_action S Y a e n v τ) x = z)
    (d : W ⟶ W)
    (hgenerator : q ≫ d = s2_action S Y a e n (s2_delta S n hn 1) 1 ≫ q)
    (k : ℕ) (hk : (End.of d) ^ k = 1) : S.m ∣ k := by
  have hpoints (y : ComplexPoint Y) :
      Point.map (a (e.symm (.ofAdd (k : ZMod S.m)))) y = y := by
    apply s2v_i2a_diagonal_translation_fixed S Y W a e ha1 hamul n hn q hq y
    have H := s2v_i2a_pointMap_end_power W d k (Point.map q (s2_lift n (fun _ => y)))
    rw [hk, End.one_asHom, Point.map_id,
      s2v_residual_generator_iterate S Y W a e ha1 hamul n hn q d hgenerator] at H
    exact H.symm
  have hcurve : a (e.symm (.ofAdd (k : ZMod S.m))) = 𝟙 Y := by
    apply Over.OverMorphism.ext
    haveI : LocallyOfFiniteType ((a (e.symm (.ofAdd (k : ZMod S.m)))).left ≫ Y.hom) := by
      rw [Over.w]; infer_instance
    apply ext_of_apply_eq Y.hom Set.univ isClosed_univ.isLocallyClosed dense_univ
    · intro x hx hxc
      let y : ComplexPoint Y := Over.homMk (pointOfClosedPoint Y.hom x hxc)
        (pointOfClosedPoint_comp Y.hom x hxc)
      have H := congrArg (fun z : ComplexPoint Y => z.left (IsLocalRing.closedPoint ℂ)) (hpoints y)
      change (a (e.symm (.ofAdd (k : ZMod S.m)))).left
        (y.left (IsLocalRing.closedPoint ℂ)) = y.left (IsLocalRing.closedPoint ℂ) at H
      have hyx : y.left (IsLocalRing.closedPoint ℂ) = x :=
        pointOfClosedPoint_apply Y.hom x hxc _
      rw [hyx] at H
      change (a (e.symm (.ofAdd (k : ZMod S.m)))).left x = x
      exact H
    · simp only [Over.w, Over.id_left, Category.id_comp]
  have hu := hinj (hcurve.trans ha1.symm)
  have hcast : (k : ZMod S.m) = 0 := by
    have H := congrArg e hu
    have H' : Multiplicative.ofAdd (k : ZMod S.m) = 1 := by simpa using H
    exact congrArg Multiplicative.toAdd H'
  exact (ZMod.natCast_eq_zero_iff k S.m).mp hcast

/-- The retained residual deck map has full supplier order.
Source: Schoen (1988), section 1, the residual cyclic action, detected on diagonal tuples. -/
theorem s2v_i2a_residual_order_eq
    (S : g32p_Supplier) (Y W : Over (Spec ↧ℂ))
    [IsReduced Y.left] [IsSeparated Y.hom] [LocallyOfFiniteType Y.hom]
    (a : (S.H ⧸ S.χ.ker) → (Y ⟶ Y))
    (e : (S.H ⧸ S.χ.ker) ≃* Multiplicative (ZMod S.m))
    (ha1 : a 1 = 𝟙 Y) (hamul : ∀ u v, a (u * v) = a v ≫ a u)
    (hinj : Function.Injective a)
    (n : ℕ) (hn : 0 < n) (q : g3_power Y n ⟶ W)
    (hq : ∀ x z : ComplexPoint (g3_power Y n),
      Point.map q x = Point.map q z →
        ∃ (v : Fin n → ZMod S.m) (τ : Equiv.Perm (Fin n)),
          (∑ i, v i = 0) ∧ Point.map (s2_action S Y a e n v τ) x = z)
    (d : W ⟶ W)
    (hgenerator : q ≫ d = s2_action S Y a e n (s2_delta S n hn 1) 1 ≫ q)
    (hperiod : (End.of d) ^ S.m = 1) : orderOf (End.of d) = S.m := by
  apply Nat.dvd_antisymm (orderOf_dvd_of_pow_eq_one hperiod)
  exact s2v_i2a_residual_period_dvd S Y W a e ha1 hamul hinj n hn q hq d
    hgenerator _ (pow_orderOf_eq_one _)

end HodgeLean.Foundations.Program
