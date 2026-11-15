import HodgeLean.Foundations.QuotientDuality.RetainedCycleCoefficients
import Other.AlgebraicGeometry.Cycle.Component.GenericPoint

noncomputable section
open CategoryTheory AlgebraicGeometry
open HodgeLean.Adapters
open scoped Classical
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace HodgeLean.Foundations.QuotientDuality

theorem retained_prime_pushforward_formula {X Y : Over (Spec ↧ℂ)}
    (f : X ⟶ Y) [QuasiCompact f.left] (x : X.left) :
    a1p_pushforward f.left (properPrime x) =
      (properPrime (f.left x)).mapRange ((a1p_degree f.left x : ℚ) * ·) (mul_zero _) := by
  rw [properPrime, a1p_pushforward_single]
  ext y
  simp only [one_mul, properPrime, Function.locallyFinsuppWithin.mapRange_apply,
    Function.locallyFinsuppWithin.single_apply]
  split_ifs <;> simp

theorem retained_positive_degree_coheight {X Y : Over (Spec ↧ℂ)}
    [IsIntegral X.left] [IsIntegral Y.left]
    [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    (f : X ⟶ Y) (n : ℕ)
    (hX : TopologicalSpace.dim X.left = n) (hY : TopologicalSpace.dim Y.left = n)
    (x : X.left) (hd : 0 < a1p_degree f.left x) :
    Order.coheight (f.left x) = Order.coheight x := by
  have hs := retained_integral_dimension_formula X x
  have ht := retained_integral_dimension_formula Y (f.left x)
  have hh := (a1d_degree_pos_iff f x).mp hd
  rw [hX] at hs
  rw [hY, hh] at ht
  exact ENat.add_right_injective_of_ne_top
    (ne_top_of_le_ne_top (ENat.natCast_ne_top n)
      (by rw [← hs]; exact le_self_add)) (ht.trans hs.symm)

theorem retained_intrinsic_component_dimension (X : Over (Spec ↧ℂ))
    [IsIntegral X.left] [LocallyOfFiniteType X.hom]
    (k : ℕ) (hX : TopologicalSpace.dim X.left = 2 * k)
    (x : X.left) (hc : Order.coheight x = k) :
    TopologicalSpace.dim (intrinsicComponent X x).left = k := by
  have hsum := retained_integral_dimension_formula X x
  rw [hX, hc] at hsum
  have hh : Order.height x = k :=
    ENat.add_left_injective_of_ne_top (ENat.natCast_ne_top k)
      (show Order.height x + (k : ℕ∞) = (k : ℕ∞) + k by
        rw [hsum]; norm_cast; omega)
  have hcomp : Order.height (genericPoint (cycleComponent X.left x)) = Order.height x := by
    rw [← cycleComponentGenericPoint_eq_genericPoint]
    exact height_cycleComponentGenericPoint X.left x
  rw [TopologicalSpace.dim_eq_krullDim, ← Order.height_top_eq_krullDim]
  change (Order.height (genericPoint (cycleComponent X.left x))).toNat = k
  rw [hcomp, hh, ENat.toNat_natCast]

end HodgeLean.Foundations.QuotientDuality
