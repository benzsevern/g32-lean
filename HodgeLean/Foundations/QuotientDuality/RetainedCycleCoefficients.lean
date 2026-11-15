import HodgeLean.Foundations.QuotientDuality.RetainedCycleDefs
import HodgeLean.Adapters.CyclePushforward
import HodgeLean.Foundations.QuotientDuality.RetainedCycleDimension

noncomputable section
open CategoryTheory AlgebraicGeometry
open HodgeLean.Adapters HodgeLean.Foundations.Program
open scoped BigOperators Classical
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace HodgeLean.Foundations.QuotientDuality

theorem retained_pushforward_sum {X Y : Scheme} (f : X ⟶ Y) [QuasiCompact f]
    {I : Type*} (s : Finset I) (c : I → AlgebraicCycle X ℚ) :
    a1p_pushforward f (∑ i ∈ s, c i) = ∑ i ∈ s, a1p_pushforward f (c i) := by
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    have h := a1p_pushforward_add f (0 : AlgebraicCycle X ℚ) 0
    rw [add_zero] at h
    exact left_eq_add.mp h
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi, a1p_pushforward_add, ih]

theorem retained_orbit_coefficient_formula {Q W Y : Over (Spec ↧ℂ)}
    [IsIntegral Q.left] (f : W ⟶ Y) [QuasiCompact f.left]
    (ι : Q ⟶ W) (δ : W ⟶ W) (m : ℕ) (a : Fin m → ℚ) (y : Y.left) :
    retainedOrbitCoefficient f ι δ m a y =
      ∑ t : Fin m, if f.left ((ι ≫ (End.of δ ^ t.val).asHom).left
        (genericPoint Q.left)) = y then a t * (a1p_degree f.left
          ((ι ≫ (End.of δ ^ t.val).asHom).left (genericPoint Q.left)) : ℚ) else 0 := by
  unfold retainedOrbitCoefficient s2e_rationalOrbitCycle
  rw [retained_pushforward_sum]
  simp only [Function.locallyFinsuppWithin.coe_sum, Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro t ht
  rw [a1p_pushforward_mul]
  simp only [s2e_componentCycle, a1p_pushforward_single, one_mul,
    Function.locallyFinsuppWithin.mapRange_apply,
    Function.locallyFinsuppWithin.single_apply]
  split_ifs <;> simp_all

theorem retained_orbit_support_coheight {Q W Y : Over (Spec ↧ℂ)}
    [IsIntegral Q.left] [IsIntegral W.left] [IsIntegral Y.left]
    [LocallyOfFiniteType W.hom] [LocallyOfFiniteType Y.hom]
    (f : W ⟶ Y) [QuasiCompact f.left]
    (ι : Q ⟶ W) (δ : W ⟶ W) (m k : ℕ) (a : Fin m → ℚ)
    (hW : TopologicalSpace.dim W.left = 2 * k)
    (hY : TopologicalSpace.dim Y.left = 2 * k)
    (hc : ∀ t : Fin m, Order.coheight
      ((ι ≫ (End.of δ ^ t.val).asHom).left (genericPoint Q.left)) = k)
    (y : Y.left) (hy : y ∈ (a1p_pushforward f.left
      (s2e_rationalOrbitCycle ι δ m a)).support) : Order.coheight y = k := by
  have hy' : retainedOrbitCoefficient f ι δ m a y ≠ 0 := hy
  rw [retained_orbit_coefficient_formula] at hy'
  obtain ⟨t, _, ht⟩ := Finset.exists_ne_zero_of_sum_ne_zero hy'
  split_ifs at ht with he
  · have hd : 0 < a1p_degree f.left
        ((ι ≫ (End.of δ ^ t.val).asHom).left (genericPoint Q.left)) := by
      apply Nat.pos_of_ne_zero
      intro hz
      apply ht
      rw [hz, Nat.cast_zero, mul_zero]
    have hh := (a1d_degree_pos_iff f _).mp hd
    have hsource := retained_integral_dimension_formula W
      ((ι ≫ (End.of δ ^ t.val).asHom).left (genericPoint Q.left))
    have htarget := retained_integral_dimension_formula Y y
    rw [hW, hc t] at hsource
    rw [he] at hh
    rw [hY, hh] at htarget
    exact ENat.add_right_injective_of_ne_top
      (ne_top_of_le_ne_top (ENat.natCast_ne_top (2 * k))
        (by rw [← hsource]; exact le_self_add)) (htarget.trans hsource.symm)
  · exact (ht rfl).elim

end HodgeLean.Foundations.QuotientDuality
