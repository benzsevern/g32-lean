import HodgeLean.Foundations.Program.SchoenCyclePushDefs

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
open scoped BigOperators
namespace HodgeLean.Foundations.Program

/-- Rational orbit coefficients act linearly on any family of absolute classes. -/
def s2e_orbitLinearMap {m : ℕ} {V : Type*} [AddCommGroup V] [Module ℚ V]
    (v : Fin m → V) : (Fin m → ℚ) →ₗ[ℚ] V where
  toFun a := ∑ t, a t • v t
  map_add' a b := by
    simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' a b := by
    simp only [Pi.smul_apply, smul_eq_mul, mul_smul, Finset.smul_sum,
      RingHom.id_apply]

/-- Evaluation on a coordinate vector retains its component class. -/
theorem s2e_orbitLinearMap_single {m : ℕ} {V : Type*}
    [AddCommGroup V] [Module ℚ V] (v : Fin m → V) (t : Fin m) :
    s2e_orbitLinearMap v (Pi.single t 1) = v t := by
  classical
  simp [s2e_orbitLinearMap, Pi.single_apply]

/-- Any nonzero coefficient of a rational orbit sum comes from an orbit component. -/
theorem s2e_rationalOrbitCycle_support_subset
    {Q W : Over (Spec ↧ℂ)} [IsIntegral Q.left]
    (ι : Q ⟶ W) (δ : W ⟶ W) (m : ℕ) (a : Fin m → ℚ) :
    (s2e_rationalOrbitCycle ι δ m a).support ⊆
      ⋃ t : Fin m, (s2e_componentCycle (ι ≫ (End.of δ ^ t.val).asHom) ℚ).support := by
  intro x hx
  by_contra h
  have hz : ∀ t : Fin m,
      (s2e_componentCycle (ι ≫ (End.of δ ^ t.val).asHom) ℚ) x = 0 := by
    intro t
    by_contra ht
    exact h (Set.mem_iUnion.mpr ⟨t, ht⟩)
  apply hx
  change (∑ t : Fin m, (s2e_componentCycle (ι ≫ (End.of δ ^ t.val).asHom) ℚ).mapRange
    (a t * ·) (mul_zero _)) x = 0
  simp only [Function.locallyFinsuppWithin.coe_sum, Finset.sum_apply,
    Function.locallyFinsuppWithin.mapRange_apply, hz, mul_zero, Finset.sum_const_zero]

/-- Component coheight is preserved by finite rational combinations. -/
theorem s2e_rationalOrbitCycle_coheight
    {Q W : Over (Spec ↧ℂ)} [IsIntegral Q.left]
    (ι : Q ⟶ W) (δ : W ⟶ W) (k m : ℕ)
    (h : ∀ t : Fin m, ∀ x ∈
      (s2e_componentCycle (ι ≫ (End.of δ ^ t.val).asHom) ℚ).support,
      Order.coheight x = k) (a : Fin m → ℚ) :
    ∀ x ∈ (s2e_rationalOrbitCycle ι δ m a).support, Order.coheight x = k := by
  intro x hx
  obtain ⟨t, ht⟩ := Set.mem_iUnion.mp
    (s2e_rationalOrbitCycle_support_subset ι δ m a hx)
  exact h t x ht

end HodgeLean.Foundations.Program
