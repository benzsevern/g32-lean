import HodgeLean.Foundations.Program.G32Native.ComplexOrbitRestriction

/-! # Numerical detection of the final component orbit -/
noncomputable section
set_option maxHeartbeats 200000
open CategoryTheory AlgebraicGeometry
open HodgeLean.Adapters HodgeLean.Foundations.Program
namespace HodgeLean.Foundations.Program.G32Native
open HodgeLean.Foundations.Program.G32Native.TowerOrbit

/-- A numerical self-intersection detects every primitive inverse orbit sum.
This uses the actual supported class and needs no coefficient-one Euler formula. -/
theorem numerical_normal_weighted_nonzero
    {Q W : Over (Spec ↧ℂ)} [IsIntegral Q.left]
    (ι : Q ⟶ W) [IsClosedImmersion ι.left] (d : W ⟶ W)
    (m : ℕ) (hm : 0 < m) (hperiod : End.of d ^ m = 1)
    (hdis : ∀ s t : Fin m, s ≠ t → Disjoint
      (Set.range (ι ≫ (End.of d ^ s.val).asHom).left)
      (Set.range (ι ≫ (End.of d ^ t.val).asHom).left))
    (k : ℕ) (c : s2e_supportedClass W (s2e_componentCycle ι ℚ) k)
    (degree : AlgebraicTopology.Singular.Cohomology ℚ
      (TopCat.of (ComplexPoint Q)) (2 * k) →ₗ[ℚ] ℚ)
    (hdegree : degree (s2e_normalEuler ι k c) ≠ 0) :
    ∀ ζ : ℂ, IsPrimitiveRoot ζ m →
      s2e_weightedSum m (fun t : ZMod m => ζ ^ t.val)
        (fun t : Fin m => TensorProduct.tmul ℚ (1 : ℂ)
          (s2e_pullback ℚ ((End.of d ^ (m - t.val)).asHom) (2 * k)
            (s2e_classToAbsolute W (s2e_componentCycle ι ℚ) k c))) ≠ 0 := by
  have hn : s2e_normalEuler ι k c ≠ 0 := by
    intro hz
    exact hdegree (by rw [hz, map_zero])
  intro ζ _
  exact complex_inverse_orbit_ne_zero ι d m hm hperiod hdis _ (by
    rw [ZMod.val_zero, pow_zero]) k c hn

/-- Any nonzero coefficient of a numerically nonzero top class suffices.
The coefficient is retained, so no coefficient-one normalization is asserted. -/
theorem numerical_normal_degree_of_scalar
    {Q W : Over (Spec ↧ℂ)} [IsIntegral Q.left]
    (ι : Q ⟶ W) (k : ℕ)
    (c : s2e_supportedClass W (s2e_componentCycle ι ℚ) k)
    (degree : AlgebraicTopology.Singular.Cohomology ℚ
      (TopCat.of (ComplexPoint Q)) (2 * k) →ₗ[ℚ] ℚ)
    (H : AlgebraicTopology.Singular.Cohomology ℚ
      (TopCat.of (ComplexPoint Q)) (2 * k))
    (a : ℚ) (ha : a ≠ 0)
    (hmodel : s2e_normalEuler ι k c = a • H)
    (hH : degree H ≠ 0) : degree (s2e_normalEuler ι k c) ≠ 0 := by
  rw [hmodel, map_smul, smul_eq_mul]
  exact mul_ne_zero ha hH

#print axioms numerical_normal_degree_of_scalar
#print axioms numerical_normal_weighted_nonzero
end HodgeLean.Foundations.Program.G32Native
