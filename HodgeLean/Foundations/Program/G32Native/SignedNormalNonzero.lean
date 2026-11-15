import HodgeLean.Foundations.Program.G32Native.ComplexOrbitRestriction

/-! # Weighted classes on the retained final component -/
noncomputable section
set_option maxHeartbeats 200000
open CategoryTheory AlgebraicGeometry
open HodgeLean.Adapters HodgeLean.Foundations.Program
namespace HodgeLean.Foundations.Program.G32Native
open HodgeLean.Foundations.Program.G32Native.TowerOrbit

/-- A signed normal restriction with coefficient one detects the actual component orbit. -/
theorem signed_normal_weighted_nonzero
    {Q W : Over (Spec ↧ℂ)} [IsIntegral Q.left]
    (ι : Q ⟶ W) [IsClosedImmersion ι.left] (d : W ⟶ W)
    (m : ℕ) (hm : 0 < m) (hperiod : End.of d ^ m = 1)
    (hdis : ∀ s t : Fin m, s ≠ t → Disjoint
      (Set.range (ι ≫ (End.of d ^ s.val).asHom).left)
      (Set.range (ι ≫ (End.of d ^ t.val).asHom).left))
    (k : ℕ) (c : s2e_supportedClass W (s2e_componentCycle ι ℚ) k)
    (H : AlgebraicTopology.Singular.Cohomology ℚ (TopCat.of (ComplexPoint Q)) 2)
    (hsigned : s2e_normalEuler ι k c = (-1 : ℚ) ^ k •
      s2e_hyperplanePower (TopCat.of (ComplexPoint Q)) H k)
    (htop : s2e_hyperplanePower (TopCat.of (ComplexPoint Q)) H k ≠ 0) :
    ∀ ζ : ℂ, IsPrimitiveRoot ζ m →
      s2e_weightedSum m (fun t : ZMod m => ζ ^ t.val)
        (fun t : Fin m => TensorProduct.tmul ℚ (1 : ℂ)
          (s2e_pullback ℚ ((End.of d ^ (m - t.val)).asHom) (2 * k)
            (s2e_classToAbsolute W (s2e_componentCycle ι ℚ) k c))) ≠ 0 := by
  intro ζ _
  have hn : s2e_normalEuler ι k c ≠ 0 := by
    rw [hsigned]
    exact smul_ne_zero (pow_ne_zero k (by norm_num)) htop
  exact complex_inverse_orbit_ne_zero ι d m hm hperiod hdis _ (by
    rw [ZMod.val_zero, pow_zero]) k c hn

#print axioms signed_normal_weighted_nonzero
end HodgeLean.Foundations.Program.G32Native
