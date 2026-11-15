import HodgeLean.Foundations.Program.G32Native.OrbitRestriction
import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic

/-! # Complex character sums detected on the selected component -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
open CategoryTheory AlgebraicGeometry AlgebraicTopology.Singular
open HodgeLean.Adapters HodgeLean.Foundations.Program
open scoped BigOperators
namespace HodgeLean.Foundations.Program.G32Native
open HodgeLean.Foundations.Program.G32Native.TowerOrbit

/-- Complex scalar extension retains the same zeroth component restriction. -/
theorem complex_inverse_orbit_restrict
    {Q W : Over (Spec ↧ℂ)} [IsIntegral Q.left]
    (ι : Q ⟶ W) [IsClosedImmersion ι.left] (d : W ⟶ W)
    (m : ℕ) (hm : 0 < m) (hperiod : End.of d ^ m = 1)
    (hdis : ∀ s t : Fin m, s ≠ t → Disjoint
      (Set.range (ι ≫ (End.of d ^ s.val).asHom).left)
      (Set.range (ι ≫ (End.of d ^ t.val).asHom).left))
    (χ : ZMod m → ℂ) (hχ : χ 0 = 1) (k : ℕ)
    (c : s2e_supportedClass W (s2e_componentCycle ι ℚ) k) :
    (s2e_pullback ℚ ι (2 * k)).baseChange ℂ
      (s2e_weightedSum m χ (fun t : Fin m => TensorProduct.tmul ℚ (1 : ℂ)
        (s2e_pullback ℚ (End.of d ^ (m - t.val)).asHom (2 * k)
          (s2e_classToAbsolute W (s2e_componentCycle ι ℚ) k c)))) =
      TensorProduct.tmul ℚ (1 : ℂ) (s2e_normalEuler ι k c) := by
  classical
  unfold s2e_weightedSum
  rw [map_sum, Finset.sum_eq_single (⟨0, hm⟩ : Fin m)]
  · rw [map_smul, LinearMap.baseChange_tmul]
    simp only [Nat.cast_zero, neg_zero, hχ, one_smul, Nat.sub_zero,
      hperiod, End.one_asHom]
    change TensorProduct.tmul ℚ (1 : ℂ) (s2e_pullback ℚ ι (2 * k)
      (cohomologyMap ℚ (2 * k) (𝟙 _) _)) = _
    rw [cohomologyMap_id, LinearMap.id_apply]
    rfl
  · intro t _ ht
    rw [map_smul, LinearMap.baseChange_tmul,
      inverse_translate_restrict_eq_zero ι d m hm hdis t ht,
      TensorProduct.tmul_zero, smul_zero]
  · intro ht
    exact (ht (Finset.mem_univ _)).elim

#print axioms complex_inverse_orbit_restrict
/-- A nonzero normal restriction detects every character sum normalized at zero. -/
theorem complex_inverse_orbit_ne_zero
    {Q W : Over (Spec ↧ℂ)} [IsIntegral Q.left]
    (ι : Q ⟶ W) [IsClosedImmersion ι.left] (d : W ⟶ W)
    (m : ℕ) (hm : 0 < m) (hperiod : End.of d ^ m = 1)
    (hdis : ∀ s t : Fin m, s ≠ t → Disjoint
      (Set.range (ι ≫ (End.of d ^ s.val).asHom).left)
      (Set.range (ι ≫ (End.of d ^ t.val).asHom).left))
    (χ : ZMod m → ℂ) (hχ : χ 0 = 1) (k : ℕ)
    (c : s2e_supportedClass W (s2e_componentCycle ι ℚ) k)
    (hc : s2e_normalEuler ι k c ≠ 0) :
    s2e_weightedSum m χ (fun t : Fin m => TensorProduct.tmul ℚ (1 : ℂ)
      (s2e_pullback ℚ (End.of d ^ (m - t.val)).asHom (2 * k)
        (s2e_classToAbsolute W (s2e_componentCycle ι ℚ) k c))) ≠ 0 := by
  intro hz
  have he := complex_inverse_orbit_restrict ι d m hm hperiod hdis χ hχ k c
  rw [hz, map_zero] at he
  exact hc ((Module.FaithfullyFlat.one_tmul_eq_zero_iff ℚ _ (A := ℂ) _).mp he.symm)

#print axioms complex_inverse_orbit_ne_zero
end HodgeLean.Foundations.Program.G32Native
