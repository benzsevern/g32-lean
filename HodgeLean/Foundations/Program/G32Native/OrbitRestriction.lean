import HodgeLean.Foundations.Program.G32Native.Restriction
import HodgeLean.Foundations.Program.SchoenCycleFiniteQuotientCohomology

/-! # Inverse orbit restriction on the selected component -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
open CategoryTheory AlgebraicGeometry AlgebraicTopology.Singular
open HodgeLean.Adapters HodgeLean.Foundations.Program
open scoped BigOperators
namespace HodgeLean.Foundations.Program.G32Native
open HodgeLean.Foundations.Program.G32Native.TowerOrbit

/-- Every nonidentity inverse translate restricts to zero on the selected component. -/
theorem inverse_translate_restrict_eq_zero
    {Q W : Over (Spec ↧ℂ)} [IsIntegral Q.left]
    (ι : Q ⟶ W) [IsClosedImmersion ι.left] (d : W ⟶ W)
    (m : ℕ) (hm : 0 < m)
    (hdis : ∀ s t : Fin m, s ≠ t → Disjoint
      (Set.range (ι ≫ (End.of d ^ s.val).asHom).left)
      (Set.range (ι ≫ (End.of d ^ t.val).asHom).left))
    (t : Fin m) (ht : t ≠ ⟨0, hm⟩) (k : ℕ)
    (c : s2e_supportedClass W (s2e_componentCycle ι ℚ) k) :
    s2e_pullback ℚ ι (2 * k)
      (s2e_pullback ℚ (End.of d ^ (m - t.val)).asHom (2 * k)
        (s2e_classToAbsolute W (s2e_componentCycle ι ℚ) k c)) = 0 := by
  have htpos : 0 < t.val := by
    have hn : t.val ≠ 0 := fun h => ht (Fin.ext h)
    omega
  have hlt : m - t.val < m := by omega
  have hn : (⟨m - t.val, hlt⟩ : Fin m) ≠ ⟨0, hm⟩ := by
    intro he
    have hv := congrArg Fin.val he
    simp only at hv
    omega
  have hd := hdis ⟨m - t.val, hlt⟩ ⟨0, hm⟩ hn
  simp only [pow_zero, End.one_asHom, Category.comp_id] at hd
  rw [← LinearMap.comp_apply, ← s2e_quotient_pullback_comp]
  exact component_class_restrict_eq_zero ι (ι ≫ (End.of d ^ (m - t.val)).asHom) hd k c

#print axioms inverse_translate_restrict_eq_zero
/-- Restriction of an inverse orbit sum retains exactly its zeroth coefficient. -/
theorem inverse_orbit_restrict
    {Q W : Over (Spec ↧ℂ)} [IsIntegral Q.left]
    (ι : Q ⟶ W) [IsClosedImmersion ι.left] (d : W ⟶ W)
    (m : ℕ) (hm : 0 < m) (hperiod : End.of d ^ m = 1)
    (hdis : ∀ s t : Fin m, s ≠ t → Disjoint
      (Set.range (ι ≫ (End.of d ^ s.val).asHom).left)
      (Set.range (ι ≫ (End.of d ^ t.val).asHom).left))
    (a : Fin m → ℚ) (k : ℕ)
    (c : s2e_supportedClass W (s2e_componentCycle ι ℚ) k) :
    s2e_pullback ℚ ι (2 * k)
      (∑ t : Fin m, a t • s2e_pullback ℚ (End.of d ^ (m - t.val)).asHom (2 * k)
        (s2e_classToAbsolute W (s2e_componentCycle ι ℚ) k c)) =
      a ⟨0, hm⟩ • s2e_normalEuler ι k c := by
  classical
  rw [map_sum, Finset.sum_eq_single (⟨0, hm⟩ : Fin m)]
  · rw [map_smul]
    simp only [Nat.sub_zero, hperiod, End.one_asHom]
    change a ⟨0, hm⟩ • s2e_pullback ℚ ι (2 * k)
      (cohomologyMap ℚ (2 * k) (𝟙 _) _) = _
    rw [cohomologyMap_id, LinearMap.id_apply]
    rfl
  · intro t _ ht
    rw [map_smul, inverse_translate_restrict_eq_zero ι d m hm hdis t ht, smul_zero]
  · intro ht
    exact (ht (Finset.mem_univ _)).elim

#print axioms inverse_orbit_restrict
end HodgeLean.Foundations.Program.G32Native
