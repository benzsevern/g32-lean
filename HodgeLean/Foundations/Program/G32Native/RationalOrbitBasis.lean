import HodgeLean.Foundations.Program.G32Native.RationalKernelBasis
import HodgeLean.Foundations.Program.G32Native.InverseFourier

/-! # Rational bases of the specified inverse orbit -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
open scoped TensorProduct BigOperators
open HodgeLean.Foundations.Program
namespace HodgeLean.Foundations.Program.G32Native.TowerOrbit

/-- The rank bound and nonzero primitive orbit projections give an exhaustive rational orbit basis. -/
theorem rational_inverse_orbit_basis
    {V : Type*} [AddCommGroup V] [Module ℚ V] [Module.Finite ℚ V]
    (T : Module.End ℚ V) (m : ℕ) (hm : 1 < m) (hT : T ^ m = 1) (seed : V)
    (hbound : Module.finrank ℚ (LinearMap.ker
      (Polynomial.aeval T (Polynomial.cyclotomic m ℚ))) ≤ Nat.totient m)
    (hne : ∀ ζ : ℂ, IsPrimitiveRoot ζ m →
      primitiveOrbit (T.baseChange ℂ) m (fun t : ZMod m => ζ ^ t.val)
        (TensorProduct.tmul ℚ (1 : ℂ) seed) ≠ 0) :
    ∃ (a : Fin (Nat.totient m) → Fin m → ℚ) (v : Fin (Nat.totient m) → V),
      LinearIndependent ℚ v ∧
      Submodule.span ℚ (Set.range v) = LinearMap.ker
        (Polynomial.aeval T (Polynomial.cyclotomic m ℚ)) ∧
      (∀ j, v j = ∑ t : Fin m, a j t • (T ^ (m - t.val)) seed) ∧
      ∀ ζ : ℂ, IsPrimitiveRoot ζ m →
        (∃ u : ℂ ⊗[ℚ] V, u ≠ 0 ∧ T.baseChange ℂ u = ζ • u) ∧
        (∀ u : ℂ ⊗[ℚ] V, T.baseChange ℂ u = ζ • u →
          ∃ b : Fin (Nat.totient m) → ℂ,
            u = ∑ j, b j • TensorProduct.tmul ℚ (1 : ℂ) (v j)) := by
  classical
  have hm0 : 0 < m := by omega
  let R := Submodule.span ℚ (Set.range (fun t : Fin m => (T ^ (m - t.val)) seed))
  let w : {ζ : ℂ // ζ ∈ primitiveRoots m ℂ} → ℂ ⊗[ℚ] V := fun ζ =>
    primitiveOrbit (T.baseChange ℂ) m (fun t : ZMod m => ζ.val⁻¹ ^ t.val)
      (TensorProduct.tmul ℚ (1 : ℂ) seed)
  have hTc : (T.baseChange ℂ) ^ m = 1 := by
    rw [← LinearMap.baseChange_pow, hT, Module.End.one_eq_id, LinearMap.baseChange_id]
    rfl
  have hw (ζ : {ζ : ℂ // ζ ∈ primitiveRoots m ℂ}) :
      T.baseChange ℂ (w ζ) = ζ.val • w ζ := by
    have he := primitiveOrbit_eigen (T.baseChange ℂ) m hm hTc ζ.val⁻¹
      (((mem_primitiveRoots hm0).mp ζ.property).inv) (TensorProduct.tmul ℚ (1 : ℂ) seed)
    simpa only [inv_inv] using he
  have hnw (ζ : {ζ : ℂ // ζ ∈ primitiveRoots m ℂ}) : w ζ ≠ 0 :=
    hne ζ.val⁻¹ (((mem_primitiveRoots hm0).mp ζ.property).inv)
  have hmem (ζ : {ζ : ℂ // ζ ∈ primitiveRoots m ℂ}) : w ζ ∈ R.baseChange ℂ := by
    unfold w primitiveOrbit s2e_weightedSum
    apply Submodule.sum_mem
    intro t _
    apply Submodule.smul_mem
    change ((T.baseChange ℂ) ^ (m - t.val)) (TensorProduct.tmul ℚ (1 : ℂ) seed) ∈ R.baseChange ℂ
    rw [← LinearMap.baseChange_pow, LinearMap.baseChange_tmul]
    exact Submodule.tmul_mem_baseChange_of_mem _ (Submodule.subset_span ⟨t, rfl⟩)
  obtain ⟨hrank, hspan⟩ := cyclotomic_kernel_rank_and_span T m hm0 R hbound w hw hnw hmem
  obtain ⟨a, v, hlin, hvspan, hav, heig⟩ := rational_kernel_basis T m hm0
    (fun t : Fin m => (T ^ (m - t.val)) seed) hrank hspan
  refine ⟨a, v, hlin, hvspan, hav, ?_⟩
  intro ζ hζ
  let z : {ζ : ℂ // ζ ∈ primitiveRoots m ℂ} := ⟨ζ, (mem_primitiveRoots hm0).mpr hζ⟩
  exact ⟨⟨w z, hnw z, hw z⟩, heig ζ hζ⟩

#print axioms rational_inverse_orbit_basis
end HodgeLean.Foundations.Program.G32Native.TowerOrbit
