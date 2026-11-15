import HodgeLean.Foundations.Program.G32Native.RationalOrbitBasis

/-! # Inverse orbit coefficients through the retained retraction -/
noncomputable section
set_option maxHeartbeats 200000
open scoped TensorProduct BigOperators
namespace HodgeLean.Foundations.Program.G32Native
open HodgeLean.Foundations.Program.G32Native.TowerOrbit

/-- Intertwining preserves each specified inverse-power character combination. -/
theorem map_primitiveOrbit
    {K V W : Type*} [CommRing K] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W]
    (A : Module.End K V) (B : Module.End K W) (G : V →ₗ[K] W)
    (hG : G.comp A = B.comp G) (m : ℕ) (χ : ZMod m → K) (x : V) :
    G (primitiveOrbit A m χ x) = primitiveOrbit B m χ (G x) := by
  have hpoint (v : V) : G (A v) = B (G v) := LinearMap.congr_fun hG v
  have hp (n : ℕ) (v : V) : G ((A ^ n) v) = (B ^ n) (G v) := by
    induction n with
    | zero => rfl
    | succ n ih =>
      rw [pow_succ', Module.End.mul_apply, hpoint, ih,
        pow_succ', Module.End.mul_apply]
  unfold primitiveOrbit HodgeLean.Foundations.Program.s2e_weightedSum
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro t _
  rw [map_smul, hp]

/-- The rational coefficients retain the same final seed and actual retraction.
The descent premise is the nonzero-preimage output of I2 for the weighted class. -/
theorem tower_inverse_orbit_basis
    {V₀ Vr : Type*} [AddCommGroup V₀] [Module ℚ V₀] [Module.Finite ℚ V₀]
    [AddCommGroup Vr] [Module ℚ Vr]
    (T₀ : Module.End ℚ V₀) (Tr : Module.End ℚ Vr)
    (F : V₀ →ₗ[ℚ] Vr) (G : Vr →ₗ[ℚ] V₀)
    (hGF : G.comp F = LinearMap.id) (hG : G.comp Tr = T₀.comp G)
    (m : ℕ) (hm : 1 < m) (hT₀ : T₀ ^ m = 1) (seed : Vr)
    (hbound : Module.finrank ℚ (LinearMap.ker
      (Polynomial.aeval T₀ (Polynomial.cyclotomic m ℚ))) ≤ Nat.totient m)
    (hdescent : ∀ ζ : ℂ, IsPrimitiveRoot ζ m →
      ∃ u : ℂ ⊗[ℚ] V₀, u ≠ 0 ∧ F.baseChange ℂ u =
        primitiveOrbit (Tr.baseChange ℂ) m (fun t : ZMod m => ζ ^ t.val)
          (TensorProduct.tmul ℚ (1 : ℂ) seed)) :
    ∃ (a : Fin (Nat.totient m) → Fin m → ℚ) (v : Fin (Nat.totient m) → V₀),
      LinearIndependent ℚ v ∧
      Submodule.span ℚ (Set.range v) = LinearMap.ker
        (Polynomial.aeval T₀ (Polynomial.cyclotomic m ℚ)) ∧
      (∀ j, v j = G (∑ t : Fin m, a j t • (Tr ^ (m - t.val)) seed)) ∧
      ∀ ζ : ℂ, IsPrimitiveRoot ζ m →
        (∃ u : ℂ ⊗[ℚ] V₀, u ≠ 0 ∧ T₀.baseChange ℂ u = ζ • u) ∧
        (∀ u : ℂ ⊗[ℚ] V₀, T₀.baseChange ℂ u = ζ • u →
          ∃ b : Fin (Nat.totient m) → ℂ,
            u = ∑ j, b j • TensorProduct.tmul ℚ (1 : ℂ) (v j)) := by
  have hGc : (G.baseChange ℂ).comp (Tr.baseChange ℂ) =
      (T₀.baseChange ℂ).comp (G.baseChange ℂ) := by
    simpa only [LinearMap.baseChange_comp] using congrArg (LinearMap.baseChange ℂ) hG
  have hGFc : (G.baseChange ℂ).comp (F.baseChange ℂ) = LinearMap.id := by
    simpa only [LinearMap.baseChange_comp, LinearMap.baseChange_id] using
      congrArg (LinearMap.baseChange ℂ) hGF
  have hne (ζ : ℂ) (hζ : IsPrimitiveRoot ζ m) :
      primitiveOrbit (T₀.baseChange ℂ) m (fun t : ZMod m => ζ ^ t.val)
        (TensorProduct.tmul ℚ (1 : ℂ) (G seed)) ≠ 0 := by
    obtain ⟨u, hu, he⟩ := hdescent ζ hζ
    have heq : primitiveOrbit (T₀.baseChange ℂ) m (fun t : ZMod m => ζ ^ t.val)
        (TensorProduct.tmul ℚ (1 : ℂ) (G seed)) = u := by
      rw [← LinearMap.baseChange_tmul, ← map_primitiveOrbit _ _ _ hGc, ← he,
        ← LinearMap.comp_apply, hGFc, LinearMap.id_apply]
    exact heq ▸ hu
  obtain ⟨a, v, hi, hs, hv, he⟩ :=
    rational_inverse_orbit_basis T₀ m hm hT₀ (G seed) hbound hne
  refine ⟨a, v, hi, hs, ?_, he⟩
  intro j
  rw [hv j, map_sum]
  apply Finset.sum_congr rfl
  intro t _
  rw [map_smul]
  have hpoint (v : Vr) : G (Tr v) = T₀ (G v) := LinearMap.congr_fun hG v
  have hp (n : ℕ) : G ((Tr ^ n) seed) = (T₀ ^ n) (G seed) := by
    induction n with
    | zero => rfl
    | succ n ih =>
      rw [pow_succ', Module.End.mul_apply, hpoint, ih,
        pow_succ', Module.End.mul_apply]
  rw [hp]

#print axioms map_primitiveOrbit
#print axioms tower_inverse_orbit_basis
end HodgeLean.Foundations.Program.G32Native
