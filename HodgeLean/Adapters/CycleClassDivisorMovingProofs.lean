import HodgeLean.Adapters.CycleClassDivisorIntersection

/-! # Proof obligations for divisor moving primitives
HC no distance; AV milestone no distance.
-/

noncomputable section
open CategoryTheory AlgebraicGeometry
open scoped BigOperators
namespace HodgeLean.Adapters

/-- Projectivity over the complex field supplies the finiteness needed for intersection cycles.
Source: Hartshorne, Algebraic Geometry, II.3, finite type over a Noetherian base;
Mathlib LocallyOfFiniteType.isLocallyNoetherian and quasiCompact_iff_compactSpace. -/
theorem ccm12_isNoetherian_aux (X : Over (Spec ↧ℂ)) [IsProjective X.hom] :
    IsNoetherian X.left := by
  let hlocal : IsLocallyNoetherian X.left :=
    LocallyOfFiniteType.isLocallyNoetherian X.hom
  let hcompact : CompactSpace X.left :=
    (quasiCompact_iff_compactSpace X.hom).mp inferInstance
  exact
    { toIsLocallyNoetherian := hlocal
      toCompactSpace := hcompact }

/-- A single nonzero linear polynomial avoids all the specified ideals.
The ideals need not be maximal or prime; each must miss a homogeneous coordinate.
Source: Hartshorne, Algebraic Geometry, II.7, hyperplane sections;
Mathlib Submodule.exists_forall_notMem_of_forall_ne_top, finite subspace avoidance. -/
theorem ccm12_linearPolynomial_avoids_aux (K : Type*) [Field K] [Infinite K]
    (n : ℕ) (s : Finset (Ideal (MvPolynomial (Fin (n + 1)) K)))
    (hs : ∀ P ∈ s, ∃ j : Fin (n + 1), MvPolynomial.X j ∉ P) :
    ∃ a : Fin (n + 1) → K, a ≠ 0 ∧
      ∀ P ∈ s, (∑ j, MvPolynomial.C (a j) * MvPolynomial.X j) ∉ P := by
  classical
  let L : (Fin (n + 1) → K) →ₗ[K] MvPolynomial (Fin (n + 1)) K :=
    { toFun := fun a => ∑ j, MvPolynomial.C (a j) * MvPolynomial.X j
      map_add' := by
        intro a b
        simp only [Pi.add_apply, map_add, add_mul, Finset.sum_add_distrib]
      map_smul' := by
        intro r a
        simp [Algebra.smul_def, Finset.mul_sum, mul_assoc] }
  have L_single (j : Fin (n + 1)) : L (Pi.single j 1) = MvPolynomial.X j := by
    simp only [L, LinearMap.coe_mk, AddHom.coe_mk]
    rw [Fintype.sum_eq_single j]
    · simp
    · intro i hi
      rw [Pi.single_eq_of_ne hi]
      simp
  let p : Option {P // P ∈ s} → Submodule K (Fin (n + 1) → K)
    | none => ⊥
    | some P => P.1.restrictScalars K |>.comap L
  have hp : ∀ i, p i ≠ ⊤ := by
    intro i
    cases i with
    | none =>
        intro h
        have hmem : (Pi.single (0 : Fin (n + 1)) 1 : Fin (n + 1) → K) ∈ p none :=
          h.symm ▸ Submodule.mem_top
        simpa [p] using hmem
    | some P =>
        obtain ⟨j, hj⟩ := hs P.1 P.2
        intro h
        have hmem : (Pi.single j 1 : Fin (n + 1) → K) ∈ p (some P) :=
          h.symm ▸ Submodule.mem_top
        change L (Pi.single j 1) ∈ P.1 at hmem
        rw [L_single j] at hmem
        exact hj hmem
  obtain ⟨a, ha⟩ := Submodule.exists_forall_notMem_of_forall_ne_top p hp
  refine ⟨a, ?_, ?_⟩
  · intro ha0
    exact ha none (by simp [p, ha0])
  · intro P hP hmem
    exact ha (some ⟨P, hP⟩) (by simpa [p, L] using hmem)

end HodgeLean.Adapters
