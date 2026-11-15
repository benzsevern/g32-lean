import HodgeLean.Adapters.CycleClassDivisorMovingProofs

/-! # Divisor moving: frozen first primitives

These are implications from projectivity and from finite coordinate-avoidance
conditions. They supply Noetherianity and simultaneous polynomial avoidance.
Very ample decomposition, the passage to ideal sheaves, expected codimension,
and the supported cup comparison remain separate obligations.
HC no distance; AV milestone no distance.
-/

noncomputable section
open CategoryTheory AlgebraicGeometry
open scoped BigOperators
namespace HodgeLean.Adapters

/-- Projectivity over the complex field supplies the finiteness needed for intersection cycles.
Source: Hartshorne, Algebraic Geometry, II.3, finite type over a Noetherian base;
Mathlib LocallyOfFiniteType.isLocallyNoetherian and quasiCompact_iff_compactSpace. -/
theorem ccm12_isNoetherian (X : Over (Spec ↧ℂ)) [IsProjective X.hom] :
    IsNoetherian X.left :=
  ccm12_isNoetherian_aux X

/-- A single nonzero linear polynomial avoids all the specified ideals.
The ideals need not be maximal or prime; each must miss a homogeneous coordinate.
Source: Hartshorne, Algebraic Geometry, II.7, hyperplane sections;
Mathlib Submodule.exists_forall_notMem_of_forall_ne_top, finite subspace avoidance. -/
theorem ccm12_linearPolynomial_avoids (K : Type*) [Field K] [Infinite K]
    (n : ℕ) (s : Finset (Ideal (MvPolynomial (Fin (n + 1)) K)))
    (hs : ∀ P ∈ s, ∃ j : Fin (n + 1), MvPolynomial.X j ∉ P) :
    ∃ a : Fin (n + 1) → K, a ≠ 0 ∧
      ∀ P ∈ s, (∑ j, MvPolynomial.C (a j) * MvPolynomial.X j) ∉ P :=
  ccm12_linearPolynomial_avoids_aux K n s hs

open HodgeLean.Foundations HodgeLean.Foundations.Curves

/-- W1: the constructed projective cubic instantiates the geometric premise.
Source: the projective presentation of E. -/
example : IsNoetherian E.left := ccm12_isNoetherian E

/-- W1b: the new finiteness result makes the existing intersection cycle available on E.
Source: ccm11_intersectionCycle and the projective presentation of E. -/
example : AlgebraicCycle E.left ℚ := by
  letI := ccm12_isNoetherian E
  exact ccm11_intersectionCycle E.left ⊥ ⊥

/-- W2: avoidance at the two distinct coordinate points of the projective line.
Source: evaluation kernels at the two coordinate vectors. -/
example : ∃ a : Fin 2 → ℂ, a ≠ 0 ∧
    ∀ P ∈ ({RingHom.ker (MvPolynomial.eval₂Hom (RingHom.id ℂ)
        (fun j : Fin 2 => if j = 0 then 1 else 0)),
      RingHom.ker (MvPolynomial.eval₂Hom (RingHom.id ℂ)
        (fun j : Fin 2 => if j = 1 then 1 else 0))} :
          Finset (Ideal (MvPolynomial (Fin 2) ℂ))),
      (∑ j, MvPolynomial.C (a j) * MvPolynomial.X j) ∉ P := by
  classical
  apply ccm12_linearPolynomial_avoids ℂ 1
  intro P hP
  simp only [Finset.mem_insert, Finset.mem_singleton] at hP
  rcases hP with rfl | rfl
  · refine ⟨0, ?_⟩
    simp
  · refine ⟨1, ?_⟩
    simp

/-- W2b: even the empty avoidance list produces a nonzero coefficient vector.
Source: finite subspace avoidance with the zero subspace included. -/
example : ∃ a : Fin 1 → ℂ, a ≠ 0 ∧
    ∀ P ∈ (∅ : Finset (Ideal (MvPolynomial (Fin 1) ℂ))),
      (∑ j, MvPolynomial.C (a j) * MvPolynomial.X j) ∉ P := by
  apply ccm12_linearPolynomial_avoids ℂ 0
  simp

end HodgeLean.Adapters
