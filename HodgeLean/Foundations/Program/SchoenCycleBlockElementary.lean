import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs

/-! # Elementary coefficient polynomials on stable coordinate blocks -/
noncomputable section
open MvPolynomial
namespace HodgeLean.Foundations.Program

/-- An elementary coefficient polynomial in a stable block of variables is
invariant under every permutation preserving that block.
Source: Mathlib, MvPolynomial.rename_esymm. -/
theorem s2e_block_elementary_rename
    {ι : Type*} [Fintype ι] (R : Type*) [CommRing R]
    (S : Finset ι) (σ : Equiv.Perm ι) (hσ : ∀ i, i ∈ S ↔ σ i ∈ S) (j : ℕ) :
    rename σ (rename (fun i : S => (i : ι)) (esymm S R j)) =
      rename (fun i : S => (i : ι)) (esymm S R j) := by
  classical
  let e : S ≃ S := σ.subtypeEquiv hσ
  have he : (σ : ι → ι) ∘ (fun i : S => (i : ι)) =
      (fun i : S => (i : ι)) ∘ e := rfl
  rw [rename_rename, he, ← rename_rename,
    rename_esymm (σ := ↥S) (τ := ↥S) (R := R) j e]

end HodgeLean.Foundations.Program
