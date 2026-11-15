import HodgeLean.Adapters.LatticeClassHQProofs

/-! # The lattice class in `HQ X 2`: frozen specification

Scope: for a smooth projective integral complex group `X` with S12 period lattice
`Λ = abelianPeriodLattice X`, the class `latticeClassHQ X E ∈ HQ X 2` of an integral form `E` on
`Λ` (`LatticeClassHQDefs`), built only from the stage-7 `latticeClass`, the inverse of the proved
period equivalence `spec_abelianPeriod_equiv` and `(cupProductOf X).cupWedgeMap 2`. Claimed: the
class is additive in `E` and injective on alternating forms; for `E = Im H` with `H` positive
definite its top cup power is nonzero, and Hard Lefschetz holds for it, as an implication from the
top-power statement through `hardLefschetz_abelian_of_cupPow`; the zero form gives the zero class,
for which Hard Lefschetz fails in positive dimension.

Not claimed: that `latticeClassHQ X E` is the Chern class or cycle class of a line bundle, or of
any algebraic cycle (`LefschetzOneOneHyp`, GAGA); that it lies in `cohomologyHodgePiece X 2 (1,1)`
(which needs the Betti–de Rham comparison); or that every class of `HQ X 2` is of this form with
`E` integral. No statement assumes `HodgeDecomposition`, `BettiDeRhamIso` or a finiteness
hypothesis beyond the geometric scope of `abelianTorusComparison`.
HC no distance; AV milestone no distance.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open HodgeLean.RealDefs HodgeLean.Foundations HodgeLean.Foundations.AppellHumbert

namespace HodgeLean.Adapters

variable (X : Over (Spec ↧ℂ)) [GrpObj X] [IsIntegral X.left]
  [Smooth X.hom] [IsProjective X.hom]

/-- The class in `HQ X 2` is additive in the integral form: `latticeClass` is additive
(`spec_latticeClass_add`) and both transport maps are linear.
Source: Bourbaki, *Algèbre*, ch. III, §11; `spec_latticeClass_add`. -/
theorem spec_latticeClassHQ_add
    (E₁ E₂ : abelianPeriodLattice X →+ abelianPeriodLattice X →+ ℤ) :
    latticeClassHQ X (E₁ + E₂) = latticeClassHQ X E₁ + latticeClassHQ X E₂ :=
  spec_latticeClassHQ_add_aux X E₁ E₂

example (E : abelianPeriodLattice X →+ abelianPeriodLattice X →+ ℤ) :
    latticeClassHQ X (E + E) = latticeClassHQ X E + latticeClassHQ X E :=
  spec_latticeClassHQ_add X E E

/-- On alternating integral forms the class in `HQ X 2` is injective: `latticeClass` is
(`spec_latticeClass_injective`), the exterior square of a linear equivalence is injective, and
`cupWedgeMap 2` is bijective for abelian `X` (`torusCohomology_cupProductOf`).
Source: Birkenhake–Lange, *Complex Abelian Varieties*, 2nd ed., Lemma 1.3.1;
`spec_latticeClass_injective`, `torusCohomology_cupProductOf`. -/
theorem spec_latticeClassHQ_injective
    (E₁ E₂ : abelianPeriodLattice X →+ abelianPeriodLattice X →+ ℤ)
    (h₁ : ∀ x, E₁ x x = 0) (h₂ : ∀ x, E₂ x x = 0)
    (h : latticeClassHQ X E₁ = latticeClassHQ X E₂) : E₁ = E₂ :=
  spec_latticeClassHQ_injective_aux X E₁ E₂ h₁ h₂ h

example (E : abelianPeriodLattice X →+ abelianPeriodLattice X →+ ℤ) (hE : ∀ x, E x x = 0)
    (h : latticeClassHQ X E = 0) : E = 0 :=
  spec_latticeClassHQ_injective X E 0 hE (fun _ => rfl) (by
    rw [h]; simp [latticeClassHQ, latticeClass])

/-- If `E = Im H` on the period lattice for a positive-definite Hermitian form `H` on `ℂ^g`,
`g = dim X.left`, the `g`-th cup power of the class is nonzero. Under `cupWedgeMap` the cup power
is the `g`-th wedge power, and that of `latticeClass E` is nonzero because `E` is nondegenerate on
`Λ ⊗ ℝ = ℂ^g` (as in `spec_latticeClass_wedgePow_ne_zero`).
Source: Birkenhake–Lange, *Complex Abelian Varieties*, 2nd ed., §4.1 and Lemma 1.3.1;
`spec_positive_imaginary_nondegenerate`, `Symplectic.wedgePow_ne_zero_of_isNondegenerate`,
`cupWedgeEquiv_wedgePow`. -/
theorem spec_latticeClassHQ_cupPow_ne_zero
    (H : HermitianForm (V := Fin (dim X.left) → ℂ)) (hH : H.IsPositiveDefinite)
    (E : abelianPeriodLattice X →+ abelianPeriodLattice X →+ ℤ)
    (hE : ∀ l m : abelianPeriodLattice X, (E l m : ℝ) = H.imaginary l m) :
    cupPow X (cupProductOf X) (latticeClassHQ X E) (dim X.left) ≠ 0 :=
  spec_latticeClassHQ_cupPow_ne_zero_aux X H hH E hE

example (H : HermitianForm (V := Fin (dim X.left) → ℂ)) (hH : H.IsPositiveDefinite)
    (E : abelianPeriodLattice X →+ abelianPeriodLattice X →+ ℤ)
    (hE : ∀ l m : abelianPeriodLattice X, (E l m : ℝ) = H.imaginary l m)
    (hg : 0 < dim X.left) : latticeClassHQ X E ≠ 0 := fun h0 =>
  spec_latticeClassHQ_cupPow_ne_zero X H hH E hE (by
    rw [h0]; exact cupPow_zero_of_pos X (cupProductOf X) hg)

/-- Hard Lefschetz for the class of a Riemann form: if `E = Im H` on the period lattice for a
positive-definite `H`, Hard Lefschetz holds for `latticeClassHQ X E`. This is an implication from
`spec_latticeClassHQ_cupPow_ne_zero` through `hardLefschetz_abelian_of_cupPow`; it does not say the
class is algebraic or a Chern class.
Source: Huybrechts, *Complex Geometry*, §1.2 (Lefschetz for a symplectic 2-vector);
`hardLefschetz_abelian_of_cupPow`, `spec_latticeClassHQ_cupPow_ne_zero`. -/
theorem spec_latticeClassHQ_hardLefschetz
    (H : HermitianForm (V := Fin (dim X.left) → ℂ)) (hH : H.IsPositiveDefinite)
    (E : abelianPeriodLattice X →+ abelianPeriodLattice X →+ ℤ)
    (hE : ∀ l m : abelianPeriodLattice X, (E l m : ℝ) = H.imaginary l m) :
    HardLefschetz X (cupProductOf X) (latticeClassHQ X E) :=
  spec_latticeClassHQ_hardLefschetz_aux X H hH E hE

example (H : HermitianForm (V := Fin (dim X.left) → ℂ)) (hH : H.IsPositiveDefinite)
    (E : abelianPeriodLattice X →+ abelianPeriodLattice X →+ ℤ)
    (hE : ∀ l m : abelianPeriodLattice X, (E l m : ℝ) = H.imaginary l m) :
    Function.Bijective (lefschetzPow X (cupProductOf X) (latticeClassHQ X E) (dim X.left - 0)
      (by omega : 0 + 2 * (dim X.left - 0) = 2 * dim X.left)) :=
  (spec_latticeClassHQ_hardLefschetz X H hH E hE).bijective (Nat.zero_le _) _

/-- Falsification: the zero form gives the zero class, and in positive dimension Hard Lefschetz
fails for it (`L^g = 0 : H^0 → H^{2g}` while `H^0 ≠ 0`). So the positivity premise of
`spec_latticeClassHQ_hardLefschetz` cannot be dropped, and a transport that sent every form to a
fixed polarization would fail here.
Source: Birkenhake–Lange, *Complex Abelian Varieties*, 2nd ed., Theorem 2.2.3; `HardLefschetz`
(non-degeneracy note), `cupPow_zero_of_pos`, `CupProduct.unitClass_ne_zero`. -/
theorem spec_latticeClassHQ_zero_falsification (hg : 0 < dim X.left) :
    latticeClassHQ X 0 = 0 ∧ ¬ HardLefschetz X (cupProductOf X) (latticeClassHQ X 0) :=
  spec_latticeClassHQ_zero_falsification_aux X hg

example (hg : 0 < dim X.left) : ¬ HardLefschetz X (cupProductOf X) 0 := by
  obtain ⟨h0, hn⟩ := spec_latticeClassHQ_zero_falsification X hg
  rwa [h0] at hn

end HodgeLean.Adapters
