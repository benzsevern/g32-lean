import HodgeLean.Foundations.Symplectic
import HodgeLean.Blocks.Milestone.AbelianVariety

/-! # Adapter: the top polarization power from nondegeneracy

Instantiates Foundations target T1 (`HodgeLean.Foundations.Symplectic`) for the Blocks hypothesis
`HodgeBlocks.PolarizationTopPowerNonzero`: over `ℚ`, Blocks' `polarizationPow` is
`Symplectic.wedgePow`, and `S.rank_eq : finrank ℚ V = 2 * S.g` supplies the dimension.

Relation to the goal: HC no distance; AV milestone no distance; `PolarizationTopPowerNonzero` is
replaced by nondegeneracy of the polarization.
-/

open Module

namespace HodgeLean.Adapters

open HodgeLean.Foundations.Symplectic HodgeBlocks

variable {V : Type*} [AddCommGroup V] [Module ℚ V] [Module.Finite ℚ V]

omit [Module.Finite ℚ V] in
/-- Blocks' `polarizationPow` is the Foundations `wedgePow` over `ℚ`. -/
theorem polarizationPow_eq_wedgePow (ω : ⋀[ℚ]^2 V) (g : ℕ) :
    polarizationPow ω g = wedgePow ω g := by
  induction g with
  | zero => rfl
  | succ g ih => rw [polarizationPow, wedgePow, ih]

/-- The top polarization power is nonzero when the polarization is nondegenerate.

This **replaces** the hypothesis `PolarizationTopPowerNonzero` by nondegeneracy of `ω`
(`Symplectic.IsNondegenerate`: contraction `V^∨ → V` with `ω` is bijective), a linear-algebra
condition. For the class of an ample line bundle, nondegeneracy is the nondegeneracy of the
Riemann form (Birkenhake–Lange, *Complex Abelian Varieties*, 2nd ed., Grundlehren 302, Ch. 4),
which is not formalized. It does not retire the hypothesis unconditionally.

Relation to the goal: HC no distance; AV milestone no distance; `PolarizationTopPowerNonzero` is
replaced by nondegeneracy of the polarization.

Source: Birkenhake–Lange, *Complex Abelian Varieties*, 2nd ed., Grundlehren 302, Ch. 4 (the
Riemann form of a polarization); the linear algebra is
`Symplectic.wedgePow_ne_zero_of_isNondegenerate`. -/
theorem polarizationTopPowerNonzero_of_isNondegenerate (S : AbelianVarietyCohomology V)
    (ω : ⋀[ℚ]^2 V) (hω : IsNondegenerate ω) : PolarizationTopPowerNonzero S ω :=
  ⟨by
    rw [polarizationPow_eq_wedgePow]
    exact wedgePow_ne_zero_of_isNondegenerate hω S.rank_eq⟩

/-- Conversely, `PolarizationTopPowerNonzero S ω` forces `ω` to be nondegenerate: the hypothesis
is exactly nondegeneracy, no more and no less.

Relation to the goal: HC no distance; AV milestone no distance; `PolarizationTopPowerNonzero` is
replaced by nondegeneracy of the polarization. -/
theorem isNondegenerate_of_polarizationTopPowerNonzero (S : AbelianVarietyCohomology V)
    (ω : ⋀[ℚ]^2 V) (h : PolarizationTopPowerNonzero S ω) : IsNondegenerate ω :=
  isNondegenerate_of_wedgePow_ne_zero S.rank_eq (by
    rw [← polarizationPow_eq_wedgePow]
    exact h.ne_zero)

/-- `PolarizationTopPowerNonzero S ω` holds iff `ω` is nondegenerate.

Relation to the goal: HC no distance; AV milestone no distance; `PolarizationTopPowerNonzero` is
replaced by nondegeneracy of the polarization. -/
theorem polarizationTopPowerNonzero_iff_isNondegenerate (S : AbelianVarietyCohomology V)
    (ω : ⋀[ℚ]^2 V) : PolarizationTopPowerNonzero S ω ↔ IsNondegenerate ω :=
  ⟨isNondegenerate_of_polarizationTopPowerNonzero S ω,
    polarizationTopPowerNonzero_of_isNondegenerate S ω⟩

end HodgeLean.Adapters
