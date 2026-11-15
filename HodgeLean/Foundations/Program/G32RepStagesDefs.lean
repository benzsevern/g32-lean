import HodgeLean.Foundations.Program.G32ContractionDefs
import HodgeLean.Foundations.RepFoundations
import HodgeLean.RealDefs.F1569

/-! # The G32 action as a representation, and the polarization form (FROZEN DEFINITIONS)

The pullback action of `G₃₂` on `ℂ ⊗ H¹(J; ℚ)` of a realized cover, packaged as a
`Representation` so that the general multiplicity spaces `rfd_mult` and characters `rfd_det`
apply to it, and the complexified polarization form `E_ω` on `ℂ ⊗ H¹(J; ℚ)`. The membership
`g32rep_U_le` (every element of `g32c_U` centralizes the action) has a full proof here, because the
statement `g32rep_char_eq` needs it as an argument. No definition records a determinant value,
a multiplicity or a form type. HC no distance; AV milestone no distance.
-/

noncomputable section
set_option maxHeartbeats 400000

open scoped TensorProduct CategoryTheory.MonObj
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open HodgeLean.RealDefs HodgeLean.Adapters HodgeLean.Papers HodgeLean.Foundations
open HodgeLean.Foundations.Symplectic

namespace HodgeLean.Foundations.Program

variable {A : g32t_Sixfold}

/-- **Stage A: the action of `G₃₂` on `ℂ ⊗ H¹(J; ℚ)` as a representation**,
`g ↦ (aut g)^*` complexified. Pullback is contravariant (`spec_homPullback_comp`) and
`aut (g * h) = aut g ≫ aut h` (`X.aut_mul`), so `g ↦ (aut g)^*` is multiplicative;
`X.aut_one` and `spec_homPullback_id` give the unit.
Source: G32 v0.16, Subsection 4.2 (`G` acting on `H¹(C, ℂ)`); Serre, *Linear representations of
finite groups*, §1.1; `homPullback`, `spec_homPullback_comp`, `spec_homPullback_id`. -/
def g32rep_rep (X : g32p_Cover A) : Representation ℂ g32p_G (ℂ ⊗[ℚ] HQ X.J 1) where
  toFun g := (homPullback (X.aut g) 1).baseChange ℂ
  map_one' := by
    rw [X.aut_one, spec_homPullback_id, LinearMap.baseChange_id, Module.End.one_eq_id]
  map_mul' g h := by
    rw [X.aut_mul, spec_homPullback_comp, LinearMap.baseChange_comp, Module.End.mul_eq_comp]

/-- The representation is the complexified pullback, the map used in `g32c_mult` and `g32c_U`. -/
example (X : g32p_Cover A) (g : g32p_G) :
    g32rep_rep X g = (homPullback (X.aut g) 1).baseChange ℂ := rfl

/-- **Elements of `U` centralize the representation.** The second clause of `g32c_U` is
commutation with every `(aut g)^*`.
Source: G32 v0.16, Subsection 4.2 (`U` is the centralizer of `G`); `g32c_U`. -/
theorem g32rep_U_le (X : g32p_Cover A) {u : Module.End ℂ (ℂ ⊗[ℚ] HQ X.J 1)}
    (hu : u ∈ g32c_U X) : u ∈ Subalgebra.centralizer ℂ (Set.range (g32rep_rep X)) := by
  rw [Subalgebra.mem_centralizer_iff]
  rintro _ ⟨g, rfl⟩
  exact (hu.2.1 g).symm

/-- `-1` centralizes the representation. -/
example (X : g32p_Cover A) :
    (-1 : Module.End ℂ (ℂ ⊗[ℚ] HQ X.J 1)) ∈
      Subalgebra.centralizer ℂ (Set.range (g32rep_rep X)) := by
  rw [Subalgebra.mem_centralizer_iff]
  rintro _ ⟨g, rfl⟩
  simp

/-- **Stage B: the polarization form on `ℂ ⊗ H¹(J; ℚ)`**, the base change to `ℂ` of the
Riemann form `E_ω` of the polarization (`polarizationForm`, the form dual to the nondegenerate
2-vector `polarizationVec … X.pol`, nondegenerate by `X.pol_nondeg`). It is the form whose
2-vector `g32c_U` fixes.
Source: Birkenhake–Lange, *Complex Abelian Varieties*, 2nd ed., Ch. 4 (the Riemann form of a
polarization); G32 v0.16, Subsection 4.2 (`U` in the symplectic group of `(H¹(C, ℚ), E)`);
`polarizationForm`, Mathlib `LinearMap.BilinForm.baseChange`. -/
def g32rep_form (X : g32p_Cover A) : LinearMap.BilinForm ℂ (ℂ ⊗[ℚ] HQ X.J 1) :=
  (polarizationForm (torusCohomology_cupProductOf X.J) X.pol_nondeg).baseChange ℂ

/-- On complexified rational classes the form is the rational Riemann form. -/
example (X : g32p_Cover A) (x y : HQ X.J 1) :
    g32rep_form X ((1 : ℂ) ⊗ₜ x) ((1 : ℂ) ⊗ₜ y) =
      ((polarizationForm (torusCohomology_cupProductOf X.J) X.pol_nondeg x y : ℚ) : ℂ) := by
  simp [g32rep_form]

end HodgeLean.Foundations.Program
