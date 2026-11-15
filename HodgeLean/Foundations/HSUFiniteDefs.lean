import HodgeLean.Foundations.HodgeLieAlgebra
import HodgeLean.Foundations.WeilPowerLie

/-! # Finite tensor stabilizers for the Hodge Lie algebra (FROZEN DEFINITIONS) -/

noncomputable section
attribute [local instance 100] LieRing.ofAssociativeRing

namespace HodgeLean.Foundations

open scoped TensorProduct

variable {V N : Type*} [AddCommGroup V] [Module ℚ V]
  [AddCommGroup N] [Module ℚ N] [LieRingModule (Module.End ℚ V) N]
  [LieModule ℚ (Module.End ℚ V) N]

/-- The complexification of the common infinitesimal stabilizer of a finite family of rational
tensors in one fixed tensor representation.

Source: Deligne, *Hodge cycles on abelian varieties*, LNM 900 (1982), §2; Moonen,
*An introduction to Mumford–Tate groups* (2004), §2. -/
def finiteTensorStabilizer {n : ℕ} (t : Fin n → N) :
    Submodule ℂ (Module.End ℂ (ℂ ⊗[ℚ] V)) :=
  complexSpan ((⨅ i, lieAnnihilator N (t i)).toSubmodule)

example (t : Fin 0 → N) :
    finiteTensorStabilizer (V := V) t =
      complexSpan (⊤ : LieSubalgebra ℚ (Module.End ℚ V)).toSubmodule := by
  simp [finiteTensorStabilizer]

/-- The explicit two-block Weil operator used for the smallest nontrivial matrix test.
Source: the matrix `exJ₄` in `HodgeLean.Foundations.WeilHermitian`. -/
def hSUFiniteSmallJ : (Fin 4 → ℚ) →ₗ[ℚ] (Fin 4 → ℚ) :=
  WeilHermitian.exJ₄

example (x : Fin 4 → ℚ) :
    hSUFiniteSmallJ x = ![-3 * x 1, x 0, -3 * x 3, x 2] := rfl

/-- The explicit block symplectic form used for the smallest nontrivial matrix test.
Source: the matrix `exE₄` in `HodgeLean.Foundations.WeilHermitian`. -/
def hSUFiniteSmallE : LinearMap.BilinForm ℚ (Fin 4 → ℚ) :=
  WeilHermitian.exE₄

example (x y : Fin 4 → ℚ) :
    hSUFiniteSmallE x y = x 0 * y 1 - x 1 * y 0 + (x 2 * y 3 - x 3 * y 2) := rfl

/-- The all-`(0,0)` Hodge decomposition on the four-dimensional test space.
Source: Deligne, *Théorie de Hodge II* (1971), §2.1 (the trivial weight-zero structure). -/
def hSUFiniteTrivialHodge :
    ℤ × ℤ → Submodule ℂ (ℂ ⊗[ℚ] (Fin 4 → ℚ)) :=
  fun k => if k = (0, 0) then ⊤ else ⊥

theorem hSUFiniteTrivialHodge_isInternal : DirectSum.IsInternal hSUFiniteTrivialHodge :=
  isInternal_single (0, 0)

example : hSUFiniteTrivialHodge (0, 0) = ⊤ := by simp [hSUFiniteTrivialHodge]

end HodgeLean.Foundations
