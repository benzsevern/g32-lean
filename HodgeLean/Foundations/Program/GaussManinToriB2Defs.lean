import HodgeLean.Foundations.Program.GaussManinTori
import HodgeLean.Foundations.Program.RelativeTorusKernel
import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# The marked-period adapter to B2: definitions (FROZEN DEFINITIONS)

These definitions feed D2's marked homology lattice to B2.  The filtration is the kernel of
the complexified period map, so the resulting quotient vector space is the original `ℂ^g`, not
the dual torus.
-/

noncomputable section

set_option maxHeartbeats 400000

open scoped TensorProduct Matrix

namespace HodgeLean.Foundations.Program

variable {g : ℕ}

/-- B2's constant marked homology local system `Λ_b = ℤ^{2g}`.
Source: Birkenhake--Lange, *Complex Abelian Varieties*, 2nd ed., §1.1. -/
abbrev d2b_localSystem (B : Type*) [TopologicalSpace B] (g : ℕ) :
    b2_LatticeLocalSystem B :=
  b2_constLocalSystem B (Fin (2 * g) → ℤ)

example (B : Type*) [TopologicalSpace B] (b : B) :
    (d2b_localSystem B g).fiber b = (Fin (2 * g) → ℤ) := rfl

/-- The complexification of the marked period map, `c ⊗ n ↦ c • P(n)`.
Source: Birkenhake--Lange, §1.1 (complexification of the period lattice). -/
def d2b_cplxPeriod (P : Fin g → Fin (2 * g) → ℂ) :
    (ℂ ⊗[ℤ] (Fin (2 * g) → ℤ)) →ₗ[ℂ] (Fin g → ℂ) :=
  LinearMap.liftBaseChange ℂ (d2_markingMap P)

example (P : Fin g → Fin (2 * g) → ℂ) (c : ℂ) (n : Fin (2 * g) → ℤ) :
    d2b_cplxPeriod P (c ⊗ₜ n) = c • d2_markingMap P n := by
  simp [d2b_cplxPeriod]

/-- The homology filtration `T^{0,1} = ker(P_ℂ)`.
Source: Birkenhake--Lange, §1.2 and §1.4. -/
def d2b_homologyF (P : Fin g → Fin (2 * g) → ℂ) :
    Submodule ℂ (ℂ ⊗[ℤ] (Fin (2 * g) → ℤ)) :=
  LinearMap.ker (d2b_cplxPeriod P)

example (P : Fin g → Fin (2 * g) → ℂ) :
    d2b_homologyF P = LinearMap.ker (d2b_cplxPeriod P) := rfl

/-- Coordinates on the complexification of the marked integral homology lattice.
Source: Bourbaki, *Algebre*, ch. II, section 5 (extension of scalars of a free module). -/
def d2b_vecZ (n : ℕ) : (ℂ ⊗[ℤ] (Fin n → ℤ)) ≃ₗ[ℂ] (Fin n → ℂ) :=
  ((Pi.basisFun ℤ (Fin n)).baseChange ℂ).equivFun

example (n : ℕ) : d2b_vecZ n 0 = 0 := map_zero _

/-- Evaluation of marked cohomology on marked homology, extended to complex scalars.
Source: Hatcher, *Algebraic Topology*, §3.1 (the evaluation pairing); Birkenhake--Lange, §1.4. -/
def d2b_pairing (g : ℕ) :
    ℂ ⊗[ℚ] (Fin (2 * g) → ℚ) →ₗ[ℂ]
      Module.Dual ℂ (ℂ ⊗[ℤ] (Fin (2 * g) → ℤ)) :=
  (dotProductBilin ℂ ℂ : (Fin (2 * g) → ℂ) →ₗ[ℂ] (Fin (2 * g) → ℂ) →ₗ[ℂ] ℂ).compl₁₂
    (d2_vec (2 * g)).symm.toLinearMap (d2b_vecZ (2 * g)).toLinearMap

example (q : Fin (2 * g) → ℚ) (n : Fin (2 * g) → ℤ) :
    d2b_pairing g ((1 : ℂ) ⊗ₜ q) ((1 : ℂ) ⊗ₜ n) =
      algebraMap ℚ ℂ (∑ k, q k * n k) := by
  simp [d2b_pairing, d2b_vecZ, d2_vec, dotProduct]

/-- The map from B2's fibre torus to the classical quotient `ℂ^g / Λ_P` induced by `P_ℂ`.
Source: Birkenhake--Lange, §1.1 and §2.4. -/
def d2b_fiberMap (P : Fin g → Fin (2 * g) → ℂ) :
    b2_torus (Fin (2 * g) → ℤ) (d2b_homologyF P) →+
      (Fin g → ℂ) ⧸ (d2_lattice P).toAddSubgroup :=
  QuotientAddGroup.lift _
    ((QuotientAddGroup.mk' (d2_lattice P).toAddSubgroup).comp
      ((d2b_homologyF P).liftQ (d2b_cplxPeriod P) (by
        rw [d2b_homologyF])).toAddMonoidHom)
    (by
      rintro _ ⟨n, rfl⟩
      change QuotientAddGroup.mk' (d2_lattice P).toAddSubgroup
        (d2b_cplxPeriod P ((1 : ℂ) ⊗ₜ n)) = 0
      rw [QuotientAddGroup.mk'_apply, QuotientAddGroup.eq_zero_iff]
      rw [d2b_cplxPeriod, LinearMap.liftBaseChange_tmul, one_smul]
      change d2_markingMap P n ∈ d2_lattice P
      rw [d2_lattice, d2_markingMap, ← Fintype.range_linearCombination]
      exact LinearMap.mem_range_self _ n)

example (P : Fin g → Fin (2 * g) → ℂ) : d2b_fiberMap P 0 = 0 := map_zero _

variable {E B : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [TopologicalSpace B] [ChartedSpace E B]

/-- The classical total-space map, obtained by inverting the fibre quotient identification.
Source: Birkenhake--Lange, *Complex Abelian Varieties*, 2nd ed., §1.1 and §2.4. -/
def d2b_totalMap (X : d2_MarkedPeriodFamily E B g) :
    B × (Fin g → ℂ) →
      b2_totalSpace (d2b_localSystem B g) (fun b ↦ d2b_homologyF (X.period b)) :=
  fun p ↦ ⟨p.1, Function.invFun (d2b_fiberMap (X.period p.1))
      (QuotientAddGroup.mk' (d2_lattice (X.period p.1)).toAddSubgroup p.2)⟩

example (X : d2_MarkedPeriodFamily E B g) (b : B) (z : Fin g → ℂ) :
    (d2b_totalMap X (b, z)).1 = b := rfl

end HodgeLean.Foundations.Program
