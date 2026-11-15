import HodgeLean.Foundations.CMLieBlocks
import HodgeLean.Foundations.WeilPowerClasses
import HodgeLean.Foundations.RationalPolarization
import HodgeLean.Blocks.Weil.WeilClasses
import HodgeLean.Blocks.Weil.RationalKernel

/-! # Weil classes for a general CM field, stage A5 (FROZEN DEFINITIONS)

Definitions for `CMWeilClasses`, stage A5 of the Powers flagship (PW v0.3, Theorem 4.2,
doi:10.5281/zenodo.23570103; plan `docs/roadmap/pw-flagship-plan.md`, §4.2 row A5, step T6). They
live in the model `ℂ ⊗ (V ⊗ ℚ^r)` of `H¹(A^r, ℂ)`, written through
`WeilPower.powerBaseChange r : ℂ ⊗ (V ⊗ ℚ^r) ≃ (ℂ ⊗ V) ⊗ ℂ^r`:

* `a5_cmDet r x y`, the decomposable class `(x₁ ⊗ y₁) ∧ ⋯ ∧ (x_n ⊗ y_n)` of degree `n`; for `x` a
  concatenation of bases of the blocks `W_v` and `y_j = y_{v(j)}` it is the paper's
  `⊗_v det(W^v ⊗ y_v)`;
* `a5_cmTheta r b c x x'`, the contraction `Σ_i (b_i ⊗ x) ∧ (c_i ⊗ x')` of degree `2`; for `b` a
  basis of `W_v` and `c` the `E_ℂ`-dual basis of `W_v̄` it is the paper's `Θ_v(x, x')`.

Neither definition asserts invariance, Hodge type, a span or a descent statement. HC no distance;
AV milestone no distance.
-/

noncomputable section

namespace HodgeLean.Foundations

open scoped TensorProduct

variable {V : Type*} [AddCommGroup V] [Module ℚ V]

/-- The decomposable class `(x₁ ⊗ y₁) ∧ ⋯ ∧ (x_n ⊗ y_n)` in `⋀^n (ℂ ⊗ (V ⊗ ℚ^r))`, for vectors
`x_j ∈ ℂ ⊗ V` and multiplicity vectors `y_j ∈ ℂ^r`. When `x` runs through bases of the blocks
`W_v` and `y_j` depends only on the block of `x_j`, it is the paper's `⊗_v det(W^v ⊗ y_v)`.
Source: PW v0.3, proof of Theorem 4.2, paragraph "Weil classes"
(`f_a^*(⊗_v det W^v) = ⊗_v det(W^v ⊗ σ_v(a))`) and Lemma 4.1 (`det(W ⊗ x)`); the one-block
case is `InvariantsExterior.detWOf` (`Foundations/InvariantsExterior.lean`). -/
def a5_cmDet (r : ℕ) {n : ℕ} (x : Fin n → ℂ ⊗[ℚ] V) (y : Fin n → Fin r → ℂ) :
    ⋀[ℂ]^n (ℂ ⊗[ℚ] (V ⊗[ℚ] (Fin r → ℚ))) :=
  exteriorPower.ιMulti ℂ n (fun j => (WeilPower.powerBaseChange (V := V) r).symm (x j ⊗ₜ[ℂ] y j))

example (r : ℕ) (x : Fin 0 → ℂ ⊗[ℚ] V) (y : Fin 0 → Fin r → ℂ) :
    a5_cmDet r x y = exteriorPower.ιMulti ℂ 0 Fin.elim0 := by
  simp only [a5_cmDet]
  congr 1
  funext j
  exact j.elim0

/-- The contraction `Σ_i (b_i ⊗ x) ∧ (c_i ⊗ x')` in `⋀² (ℂ ⊗ (V ⊗ ℚ^r))`. For `b` a basis of
`W_v` and `c` the basis of `W_v̄` dual to it under `E_ℂ`, it is the paper's `Θ_v(x, x')`.
Source: PW v0.3, Lemma 4.1 (`Θ(x, x') = Σ_i (w_i ⊗ x) ∧ (w_i^∨ ⊗ x')` for dual bases) and the
proof of Theorem 4.2, paragraph "Derived group" (`Θ_v`); the one-block case is
`InvariantsExterior.theta` (`Foundations/InvariantsExterior.lean`). -/
def a5_cmTheta (r : ℕ) {m : ℕ} (b c : Fin m → ℂ ⊗[ℚ] V) (x x' : Fin r → ℂ) :
    ⋀[ℂ]^2 (ℂ ⊗[ℚ] (V ⊗[ℚ] (Fin r → ℚ))) :=
  ∑ i, exteriorPower.ιMulti ℂ 2
    ![(WeilPower.powerBaseChange (V := V) r).symm (b i ⊗ₜ[ℂ] x),
      (WeilPower.powerBaseChange (V := V) r).symm (c i ⊗ₜ[ℂ] x')]

example (r : ℕ) (b c : Fin 0 → ℂ ⊗[ℚ] V) (x x' : Fin r → ℂ) : a5_cmTheta r b c x x' = 0 := by
  simp [a5_cmTheta]

/-- The coefficients `ι(a_i) ∈ ι(L)` of `f_a : A^r → A`, `(x_i) ↦ Σ_i a_i x_i`, for `a ∈ L^r`, as
elements of the subalgebra `ι.range` that PW-0's `cmPowerPullback` takes.
Source: PW v0.3, Theorem 4.2 (the maps `f_a`, `a ∈ (L ∩ End(A))^r`); `cmPowerPullback`
(`Foundations/PowersVocabularyDefs.lean`). -/
def a5_cmCoeff {L : Type*} [CommRing L] [Algebra ℚ L] (ι : L →ₐ[ℚ] Module.End ℚ V) {r : ℕ}
    (a : Fin r → L) : Fin r → ι.range :=
  fun i => ⟨ι (a i), AlgHom.mem_range_self ι (a i)⟩

example {L : Type*} [CommRing L] [Algebra ℚ L] (ι : L →ₐ[ℚ] Module.End ℚ V) {r : ℕ}
    (a : Fin r → L) (x : V) :
    cmPowerPullback ι.range (a5_cmCoeff ι a) x =
      ∑ i, ι (a i) x ⊗ₜ[ℚ] (Pi.single i 1 : Fin r → ℚ) := by
  simp [cmPowerPullback, a5_cmCoeff]

end HodgeLean.Foundations
