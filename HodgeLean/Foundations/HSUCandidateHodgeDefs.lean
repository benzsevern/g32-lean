import HodgeLean.Foundations.HSUTensors

/-! # The Weil tensor and a CM Hodge structure on the 12-dimensional candidate (FROZEN DEFINITIONS)

Stage 3 of the `hSU` lane. On the stage-2 candidate `ℚ¹² = K⁶`, `K = ℚ(√-3)` (`hsuJ`, `hsuE`),
with `K`-coordinates `z_k = x₂ₖ + √-3 x₂ₖ₊₁`:

* `hsuWeilTensor`, the real part of the `K`-determinant `det_K(v₁, …, v₆) = det (z_k (v_i))`, a
  rational alternating form of type `(0, 6)`: the standard Weil class (van Geemen §6);
* the lists `hsuWeilTriple = [J, E, w]` and, for a falsification check, `hsuRosatiTriple =
  [J, E, E(·, J·)]`;
* `hsuCMHodge`, an explicit weight-one Hodge decomposition of Weil type: `H^{1,0}` is spanned by
  one `J`-eigenvector in each block, chosen by the sign of the block's Hermitian weight. It is a
  CM point (a product of six CM elliptic curves): its Hodge Lie algebra is a line, not
  `complexSU`;
* `hsuCMTorus`, the rational operator whose base change is `√3` times its grading operator.
-/

noncomputable section
attribute [local instance 100] LieRing.ofAssociativeRing
attribute [local instance] HodgeLean.Foundations.SchurWeyl.dualAddCommGroup

namespace HodgeLean.Foundations

open WeilPower SchurWeyl PiTensorProduct
open scoped TensorProduct

section WeilTensor

/-- The coefficient of `∏ᵢ x_{2σ(i) + sᵢ}` in the real part of `∏ᵢ (x_{2σ(i)} + √-3 x_{2σ(i)+1})`:
with `m = #{i | sᵢ = 1}`, it is `(-3)^(m/2)` for `m` even and `0` for `m` odd (`(√-3)^m` is then
irrational).
Source: binomial expansion in `K = ℚ(√-3)`; van Geemen, *An introduction to the Hodge conjecture
for abelian varieties*, §6 (the Weil classes as the `K`-determinant). -/
def hsuWeilCoeff (s : Fin 6 → Fin 2) : ℚ :=
  if Even (Finset.univ.filter fun i => s i = 1).card then
    (-3 : ℚ) ^ ((Finset.univ.filter fun i => s i = 1).card / 2)
  else 0

example : hsuWeilCoeff (fun _ => 0) = 1 := by decide

/-- The Weil tensor of the candidate: the real part of the `K`-determinant,
`w = ∑_σ sgn σ ∑_s hsuWeilCoeff s · x_{2σ(0)+s₀} ⊗ ⋯ ⊗ x_{2σ(5)+s₅}`, a rational mixed tensor of
type `(0, 6)`. As a form, `w (v₁, …, v₆) = Re det (z_k (v_i))` with `z_k = x₂ₖ + √-3 x₂ₖ₊₁`.
Source: Weil, *Abelian varieties and the Hodge ring* (1977); van Geemen, *An introduction to the
Hodge conjecture for abelian varieties*, §6; Moonen–Zarhin, *Weil classes on abelian varieties*,
J. reine angew. Math. 496 (1998), §2 (the `K`-determinant `⋀⁶_K` spans the Weil classes). -/
def hsuWeilTensor : MixedTensorOfType (Fin 12 → ℚ) (0, 6) :=
  ∑ σ : Equiv.Perm (Fin 6), ∑ s : Fin 6 → Fin 2,
    (((Equiv.Perm.sign σ : ℤ) : ℚ) * hsuWeilCoeff s) •
      (tprod ℚ (fun k : Fin 0 => k.elim0) ⊗ₜ
        tprod ℚ (fun i => (Pi.basisFun ℚ (Fin 12)).coord
          ⟨2 * (σ i).val + (s i).val, by have := (σ i).isLt; have := (s i).isLt; omega⟩))

example : hsuWeilTensor = ∑ σ : Equiv.Perm (Fin 6), ∑ s : Fin 6 → Fin 2,
    (((Equiv.Perm.sign σ : ℤ) : ℚ) * hsuWeilCoeff s) •
      (tprod ℚ (fun k : Fin 0 => k.elim0) ⊗ₜ
        tprod ℚ (fun i => (Pi.basisFun ℚ (Fin 12)).coord
          ⟨2 * (σ i).val + (s i).val, by have := (σ i).isLt; have := (s i).isLt; omega⟩)) := rfl

/-- The three-element mixed list: the Weil operator (type `(1, 1)`), the polarization
(type `(0, 2)`) and the Weil tensor (type `(0, 6)`).
Source: constructed here; Moonen, *An introduction to Mumford–Tate groups* (2004), §2; van Geemen,
§6 (the endomorphisms, the polarization and the Weil classes are Hodge tensors of a Weil-type
structure). -/
def hsuWeilTriple : Fin 3 → BoundedTensor (Fin 12 → ℚ) :=
  ![⟨(1, 1), hsuJTensor⟩, ⟨(0, 2), hsuETensor⟩, ⟨(0, 6), hsuWeilTensor⟩]

example : (hsuWeilTriple 2).1 = (0, 6) := rfl

/-- The symmetric form `S(x, y) = E(x, J y)`, the real part of the Hermitian form, as a `(0, 2)`
tensor. A wrong candidate for the extra tensor: the unitary Lie algebra already fixes it.
Source: `WeilHermitian.weilHermitian` (its `ℚ`-part); `formTensor` in the standard basis. -/
def hsuRosatiTensor : MixedTensorOfType (Fin 12 → ℚ) (0, 2) :=
  formTensor (Pi.basisFun ℚ (Fin 12)) (hsuE.compl₂ hsuJ)

example : hsuRosatiTensor = formTensor (Pi.basisFun ℚ (Fin 12)) (hsuE.compl₂ hsuJ) := rfl

/-- The falsification list `[J, E, E(·, J·)]`: the Weil tensor replaced by the Hermitian form's
real part.
Source: constructed here for the falsification check. -/
def hsuRosatiTriple : Fin 3 → BoundedTensor (Fin 12 → ℚ) :=
  ![⟨(1, 1), hsuJTensor⟩, ⟨(0, 2), hsuETensor⟩, ⟨(0, 2), hsuRosatiTensor⟩]

example : (hsuRosatiTriple 2).1 = (0, 2) := rfl

end WeilTensor

section CMHodge

/-- The sign selecting the `H^{1,0}` eigenvector in block `k`: `-1` on the blocks of positive
Hermitian weight (`k < 3`), `+1` on the blocks of negative weight. It equals
`-sign (hsuWeights k)`, which makes `i E(x, x̄)` positive on `H^{1,0}`.
Source: constructed here from `hsuWeights`; Birkenhake–Lange, *Complex Abelian Varieties*,
2nd ed., §4.2 (Riemann relations). -/
def hsuPeriodSign (k : Fin 6) : ℂ := if k.val < 3 then -1 else 1

example : hsuPeriodSign 0 = -1 ∧ hsuPeriodSign 5 = 1 := by simp [hsuPeriodSign]

/-- The `H^{1,0}` basis vector in block `k`: `f_k = ε_k √-3 e₂ₖ + e₂ₖ₊₁` with `ε_k =
hsuPeriodSign k`, an eigenvector of `J_ℂ` with eigenvalue `ε_k √-3`.
Source: constructed here; on one block `J(x, y) = (-3y, x)` has eigenvectors `(±√-3, 1)`. -/
def hsuPeriodVec (k : Fin 6) : ℂ ⊗[ℚ] (Fin 12 → ℚ) :=
  (hsuPeriodSign k * root) ⊗ₜ Pi.single (⟨2 * k.val, by omega⟩ : Fin 12) (1 : ℚ) +
    (1 : ℂ) ⊗ₜ Pi.single (⟨2 * k.val + 1, by omega⟩ : Fin 12) (1 : ℚ)

example : hsuPeriodVec 5 = root ⊗ₜ Pi.single (10 : Fin 12) (1 : ℚ) +
    (1 : ℂ) ⊗ₜ Pi.single (11 : Fin 12) (1 : ℚ) := by
  simp [hsuPeriodVec, hsuPeriodSign]

/-- The complex conjugate of `hsuPeriodVec k`, the `H^{0,1}` basis vector in block `k`.
Source: constructed here; `conj_root`. -/
def hsuPeriodVecBar (k : Fin 6) : ℂ ⊗[ℚ] (Fin 12 → ℚ) :=
  (-(hsuPeriodSign k * root)) ⊗ₜ Pi.single (⟨2 * k.val, by omega⟩ : Fin 12) (1 : ℚ) +
    (1 : ℂ) ⊗ₜ Pi.single (⟨2 * k.val + 1, by omega⟩ : Fin 12) (1 : ℚ)

example (k : Fin 6) : hsuPeriodVecBar k = (-(hsuPeriodSign k * root)) ⊗ₜ
    Pi.single (⟨2 * k.val, by omega⟩ : Fin 12) (1 : ℚ) +
      (1 : ℂ) ⊗ₜ Pi.single (⟨2 * k.val + 1, by omega⟩ : Fin 12) (1 : ℚ) := rfl

/-- The explicit CM Hodge decomposition of the candidate: `H^{1,0} = span (f_k)`,
`H^{0,1} = span (f̄_k)`, every other piece zero. It is of Weil type (three `f_k` in each
`J`-eigenspace) and polarized by `hsuE`; being spanned by `J`-eigenvectors block by block, it is
the Hodge structure of a product of six elliptic curves with CM by `K`.
Source: constructed here; van Geemen, *An introduction to the Hodge conjecture for abelian
varieties*, §5 (Weil-type period points); Deligne, *Théorie de Hodge II* (1971), §2.1. -/
def hsuCMHodge : ℤ × ℤ → Submodule ℂ (ℂ ⊗[ℚ] (Fin 12 → ℚ)) := fun pq =>
  if pq = (1, 0) then Submodule.span ℂ (Set.range hsuPeriodVec)
  else if pq = (0, 1) then Submodule.span ℂ (Set.range hsuPeriodVecBar)
  else ⊥

example : hsuCMHodge (2, 0) = ⊥ := by simp [hsuCMHodge]

/-- The rational operator `T`: on block `k` it is `-J` for `k < 3` and `J` for `k ≥ 3`, i.e.
`ε_k J` blockwise with `ε_k = hsuPeriodSign k`. Its base change is `√3` times the
grading operator of `hsuCMHodge`.
Source: constructed here from `hsuJ₁₂`; `hodgeLieAlgebra_complexStructureHodge` for the
one-block analogue. -/
def hsuCMTorus₁₂ : Matrix (Fin 12) (Fin 12) ℚ := Matrix.of fun i j =>
  (if i.val / 2 < 3 then -1 else 1) * hsuJ₁₂ i j

example : hsuCMTorus₁₂ 0 1 = 3 ∧ hsuCMTorus₁₂ 11 10 = 1 := by
  simp [hsuCMTorus₁₂, hsuJ₁₂]

/-- The operator `hsuCMTorus₁₂` as a linear map.
Source: `hsuCMTorus₁₂`. -/
def hsuCMTorus : Module.End ℚ (Fin 12 → ℚ) := Matrix.toLin' hsuCMTorus₁₂

example (x : Fin 12 → ℚ) : hsuCMTorus x = hsuCMTorus₁₂.mulVec x := rfl

end CMHodge

end HodgeLean.Foundations
