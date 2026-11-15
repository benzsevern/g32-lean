import HodgeLean.Foundations.HSUFiniteDefs
import HodgeLean.Foundations.SchurWeylLie

/-! # Bounded mixed tensors and the 12-dimensional Weil candidate (FROZEN DEFINITIONS)

A bounded mixed tensor is an element of `T^{a,b}(V) = V^{⊗a} ⊗ (V^∨)^{⊗b}` for one type
`(a, b)`, reusing `SchurWeyl.MixedTensor` and its Lie-module structure `SchurWeyl.mixedLie` (the
derivation action, `-Xᵀ` on the dual slots). A finite list may mix types. The 12-dimensional
candidate is the block model of the F-1569 Hermitian datum `⟨1, 1, 1, -1, -1, -2⟩` over
`ℚ(√-3)`: `J` is multiplication by `√-3` and `E` the matching alternating form.
-/

noncomputable section
attribute [local instance 100] LieRing.ofAssociativeRing
attribute [local instance] HodgeLean.Foundations.SchurWeyl.dualAddCommGroup

namespace HodgeLean.Foundations

open SchurWeyl PiTensorProduct
open scoped TensorProduct

section Mixed

variable (V : Type*) [AddCommGroup V] [Module ℚ V]

/-- The rational mixed tensors of type `(a, b)`: `V^{⊗a} ⊗ (V^∨)^{⊗b}`, a Lie module over
`End_ℚ V` by derivations (`SchurWeyl.mixedLie`).
Source: Goodman–Wallach, *Symmetry, Representations, and Invariants*, GTM 255, Ch. 5 (mixed
tensors); Deligne, *Hodge cycles on abelian varieties*, LNM 900 (1982), §1 (the tensor spaces
`T^{a,b}`). -/
abbrev MixedTensorOfType (ab : ℕ × ℕ) : Type _ := MixedTensor ℚ V (Fin ab.1) (Fin ab.2)

example (X : Module.End ℚ V) (v : MixedTensorOfType V (1, 1)) :
    ⁅X, v⁆ = mixedLie ℚ V (Fin 1) (Fin 1) X v := rfl

/-- A bounded mixed tensor: a type `(a, b)` together with a tensor of that type.
Source: Deligne, *Hodge cycles on abelian varieties*, LNM 900 (1982), §1 (a Hodge tensor is an
element of one `T^{a,b}`); Moonen, *An introduction to Mumford–Tate groups* (2004), §2. -/
abbrev BoundedTensor : Type _ := Σ ab : ℕ × ℕ, MixedTensorOfType V ab

example (v : MixedTensorOfType V (2, 0)) : BoundedTensor V := ⟨(2, 0), v⟩

variable {V}

/-- The complexification of the common infinitesimal stabilizer of a finite list of rational
mixed tensors, of possibly different types.
Source: Deligne, *Hodge cycles on abelian varieties*, LNM 900 (1982), §2; Moonen,
*An introduction to Mumford–Tate groups* (2004), §2. -/
def mixedTensorStabilizer {n : ℕ} (t : Fin n → BoundedTensor V) :
    Submodule ℂ (Module.End ℂ (ℂ ⊗[ℚ] V)) :=
  complexSpan ((⨅ i, lieAnnihilator (MixedTensorOfType V (t i).1) (t i).2).toSubmodule)

example (t : Fin 0 → BoundedTensor V) :
    mixedTensorStabilizer t =
      complexSpan (⊤ : LieSubalgebra ℚ (Module.End ℚ V)).toSubmodule := by
  simp [mixedTensorStabilizer]

/-- A vector as a mixed tensor of type `(1, 0)`.
Source: the identification `V ≅ V^{⊗1} ⊗ (V^∨)^{⊗0}`, Goodman–Wallach, GTM 255, Ch. 5. -/
def vecTensor (v : V) : MixedTensorOfType V (1, 0) :=
  tprod ℚ (fun _ : Fin 1 => v) ⊗ₜ tprod ℚ (fun i : Fin 0 => i.elim0)

example : vecTensor (0 : V) = 0 := by
  have h : tprod ℚ (fun _ : Fin 1 => (0 : V)) = 0 := (PiTensorProduct.tprod ℚ).map_coord_zero (0 : Fin 1) rfl
  rw [vecTensor, h, TensorProduct.zero_tmul]

variable {ι : Type*} [Fintype ι]

/-- An endomorphism `A` as the mixed tensor `∑ⱼ A bⱼ ⊗ bⱼ^∨` of type `(1, 1)`; it does not
depend on the basis.
Source: the identification `End V ≅ V ⊗ V^∨`, Goodman–Wallach, GTM 255, Ch. 5. -/
def endTensor (b : Module.Basis ι ℚ V) (A : Module.End ℚ V) : MixedTensorOfType V (1, 1) :=
  ∑ j, tprod ℚ (fun _ : Fin 1 => A (b j)) ⊗ₜ tprod ℚ (fun _ : Fin 1 => b.coord j)

example (b : Module.Basis ι ℚ V) : endTensor b 0 = 0 := by
  have h : tprod ℚ (fun _ : Fin 1 => (0 : V)) = 0 := (PiTensorProduct.tprod ℚ).map_coord_zero (0 : Fin 1) rfl
  simp [endTensor, h]

/-- A bilinear form `E` as the mixed tensor `∑ᵢⱼ E(bᵢ, bⱼ) bᵢ^∨ ⊗ bⱼ^∨` of type `(0, 2)`; it does
not depend on the basis.
Source: the identification of bilinear forms with `V^∨ ⊗ V^∨`, Goodman–Wallach, GTM 255,
Ch. 5. -/
def formTensor (b : Module.Basis ι ℚ V) (E : LinearMap.BilinForm ℚ V) :
    MixedTensorOfType V (0, 2) :=
  ∑ i, ∑ j, E (b i) (b j) •
    (tprod ℚ (fun k : Fin 0 => k.elim0) ⊗ₜ tprod ℚ ![b.coord i, b.coord j])

example (b : Module.Basis ι ℚ V) : formTensor b 0 = 0 := by simp [formTensor]

end Mixed

section Candidate

/-- The diagonal of the F-1569 Hermitian form `⟨1, 1, 1, -1, -1, -2⟩` over `ℚ(√-3)`.
Source: `HermitianForm.detClass_diag_F1569` and `HermitianForm.hermSignature_diag_F1569`. -/
def hsuWeights : Fin 6 → ℚ := ![1, 1, 1, -1, -1, -2]

example : hsuWeights 5 = -2 := rfl

/-- The Weil operator on `ℚ¹² = ℚ(√-3)⁶`: on each block `(x₂ₖ, x₂ₖ₊₁) ↦ (-3 x₂ₖ₊₁, x₂ₖ)`,
multiplication by `√-3` on `x₂ₖ + x₂ₖ₊₁ √-3`.
Source: the block matrix `exJ₄` in `HodgeLean.Foundations.WeilHermitian`, repeated six times;
van Geemen, *An introduction to the Hodge conjecture for abelian varieties*, §5. -/
def hsuJ₁₂ : Matrix (Fin 12) (Fin 12) ℚ := Matrix.of fun i j =>
  if i.val % 2 = 0 ∧ j.val = i.val + 1 then -3
  else if i.val % 2 = 1 ∧ j.val + 1 = i.val then 1 else 0

example : hsuJ₁₂ 0 1 = -3 ∧ hsuJ₁₂ 1 0 = 1 ∧ hsuJ₁₂ 0 0 = 0 := by
  simp [hsuJ₁₂]

/-- The polarization on `ℚ¹²`: the block form `x₂ₖ y₂ₖ₊₁ - x₂ₖ₊₁ y₂ₖ` weighted by
`hsuWeights k`.
Source: the block form `exE₄` in `HodgeLean.Foundations.WeilHermitian` with the weights of
F-1569; van Geemen, *An introduction to the Hodge conjecture for abelian varieties*, §5. -/
def hsuE₁₂ : Matrix (Fin 12) (Fin 12) ℚ := Matrix.of fun i j =>
  if i.val % 2 = 0 ∧ j.val = i.val + 1 then hsuWeights ⟨i.val / 2, by have := i.isLt; omega⟩
  else if i.val % 2 = 1 ∧ j.val + 1 = i.val then
    -hsuWeights ⟨i.val / 2, by have := i.isLt; omega⟩
  else 0

example : hsuE₁₂ 10 11 = -2 ∧ hsuE₁₂ 11 10 = 2 ∧ hsuE₁₂ 0 2 = 0 := by
  simp [hsuE₁₂, hsuWeights]

/-- The Weil operator of the candidate as a linear map.
Source: `hsuJ₁₂`. -/
def hsuJ : Module.End ℚ (Fin 12 → ℚ) := Matrix.toLin' hsuJ₁₂

example (x : Fin 12 → ℚ) : hsuJ x = hsuJ₁₂.mulVec x := rfl

/-- The polarization of the candidate as a bilinear form.
Source: `hsuE₁₂`. -/
def hsuE : LinearMap.BilinForm ℚ (Fin 12 → ℚ) := Matrix.toBilin' hsuE₁₂

example (x y : Fin 12 → ℚ) : hsuE x y = x ⬝ᵥ hsuE₁₂.mulVec y := by
  simp [hsuE, Matrix.toBilin'_apply']

/-- The Weil operator of the candidate as a `(1, 1)` tensor.
Source: `endTensor` in the standard basis. -/
def hsuJTensor : MixedTensorOfType (Fin 12 → ℚ) (1, 1) :=
  endTensor (Pi.basisFun ℚ (Fin 12)) hsuJ

example : hsuJTensor = endTensor (Pi.basisFun ℚ (Fin 12)) hsuJ := rfl

/-- The polarization of the candidate as a `(0, 2)` tensor.
Source: `formTensor` in the standard basis. -/
def hsuETensor : MixedTensorOfType (Fin 12 → ℚ) (0, 2) :=
  formTensor (Pi.basisFun ℚ (Fin 12)) hsuE

example : hsuETensor = formTensor (Pi.basisFun ℚ (Fin 12)) hsuE := rfl

/-- The one-element list: the polarization alone.
Source: constructed here for the falsification check. -/
def hsuPolarizationOnly : Fin 1 → BoundedTensor (Fin 12 → ℚ) := ![⟨(0, 2), hsuETensor⟩]

example : (hsuPolarizationOnly 0).1 = (0, 2) := rfl

/-- The two-element mixed list: the Weil operator (type `(1, 1)`) and the polarization (type
`(0, 2)`).
Source: constructed here; Moonen, *An introduction to Mumford–Tate groups* (2004), §2 (the
endomorphisms and the polarization are Hodge tensors). -/
def hsuWeilPair : Fin 2 → BoundedTensor (Fin 12 → ℚ) :=
  ![⟨(1, 1), hsuJTensor⟩, ⟨(0, 2), hsuETensor⟩]

example : (hsuWeilPair 0).1 = (1, 1) ∧ (hsuWeilPair 1).1 = (0, 2) := ⟨rfl, rfl⟩

end Candidate

end HodgeLean.Foundations
