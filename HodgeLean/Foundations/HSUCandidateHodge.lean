import HodgeLean.Foundations.HSUCandidateHodgeProofs

/-!
# The Hodge tensors of the 12-dimensional `hSU` candidate (FROZEN SPEC)

Stage 3 of the `hSU` lane (after `HSUFinite` and `HSUTensors`). It claims:

* a finite mixed list consists of Hodge tensors exactly when the grading operator lies in its
  complexified stabilizer;
* the Weil tensor `w` (the real part of the `K`-determinant, type `(0, 6)`, `K = ℚ(√-3)`)
  together with `J` and `E` has stabilizer exactly `complexSU` (dimension `35`); the
  falsification list `[J, E, E(·, J·)]` has stabilizer of dimension `36`;
* an explicit weight-one Hodge decomposition `hsuCMHodge` of the candidate: internal, pure,
  conjugation-symmetric, `J`-stable, of Weil type `(3, 3)`, satisfying both Riemann relations for
  `hsuE`, with grading operator in `complexSU`, so `J`, `E`, `w` are Hodge tensors for it;
* falsification: `hsuCMHodge` is a CM point; its Hodge Lie algebra is the line `ℚ ∙ hsuCMTorus`,
  so the equality of `F1575MemberHodgeGroupIsSU`'s shape fails for it;
* the implication from `J`, `E`, `w` being Hodge tensors of a structure on `ℚ¹²` to inclusion of
  its complexified Hodge Lie algebra in `complexSU`, and the implication from that plus explicit
  generators in the Hodge Lie algebra to equality with `complexSU`.

It does not claim: any Hodge structure on the candidate whose Hodge Lie algebra is `complexSU`
(the generator hypothesis is open for every non-CM period point; none is exhibited); genericity
in the F-1575 family; realization by an abelian variety; any link from `ℚ¹²` to the cohomology of
a member of `M`; any geometric cohomology or algebraicity. HC no distance; AV milestone no
distance.
-/

noncomputable section
attribute [local instance 100] LieRing.ofAssociativeRing
attribute [local instance] HodgeLean.Foundations.SchurWeyl.dualAddCommGroup

namespace HodgeLean.Foundations

open WeilPower SchurWeyl
open scoped TensorProduct

section General

variable {V : Type*} [AddCommGroup V] [Module ℚ V] [FiniteDimensional ℚ V]
  {H : ℤ × ℤ → Submodule ℂ (ℂ ⊗[ℚ] V)} {hH : DirectSum.IsInternal H}

/-- A finite mixed list consists of Hodge tensors exactly when the grading operator lies in its
complexified stabilizer. Forward: `spec_hodgeLieAlgebra_le_mixedTensorStabilizer` and
`gradingOperator_mem_span_hodgeLieAlgebra`; backward: minimality `hodgeLieAlgebra_le` applied to
the rational Lie subalgebra `⨅ᵢ lieAnnihilator (t i)`.
Source: Deligne, *Hodge cycles on abelian varieties*, LNM 900 (1982), §2; Moonen,
*An introduction to Mumford–Tate groups* (2004), §1–2 (the Hodge group is the smallest
`ℚ`-subgroup through which `h(U(1))` factors). -/
theorem spec_hodge_iff_gradingOperator_mem_mixedTensorStabilizer {n : ℕ}
    (t : Fin n → BoundedTensor V) :
    (∀ i, (t i).2 ∈
      LieModule.maxTrivSubmodule ℚ (hodgeLieAlgebra H hH) (MixedTensorOfType V (t i).1)) ↔
      gradingOperator H hH ∈ mixedTensorStabilizer t :=
  spec_hodge_iff_gradingOperator_mem_mixedTensorStabilizer_aux t

example {n : ℕ}
    (t : Fin n → BoundedTensor V) :
    (∀ i, (t i).2 ∈
      LieModule.maxTrivSubmodule ℚ (hodgeLieAlgebra H hH) (MixedTensorOfType V (t i).1)) ↔
      gradingOperator H hH ∈ mixedTensorStabilizer t :=
  spec_hodge_iff_gradingOperator_mem_mixedTensorStabilizer t

end General

section WeilTensor

/-- The Weil operator, the polarization and the Weil tensor cut out exactly `complexSU`: an
endomorphism commuting with `J` acts on the `K`-determinant by minus its `K`-trace, so killing
`w` adds the trace condition to the unitary Lie algebra `gl₆` of `hsuWeilPair`.
Source: van Geemen, *An introduction to the Hodge conjecture for abelian varieties*, §6;
Moonen–Zarhin, *Weil classes on abelian varieties*, J. reine angew. Math. 496 (1998), §2;
`mem_complexSU`. -/
theorem spec_mixedTensorStabilizer_hsuWeilTriple :
    mixedTensorStabilizer hsuWeilTriple =
      (complexSU hsuE spec_hsuE_nondegenerate hsuJ spec_hsuJ_sq
        spec_hsuE_skew).toSubmodule :=
  spec_mixedTensorStabilizer_hsuWeilTriple_aux

example :
    mixedTensorStabilizer hsuWeilTriple =
      (complexSU hsuE spec_hsuE_nondegenerate hsuJ spec_hsuJ_sq
        spec_hsuE_skew).toSubmodule :=
  spec_mixedTensorStabilizer_hsuWeilTriple

/-- The stabilizer of `[J, E, w]` has dimension `35 = dim sl₆`.
Source: `spec_mixedTensorStabilizer_hsuWeilTriple` with `spec_finrank_hsu_complexSU`. -/
theorem spec_finrank_hsuWeilTriple :
    Module.finrank ℂ (mixedTensorStabilizer hsuWeilTriple) = 35 :=
  spec_finrank_hsuWeilTriple_aux

example :
    Module.finrank ℂ (mixedTensorStabilizer hsuWeilTriple) = 35 :=
  spec_finrank_hsuWeilTriple

/-- Falsification check: replacing the Weil tensor by the real part `E(·, J·)` of the Hermitian
form leaves the stabilizer at dimension `36` (`gl₆`), so that tensor does not supply the trace
condition.
Source: Moonen, *An introduction to Mumford–Tate groups* (2004), §2 (the unitary group fixes its
Hermitian form); `spec_finrank_hsuWeilPair`. -/
theorem spec_finrank_hsuRosatiTriple :
    Module.finrank ℂ (mixedTensorStabilizer hsuRosatiTriple) = 36 :=
  spec_finrank_hsuRosatiTriple_aux

example :
    Module.finrank ℂ (mixedTensorStabilizer hsuRosatiTriple) = 36 :=
  spec_finrank_hsuRosatiTriple

end WeilTensor

section CMHodge

/-- The explicit decomposition is internal: the twelve vectors `f_k`, `f̄_k` form a basis of
`ℂ¹²` (in block `k`, `det [[ε√-3, -ε√-3], [1, 1]] = 2ε√-3 ≠ 0`).
Source: Deligne, *Théorie de Hodge II* (1971), §2.1; linear algebra blockwise. -/
theorem spec_hsuCMHodge_isInternal : DirectSum.IsInternal hsuCMHodge :=
  spec_hsuCMHodge_isInternal_aux

example : DirectSum.IsInternal hsuCMHodge :=
  spec_hsuCMHodge_isInternal

/-- The decomposition is pure of weight one.
Source: the definition of `hsuCMHodge`; Deligne, *Théorie de Hodge II* (1971), §2.1. -/
theorem spec_hsuCMHodge_pure : ∀ p q : ℤ, p + q ≠ 1 → hsuCMHodge (p, q) = ⊥ :=
  spec_hsuCMHodge_pure_aux

example : ∀ p q : ℤ, p + q ≠ 1 → hsuCMHodge (p, q) = ⊥ :=
  spec_hsuCMHodge_pure

/-- Conjugation symmetry: complex conjugation maps `H^{p,q}` to `H^{q,p}`.
Source: `conj_root` (`f̄_k` is the conjugate of `f_k`); Deligne, *Théorie de Hodge II* (1971),
§2.1. -/
theorem spec_hsuCMHodge_conj :
    ∀ p q : ℤ, ∀ x ∈ hsuCMHodge (p, q),
      complexConj (Fin 12 → ℚ) x ∈ hsuCMHodge (q, p) :=
  spec_hsuCMHodge_conj_aux

example :
    ∀ p q : ℤ, ∀ x ∈ hsuCMHodge (p, q),
      complexConj (Fin 12 → ℚ) x ∈ hsuCMHodge (q, p) :=
  spec_hsuCMHodge_conj

/-- Every piece is stable under `J_ℂ`: the `K`-action is by morphisms of Hodge structures.
Source: each `f_k`, `f̄_k` is a `J_ℂ`-eigenvector; van Geemen, *An introduction to the Hodge
conjecture for abelian varieties*, §5. -/
theorem spec_hsuCMHodge_J :
    ∀ pq : ℤ × ℤ, ∀ x ∈ hsuCMHodge pq, hsuJ.baseChange ℂ x ∈ hsuCMHodge pq :=
  spec_hsuCMHodge_J_aux

example :
    ∀ pq : ℤ × ℤ, ∀ x ∈ hsuCMHodge pq, hsuJ.baseChange ℂ x ∈ hsuCMHodge pq :=
  spec_hsuCMHodge_J

/-- The structure is of Weil type: `H^{1,0}` meets each `J_ℂ`-eigenspace in dimension `3`.
Source: `f₃, f₄, f₅` have eigenvalue `√-3` and `f₀, f₁, f₂` have `-√-3`; van Geemen, *An
introduction to the Hodge conjecture for abelian varieties*, §5 (Weil type `(3, 3)`). -/
theorem spec_hsuCMHodge_weilType :
    Module.finrank ℂ ↥(hsuCMHodge (1, 0) ⊓ Module.End.eigenspace (hsuJ.baseChange ℂ) root) = 3 ∧
      Module.finrank ℂ
        ↥(hsuCMHodge (1, 0) ⊓ Module.End.eigenspace (hsuJ.baseChange ℂ) (-root)) = 3 :=
  spec_hsuCMHodge_weilType_aux

example :
    Module.finrank ℂ ↥(hsuCMHodge (1, 0) ⊓ Module.End.eigenspace (hsuJ.baseChange ℂ) root) = 3 ∧
      Module.finrank ℂ
        ↥(hsuCMHodge (1, 0) ⊓ Module.End.eigenspace (hsuJ.baseChange ℂ) (-root)) = 3 :=
  spec_hsuCMHodge_weilType

/-- First Riemann relation: `H^{1,0}` is isotropic for the complexified polarization.
Source: Birkenhake–Lange, *Complex Abelian Varieties*, 2nd ed., §4.2; distinct blocks are
`E`-orthogonal and each block contributes one vector. -/
theorem spec_hsuCMHodge_isotropic :
    ∀ x ∈ hsuCMHodge (1, 0), ∀ y ∈ hsuCMHodge (1, 0), hsuE.baseChange ℂ x y = 0 :=
  spec_hsuCMHodge_isotropic_aux

example :
    ∀ x ∈ hsuCMHodge (1, 0), ∀ y ∈ hsuCMHodge (1, 0), hsuE.baseChange ℂ x y = 0 :=
  spec_hsuCMHodge_isotropic

/-- Second Riemann relation: `i E(x, x̄) > 0` for nonzero `x ∈ H^{1,0}`. In the basis `f_k` it is
`∑ₖ |c_k|² · 2√3 |hsuWeights k|`; the sign choice `hsuPeriodSign` is what makes it positive.
Source: Birkenhake–Lange, *Complex Abelian Varieties*, 2nd ed., §4.2; `spec_hsuE_hermitian_diag`. -/
theorem spec_hsuCMHodge_positive :
    ∀ x ∈ hsuCMHodge (1, 0), x ≠ 0 →
      0 < (Complex.I * hsuE.baseChange ℂ x (complexConj (Fin 12 → ℚ) x)).re :=
  spec_hsuCMHodge_positive_aux

example :
    ∀ x ∈ hsuCMHodge (1, 0), x ≠ 0 →
      0 < (Complex.I * hsuE.baseChange ℂ x (complexConj (Fin 12 → ℚ) x)).re :=
  spec_hsuCMHodge_positive

/-- The grading operator of the CM structure is `(√3)⁻¹ T_ℂ` for the rational operator
`T = hsuCMTorus`: it acts by `i` on each `f_k` and by `-i` on each `f̄_k`, as `ε_k J / √3` does.
Source: `gradingOperator_apply_of_mem`; `gradingOperator_complexStructureHodge` for one block. -/
theorem spec_hsuCMHodge_gradingOperator_eq :
    gradingOperator hsuCMHodge spec_hsuCMHodge_isInternal =
      ((Real.sqrt 3 : ℂ)⁻¹) • hsuCMTorus.baseChange ℂ :=
  spec_hsuCMHodge_gradingOperator_eq_aux

example :
    gradingOperator hsuCMHodge spec_hsuCMHodge_isInternal =
      ((Real.sqrt 3 : ℂ)⁻¹) • hsuCMTorus.baseChange ℂ :=
  spec_hsuCMHodge_gradingOperator_eq

/-- The grading operator of the CM structure lies in `complexSU`: it commutes with `J_ℂ`, is
`E`-skew by the first Riemann relation, and has trace `3i - 3i = 0` on the `√-3`-eigenspace.
Source: van Geemen, *An introduction to the Hodge conjecture for abelian varieties*, §5–6;
`mem_complexSU`. -/
theorem spec_hsuCMHodge_gradingOperator_mem_complexSU :
    gradingOperator hsuCMHodge spec_hsuCMHodge_isInternal ∈
      complexSU hsuE spec_hsuE_nondegenerate hsuJ spec_hsuJ_sq spec_hsuE_skew :=
  spec_hsuCMHodge_gradingOperator_mem_complexSU_aux

example :
    gradingOperator hsuCMHodge spec_hsuCMHodge_isInternal ∈
      complexSU hsuE spec_hsuE_nondegenerate hsuJ spec_hsuJ_sq spec_hsuE_skew :=
  spec_hsuCMHodge_gradingOperator_mem_complexSU

/-- `J`, `E` and the Weil tensor `w` are Hodge tensors for the CM structure.
Source: `spec_hodge_iff_gradingOperator_mem_mixedTensorStabilizer`,
`spec_mixedTensorStabilizer_hsuWeilTriple`, `spec_hsuCMHodge_gradingOperator_mem_complexSU`;
van Geemen, §6 (Weil classes are Hodge on every Weil-type structure). -/
theorem spec_hsuWeilTriple_hodge_hsuCMHodge :
    ∀ i, (hsuWeilTriple i).2 ∈
      LieModule.maxTrivSubmodule ℚ (hodgeLieAlgebra hsuCMHodge spec_hsuCMHodge_isInternal)
        (MixedTensorOfType (Fin 12 → ℚ) (hsuWeilTriple i).1) :=
  spec_hsuWeilTriple_hodge_hsuCMHodge_aux

example :
    ∀ i, (hsuWeilTriple i).2 ∈
      LieModule.maxTrivSubmodule ℚ (hodgeLieAlgebra hsuCMHodge spec_hsuCMHodge_isInternal)
        (MixedTensorOfType (Fin 12 → ℚ) (hsuWeilTriple i).1) :=
  spec_hsuWeilTriple_hodge_hsuCMHodge

/-- The Hodge Lie algebra of the CM structure is the line `ℚ ∙ T`: a one-dimensional torus, as
for a CM point.
Source: `hodgeLieAlgebra_complexStructureHodge` (same argument); Moonen, *An introduction to
Mumford–Tate groups* (2004), §1 (a CM Hodge structure has a commutative Mumford–Tate group). -/
theorem spec_hodgeLieAlgebra_hsuCMHodge :
    (hodgeLieAlgebra hsuCMHodge spec_hsuCMHodge_isInternal).toSubmodule = ℚ ∙ hsuCMTorus :=
  spec_hodgeLieAlgebra_hsuCMHodge_aux

example :
    (hodgeLieAlgebra hsuCMHodge spec_hsuCMHodge_isInternal).toSubmodule = ℚ ∙ hsuCMTorus :=
  spec_hodgeLieAlgebra_hsuCMHodge

/-- Falsification check: for the explicit CM structure the Hodge-group equality of
`F1575MemberHodgeGroupIsSU`'s shape fails (dimension `1` against `35`). Weil type and a
polarization alone do not give `hSU`.
Source: `spec_hodgeLieAlgebra_hsuCMHodge`, `spec_finrank_hsu_complexSU`; Moonen, *An
introduction to Mumford–Tate groups* (2004), §2. -/
theorem spec_hsuCMHodge_hSU_fails :
    complexSpan (hodgeLieAlgebra hsuCMHodge spec_hsuCMHodge_isInternal).toSubmodule ≠
      (complexSU hsuE spec_hsuE_nondegenerate hsuJ spec_hsuJ_sq spec_hsuE_skew).toSubmodule :=
  spec_hsuCMHodge_hSU_fails_aux

example :
    complexSpan (hodgeLieAlgebra hsuCMHodge spec_hsuCMHodge_isInternal).toSubmodule ≠
      (complexSU hsuE spec_hsuE_nondegenerate hsuJ spec_hsuJ_sq spec_hsuE_skew).toSubmodule :=
  spec_hsuCMHodge_hSU_fails

end CMHodge

section Assembly

variable {H : ℤ × ℤ → Submodule ℂ (ℂ ⊗[ℚ] (Fin 12 → ℚ))} {hH : DirectSum.IsInternal H}

/-- The implication from `J`, `E`, `w` being Hodge tensors of a structure on `ℚ¹²` to the
inclusion of its complexified Hodge Lie algebra in `complexSU`.
Source: `spec_hodgeLieAlgebra_le_mixedTensorStabilizer`,
`spec_mixedTensorStabilizer_hsuWeilTriple`; van Geemen, §6. -/
theorem spec_hsu_hodgeLieAlgebra_le_complexSU
    (ht : ∀ i, (hsuWeilTriple i).2 ∈ LieModule.maxTrivSubmodule ℚ (hodgeLieAlgebra H hH)
      (MixedTensorOfType (Fin 12 → ℚ) (hsuWeilTriple i).1)) :
    complexSpan (hodgeLieAlgebra H hH).toSubmodule ≤
      (complexSU hsuE spec_hsuE_nondegenerate hsuJ spec_hsuJ_sq spec_hsuE_skew).toSubmodule :=
  spec_hsu_hodgeLieAlgebra_le_complexSU_aux ht

example
    (ht : ∀ i, (hsuWeilTriple i).2 ∈ LieModule.maxTrivSubmodule ℚ (hodgeLieAlgebra H hH)
      (MixedTensorOfType (Fin 12 → ℚ) (hsuWeilTriple i).1)) :
    complexSpan (hodgeLieAlgebra H hH).toSubmodule ≤
      (complexSU hsuE spec_hsuE_nondegenerate hsuJ spec_hsuJ_sq spec_hsuE_skew).toSubmodule :=
  spec_hsu_hodgeLieAlgebra_le_complexSU ht

/-- The implication from `J`, `E`, `w` being Hodge tensors and explicit spanning elements of
`complexSU` lying in the complexified Hodge Lie algebra to the equality of
`F1575MemberHodgeGroupIsSU`'s shape for a structure on `ℚ¹²`. The generator hypothesis is the
open input; `spec_hsuCMHodge_hSU_fails` shows it can fail.
Source: `spec_hSU_of_mixedTensorStabilizer_and_generators`,
`spec_mixedTensorStabilizer_hsuWeilTriple`; van Geemen, *An introduction to the Hodge conjecture
for abelian varieties*, §5. -/
theorem spec_hsu_hSU_of_weilTriple_and_generators {m : ℕ}
    (g : Fin m → Module.End ℂ (ℂ ⊗[ℚ] (Fin 12 → ℚ)))
    (ht : ∀ i, (hsuWeilTriple i).2 ∈ LieModule.maxTrivSubmodule ℚ (hodgeLieAlgebra H hH)
      (MixedTensorOfType (Fin 12 → ℚ) (hsuWeilTriple i).1))
    (hgenerate : (complexSU hsuE spec_hsuE_nondegenerate hsuJ spec_hsuJ_sq
      spec_hsuE_skew).toSubmodule ≤ Submodule.span ℂ (Set.range g))
    (hg : ∀ i, g i ∈ complexSpan (hodgeLieAlgebra H hH).toSubmodule) :
    complexSpan (hodgeLieAlgebra H hH).toSubmodule =
      (complexSU hsuE spec_hsuE_nondegenerate hsuJ spec_hsuJ_sq spec_hsuE_skew).toSubmodule :=
  spec_hsu_hSU_of_weilTriple_and_generators_aux g ht hgenerate hg

example {m : ℕ}
    (g : Fin m → Module.End ℂ (ℂ ⊗[ℚ] (Fin 12 → ℚ)))
    (ht : ∀ i, (hsuWeilTriple i).2 ∈ LieModule.maxTrivSubmodule ℚ (hodgeLieAlgebra H hH)
      (MixedTensorOfType (Fin 12 → ℚ) (hsuWeilTriple i).1))
    (hgenerate : (complexSU hsuE spec_hsuE_nondegenerate hsuJ spec_hsuJ_sq
      spec_hsuE_skew).toSubmodule ≤ Submodule.span ℂ (Set.range g))
    (hg : ∀ i, g i ∈ complexSpan (hodgeLieAlgebra H hH).toSubmodule) :
    complexSpan (hodgeLieAlgebra H hH).toSubmodule =
      (complexSU hsuE spec_hsuE_nondegenerate hsuJ spec_hsuJ_sq spec_hsuE_skew).toSubmodule :=
  spec_hsu_hSU_of_weilTriple_and_generators g ht hgenerate hg

end Assembly

end HodgeLean.Foundations
