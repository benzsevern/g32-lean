import HodgeLean.Foundations.EQWCoreProofs

/-!
# The representation-theoretic core of EQW, stage 1 (FROZEN SPEC)

Stage 1 of formalizing F-1770 (EQW): for an abelian variety of Weil type for an imaginary
quadratic `K`, of dimension 6 or 8, balanced signature and `End⁰(A) = K`, `Hg(A) = SU(V, h)`.
This stage works with Lie algebras over `ℚ` and `ℂ` acting on `V` (`hodgeLieAlgebra`,
`complexSU`), never with algebraic groups or abelian varieties.

It claims:

* bridge, linear part: the rational commutant of the Hodge Lie algebra is the algebra of
  endomorphisms of the rational Hodge structure;
* the rational special unitary Lie algebra `weilSU E J`, for `J² = -d` with any `d > 0`, is cut
  out by rational equations, and for `d = 3` it is a rational form of `complexSU`;
* part (a): balance puts the Hodge Lie algebra inside `weilSU E J`; exact commutant `ℚ[J]`
  forces trivial centre; the implication from reductivity to trivial radical;
* part (c): exact commutant `ℚ[J]` excludes every nonzero `L`-map `V₊ → V₋`;
* part (d), Lemma TENSOR in its finite linear-algebra form: two active tensor factors give three
  eigenvalues, so under `C² = -1` one factor is idle;
* the assembly, as an implication from exact commutant `ℚ[J]` (bridge binder), reductivity of
  the Hodge Lie algebra, and the classification binder `EQWClassification` (parts (b) and the
  descent half of (d), dimensions `12` and `16`, `K = ℚ(√-3)`), to the equality of
  `F1575MemberHodgeGroupIsSU`'s shape;
* falsification: for the stage-3 CM structure `hsuCMHodge`, where `hSU` fails, the commutant is
  not `ℚ[J]`.

It does not claim: the classification binder (the minuscule classification is absent from
Mathlib); the descent of idle ideals to `ℚ`; the reductivity of the Hodge Lie algebra; the
geometric half of the bridge (`End_HS(H¹(A, ℚ)) = End⁰(A)`); the assembly for `K ≠ ℚ(√-3)`
(`complexSU` is defined only for `J² = -3`); any statement in dimensions other than `12` and
`16` beyond the dimension-free linear algebra lemmas, which are not EQW claims; any genericity,
realization by an abelian variety, geometric cohomology or algebraicity. HC no distance; AV
milestone no distance.
-/

noncomputable section
attribute [local instance 100] LieRing.ofAssociativeRing

namespace HodgeLean.Foundations

open WeilPower
open scoped TensorProduct

section Bridge

variable {V : Type*} [AddCommGroup V] [Module ℚ V] [FiniteDimensional ℚ V]
  {H : ℤ × ℤ → Submodule ℂ (ℂ ⊗[ℚ] V)} {hH : DirectSum.IsInternal H}

/-- **Bridge, linear part.** A rational endomorphism commutes with the Hodge Lie algebra exactly
when its base change commutes with the grading operator, i.e. when it is an endomorphism of the
rational Hodge structure. (`⇒`: the grading operator lies in the complexified Hodge Lie algebra;
`⇐`: minimality `hodgeLieAlgebra_le` applied to the rational centralizer of `T`, whose
complexification is the centralizer of `T_ℂ`.) The remaining geometric half of the bridge,
`End_HS(H¹(A, ℚ)) = End⁰(A)`, is not stated here.
Source: Moonen, *An introduction to Mumford–Tate groups* (2004), §1–2 (the endomorphisms of a
Hodge structure are the invariants of its Mumford–Tate group); `hodgeLieAlgebra_le`,
`gradingOperator_mem_span_hodgeLieAlgebra`. -/
theorem spec_eqw_mem_centralizer_hodgeLieAlgebra_iff (T : Module.End ℚ V) :
    T ∈ Subalgebra.centralizer ℚ (hodgeLieAlgebra H hH : Set (Module.End ℚ V)) ↔
      T.baseChange ℂ * gradingOperator H hH = gradingOperator H hH * T.baseChange ℂ :=
  spec_eqw_mem_centralizer_hodgeLieAlgebra_iff_aux T

example (T : Module.End ℚ V) :
    T ∈ Subalgebra.centralizer ℚ (hodgeLieAlgebra H hH : Set (Module.End ℚ V)) ↔
      T.baseChange ℂ * gradingOperator H hH = gradingOperator H hH * T.baseChange ℂ :=
  spec_eqw_mem_centralizer_hodgeLieAlgebra_iff T

/-- For a decomposition supported on `(1, 0)` and `(0, 1)` (weight one), the grading operator
squares to `-1`: it acts by `i` and `-i`.
Source: `gradingOperator_apply_of_mem`; Deligne, *Théorie de Hodge II* (1971), §2.1. -/
theorem spec_eqw_gradingOperator_mul_self
    (hsupp : ∀ pq : ℤ × ℤ, pq ≠ (1, 0) → pq ≠ (0, 1) → H pq = ⊥) :
    gradingOperator H hH * gradingOperator H hH = -1 :=
  spec_eqw_gradingOperator_mul_self_aux hsupp

example
    (hsupp : ∀ pq : ℤ × ℤ, pq ≠ (1, 0) → pq ≠ (0, 1) → H pq = ⊥) :
    gradingOperator H hH * gradingOperator H hH = -1 :=
  spec_eqw_gradingOperator_mul_self hsupp

end Bridge

section WeilSU

variable {V : Type*} [AddCommGroup V] [Module ℚ V] [FiniteDimensional ℚ V]

/-- `weilSU E J` is cut out by rational linear equations, so its complexification is cut out by
the same equations over `ℂ`: commuting with `J_ℂ`, `E_ℂ`-skew, `tr c = 0`, `tr (J_ℂ c) = 0`.
Source: Bourbaki, *Algèbre*, ch. II, §5 (extension of scalars commutes with kernels);
`ker_baseChange_eq`, `mem_complexSpan_iff`. -/
theorem spec_eqw_mem_complexSpan_weilSU_iff (E : LinearMap.BilinForm ℚ V)
    (J : Module.End ℚ V) (c : Module.End ℂ (ℂ ⊗[ℚ] V)) :
    c ∈ complexSpan (weilSU E J).toSubmodule ↔
      c * J.baseChange ℂ = J.baseChange ℂ * c ∧
      (∀ x y, E.baseChange ℂ (c x) y = -E.baseChange ℂ x (c y)) ∧
      LinearMap.trace ℂ (ℂ ⊗[ℚ] V) c = 0 ∧
      LinearMap.trace ℂ (ℂ ⊗[ℚ] V) (J.baseChange ℂ * c) = 0 :=
  spec_eqw_mem_complexSpan_weilSU_iff_aux E J c

example (E : LinearMap.BilinForm ℚ V)
    (J : Module.End ℚ V) (c : Module.End ℂ (ℂ ⊗[ℚ] V)) :
    c ∈ complexSpan (weilSU E J).toSubmodule ↔
      c * J.baseChange ℂ = J.baseChange ℂ * c ∧
      (∀ x y, E.baseChange ℂ (c x) y = -E.baseChange ℂ x (c y)) ∧
      LinearMap.trace ℂ (ℂ ⊗[ℚ] V) c = 0 ∧
      LinearMap.trace ℂ (ℂ ⊗[ℚ] V) (J.baseChange ℂ * c) = 0 :=
  spec_eqw_mem_complexSpan_weilSU_iff E J c

/-- For `K = ℚ(√-3)`, `weilSU E J` is a rational form of `complexSU`: for `c` commuting with `J_ℂ`,
`tr c = tr c₊ + tr c₋` and `tr (J_ℂ c) = √-3 (tr c₊ - tr c₋)`, so the two trace conditions say
`tr c₊ = 0`, the trace condition of `mem_complexSU`.
Source: van Geemen, *An introduction to the Hodge conjecture for abelian varieties*, §5–6;
`mem_complexSU`, `spec_eqw_mem_complexSpan_weilSU_iff`. -/
theorem spec_eqw_complexSpan_weilSU_eq_complexSU (E : LinearMap.BilinForm ℚ V)
    (hE : E.Nondegenerate) (hAlt : E.IsAlt) (J : Module.End ℚ V)
    (hJ : J.comp J = (-3 : ℚ) • LinearMap.id) (hskew : ∀ x y, E (J x) y = -E x (J y)) :
    complexSpan (weilSU E J).toSubmodule = (complexSU E hE J hJ hskew).toSubmodule :=
  spec_eqw_complexSpan_weilSU_eq_complexSU_aux E hE hAlt J hJ hskew

example (E : LinearMap.BilinForm ℚ V)
    (hE : E.Nondegenerate) (hAlt : E.IsAlt) (J : Module.End ℚ V)
    (hJ : J.comp J = (-3 : ℚ) • LinearMap.id) (hskew : ∀ x y, E (J x) y = -E x (J y)) :
    complexSpan (weilSU E J).toSubmodule = (complexSU E hE J hJ hskew).toSubmodule :=
  spec_eqw_complexSpan_weilSU_eq_complexSU E hE hAlt J hJ hskew

variable {H : ℤ × ℤ → Submodule ℂ (ℂ ⊗[ℚ] V)} {hH : DirectSum.IsInternal H}

/-- **Balance gives determinant one** (F-1770 part (a), first half). For a weight-one decomposition
on which `J_ℂ` acts by Hodge endomorphisms, with `H^{1,0}` and `H^{0,1}` isotropic for `E_ℂ`, and
balanced on both eigenspaces `V_±` of `J_ℂ` (`dim H^{1,0} ∩ V_± = dim H^{0,1} ∩ V_±`), the grading
operator satisfies the equations of `spec_eqw_mem_complexSpan_weilSU_iff`, so the Hodge Lie
algebra lies in `weilSU E J`. Here `J² = -d`, `d > 0`, `μ = √-d`: every imaginary quadratic `K`.
Source: F-1770 part (a); van Geemen, *An introduction to the Hodge conjecture for abelian
varieties*, §5–6 (on a Weil-type structure the Hodge group lies in `SU(V, h)`);
`hodgeLieAlgebra_le`. -/
theorem spec_eqw_hodgeLieAlgebra_le_weilSU {d : ℚ} (hd : 0 < d) (μ : ℂ)
    (hμ : μ * μ = -(d : ℂ)) (E : LinearMap.BilinForm ℚ V) (J : Module.End ℚ V)
    (hJ : J.comp J = (-d) • LinearMap.id)
    (hsupp : ∀ pq : ℤ × ℤ, pq ≠ (1, 0) → pq ≠ (0, 1) → H pq = ⊥)
    (hJH : ∀ pq, ∀ x ∈ H pq, J.baseChange ℂ x ∈ H pq)
    (hiso₁₀ : ∀ x ∈ H (1, 0), ∀ y ∈ H (1, 0), E.baseChange ℂ x y = 0)
    (hiso₀₁ : ∀ x ∈ H (0, 1), ∀ y ∈ H (0, 1), E.baseChange ℂ x y = 0)
    (hbalPos : Module.finrank ℂ ↥(H (1, 0) ⊓ Module.End.eigenspace (J.baseChange ℂ) μ) =
      Module.finrank ℂ ↥(H (0, 1) ⊓ Module.End.eigenspace (J.baseChange ℂ) μ))
    (hbalNeg : Module.finrank ℂ ↥(H (1, 0) ⊓ Module.End.eigenspace (J.baseChange ℂ) (-μ)) =
      Module.finrank ℂ ↥(H (0, 1) ⊓ Module.End.eigenspace (J.baseChange ℂ) (-μ))) :
    hodgeLieAlgebra H hH ≤ weilSU E J :=
  spec_eqw_hodgeLieAlgebra_le_weilSU_aux hd μ hμ E J hJ hsupp hJH hiso₁₀ hiso₀₁ hbalPos hbalNeg

example {d : ℚ} (hd : 0 < d) (μ : ℂ)
    (hμ : μ * μ = -(d : ℂ)) (E : LinearMap.BilinForm ℚ V) (J : Module.End ℚ V)
    (hJ : J.comp J = (-d) • LinearMap.id)
    (hsupp : ∀ pq : ℤ × ℤ, pq ≠ (1, 0) → pq ≠ (0, 1) → H pq = ⊥)
    (hJH : ∀ pq, ∀ x ∈ H pq, J.baseChange ℂ x ∈ H pq)
    (hiso₁₀ : ∀ x ∈ H (1, 0), ∀ y ∈ H (1, 0), E.baseChange ℂ x y = 0)
    (hiso₀₁ : ∀ x ∈ H (0, 1), ∀ y ∈ H (0, 1), E.baseChange ℂ x y = 0)
    (hbalPos : Module.finrank ℂ ↥(H (1, 0) ⊓ Module.End.eigenspace (J.baseChange ℂ) μ) =
      Module.finrank ℂ ↥(H (0, 1) ⊓ Module.End.eigenspace (J.baseChange ℂ) μ))
    (hbalNeg : Module.finrank ℂ ↥(H (1, 0) ⊓ Module.End.eigenspace (J.baseChange ℂ) (-μ)) =
      Module.finrank ℂ ↥(H (0, 1) ⊓ Module.End.eigenspace (J.baseChange ℂ) (-μ))) :
    hodgeLieAlgebra H hH ≤ weilSU E J :=
  spec_eqw_hodgeLieAlgebra_le_weilSU hd μ hμ E J hJ hsupp hJH hiso₁₀ hiso₀₁ hbalPos hbalNeg

end WeilSU

section PartsAC

variable {V : Type*} [AddCommGroup V] [Module ℚ V] [FiniteDimensional ℚ V]

/-- **Exact `End` kills the centre** (F-1770 part (a), second half). If `L ≤ weilSU E J` and the
rational commutant of `L` is exactly `K = ℚ[J]`, then `L` has trivial centre: a central element
lies in `K ∩ 𝔰𝔲 = 0` (`a + bJ` is `E`-skew only for `a = 0`, and `tr (J · bJ) = -2nbd`).
Source: F-1770 part (a) (the connected centre is scalar, hence finite inside `SU`); Moonen,
*An introduction to Mumford–Tate groups* (2004), §2. -/
theorem spec_eqw_center_eq_bot
    (hdim : Module.finrank ℚ V = 12 ∨ Module.finrank ℚ V = 16) {d : ℚ} (hd : 0 < d)
    (E : LinearMap.BilinForm ℚ V) (hE : E.Nondegenerate) (J : Module.End ℚ V)
    (hJ : J.comp J = (-d) • LinearMap.id) (hskew : ∀ x y, E (J x) y = -E x (J y))
    (L : LieSubalgebra ℚ (Module.End ℚ V)) (hL : L ≤ weilSU E J)
    (hcomm : Subalgebra.centralizer ℚ (L : Set (Module.End ℚ V)) = Algebra.adjoin ℚ {J}) :
    LieAlgebra.center ℚ L = ⊥ :=
  spec_eqw_center_eq_bot_aux hdim hd E hE J hJ hskew L hL hcomm

example
    (hdim : Module.finrank ℚ V = 12 ∨ Module.finrank ℚ V = 16) {d : ℚ} (hd : 0 < d)
    (E : LinearMap.BilinForm ℚ V) (hE : E.Nondegenerate) (J : Module.End ℚ V)
    (hJ : J.comp J = (-d) • LinearMap.id) (hskew : ∀ x y, E (J x) y = -E x (J y))
    (L : LieSubalgebra ℚ (Module.End ℚ V)) (hL : L ≤ weilSU E J)
    (hcomm : Subalgebra.centralizer ℚ (L : Set (Module.End ℚ V)) = Algebra.adjoin ℚ {J}) :
    LieAlgebra.center ℚ L = ⊥ :=
  spec_eqw_center_eq_bot hdim hd E hE J hJ hskew L hL hcomm

/-- The implication from reductivity (`radical = centre`) and exact commutant to semisimplicity
(trivial radical; by Cartan's criterion, `LieAlgebra.HasTrivialRadical.instIsKilling`, the
Killing form is then nondegenerate). The reductivity of the Hodge Lie algebra is an explicit
binder: it is not in the repository.
Source: F-1770 part (a); Bourbaki, *Groupes et algèbres de Lie*, ch. I, §6.4 (reductive means
radical equals centre); Deligne, *Variétés de Shimura* (1979), §1.1 (Hodge groups of polarizable
structures are reductive). -/
theorem spec_eqw_hasTrivialRadical
    (hdim : Module.finrank ℚ V = 12 ∨ Module.finrank ℚ V = 16) {d : ℚ} (hd : 0 < d)
    (E : LinearMap.BilinForm ℚ V) (hE : E.Nondegenerate) (J : Module.End ℚ V)
    (hJ : J.comp J = (-d) • LinearMap.id) (hskew : ∀ x y, E (J x) y = -E x (J y))
    (L : LieSubalgebra ℚ (Module.End ℚ V)) (hL : L ≤ weilSU E J)
    (hcomm : Subalgebra.centralizer ℚ (L : Set (Module.End ℚ V)) = Algebra.adjoin ℚ {J})
    (hred : LieAlgebra.radical ℚ L = LieAlgebra.center ℚ L) :
    LieAlgebra.HasTrivialRadical ℚ L :=
  spec_eqw_hasTrivialRadical_aux hdim hd E hE J hJ hskew L hL hcomm hred

example
    (hdim : Module.finrank ℚ V = 12 ∨ Module.finrank ℚ V = 16) {d : ℚ} (hd : 0 < d)
    (E : LinearMap.BilinForm ℚ V) (hE : E.Nondegenerate) (J : Module.End ℚ V)
    (hJ : J.comp J = (-d) • LinearMap.id) (hskew : ∀ x y, E (J x) y = -E x (J y))
    (L : LieSubalgebra ℚ (Module.End ℚ V)) (hL : L ≤ weilSU E J)
    (hcomm : Subalgebra.centralizer ℚ (L : Set (Module.End ℚ V)) = Algebra.adjoin ℚ {J})
    (hred : LieAlgebra.radical ℚ L = LieAlgebra.center ℚ L) :
    LieAlgebra.HasTrivialRadical ℚ L :=
  spec_eqw_hasTrivialRadical hdim hd E hE J hJ hskew L hL hcomm hred

/-- **Part (c).** If the rational commutant of `L` is exactly `ℚ[J]`, there is no nonzero
`L`-map `V₊ → V₋`: such a map would commute with `L_ℂ`, so it would lie in the complexified
commutant `ℂ ⊕ ℂ J_ℂ`, which acts by scalars on `V₊` and `V₋`. In particular `V₊ ≇ V₋`.
Source: F-1770 part (c) (self-duality would identify the two `K`-eigenspaces as Hodge-group
modules, contradicting the exact commutant); Bourbaki, *Algèbre*, ch. II, §5 (commutants commute
with extension of scalars). -/
theorem spec_eqw_not_hasPlusMinusIntertwiner
    (hdim : Module.finrank ℚ V = 12 ∨ Module.finrank ℚ V = 16) {d : ℚ} (hd : 0 < d)
    (J : Module.End ℚ V) (hJ : J.comp J = (-d) • LinearMap.id) (μ : ℂ)
    (hμ : μ * μ = -(d : ℂ)) (L : LieSubalgebra ℚ (Module.End ℚ V))
    (hcomm : Subalgebra.centralizer ℚ (L : Set (Module.End ℚ V)) = Algebra.adjoin ℚ {J}) :
    ¬ HasPlusMinusIntertwiner L J μ :=
  spec_eqw_not_hasPlusMinusIntertwiner_aux hdim hd J hJ μ hμ L hcomm

example
    (hdim : Module.finrank ℚ V = 12 ∨ Module.finrank ℚ V = 16) {d : ℚ} (hd : 0 < d)
    (J : Module.End ℚ V) (hJ : J.comp J = (-d) • LinearMap.id) (μ : ℂ)
    (hμ : μ * μ = -(d : ℂ)) (L : LieSubalgebra ℚ (Module.End ℚ V))
    (hcomm : Subalgebra.centralizer ℚ (L : Set (Module.End ℚ V)) = Algebra.adjoin ℚ {J}) :
    ¬ HasPlusMinusIntertwiner L J μ :=
  spec_eqw_not_hasPlusMinusIntertwiner hdim hd J hJ μ hμ L hcomm

end PartsAC

section Tensor

variable {W₁ W₂ : Type*} [AddCommGroup W₁] [Module ℂ W₁] [AddCommGroup W₂] [Module ℂ W₂]

/-- **Lemma TENSOR, counting form** (F-1770 part (d)). If `f₁` and `f₂` each have two distinct
eigenvalues, `f₁ ⊗ 1 + 1 ⊗ f₂` has three distinct eigenvalues (among `μ₁ + μ₂`, `μ₁ + ν₂`,
`ν₁ + μ₂`, `ν₁ + ν₂`, two values only would force `2 (μ₂ - ν₂) = 0`).
Source: F-1770 part (d), Lemma TENSOR; Bourbaki, *Groupes et algèbres de Lie*, ch. I, §3
(the tensor product of representations). -/
theorem spec_eqw_tensor_three_eigenvalues (f₁ : Module.End ℂ W₁) (f₂ : Module.End ℂ W₂)
    {μ₁ ν₁ μ₂ ν₂ : ℂ} (hμ₁ : f₁.HasEigenvalue μ₁) (hν₁ : f₁.HasEigenvalue ν₁) (h₁ : μ₁ ≠ ν₁)
    (hμ₂ : f₂.HasEigenvalue μ₂) (hν₂ : f₂.HasEigenvalue ν₂) (h₂ : μ₂ ≠ ν₂) :
    ∃ a b c : ℂ, a ≠ b ∧ a ≠ c ∧ b ≠ c ∧
      Module.End.HasEigenvalue
        (TensorProduct.map f₁ LinearMap.id + TensorProduct.map LinearMap.id f₂) a ∧
      Module.End.HasEigenvalue
        (TensorProduct.map f₁ LinearMap.id + TensorProduct.map LinearMap.id f₂) b ∧
      Module.End.HasEigenvalue
        (TensorProduct.map f₁ LinearMap.id + TensorProduct.map LinearMap.id f₂) c :=
  spec_eqw_tensor_three_eigenvalues_aux f₁ f₂ hμ₁ hν₁ h₁ hμ₂ hν₂ h₂

example (f₁ : Module.End ℂ W₁) (f₂ : Module.End ℂ W₂)
    {μ₁ ν₁ μ₂ ν₂ : ℂ} (hμ₁ : f₁.HasEigenvalue μ₁) (hν₁ : f₁.HasEigenvalue ν₁) (h₁ : μ₁ ≠ ν₁)
    (hμ₂ : f₂.HasEigenvalue μ₂) (hν₂ : f₂.HasEigenvalue ν₂) (h₂ : μ₂ ≠ ν₂) :
    ∃ a b c : ℂ, a ≠ b ∧ a ≠ c ∧ b ≠ c ∧
      Module.End.HasEigenvalue
        (TensorProduct.map f₁ LinearMap.id + TensorProduct.map LinearMap.id f₂) a ∧
      Module.End.HasEigenvalue
        (TensorProduct.map f₁ LinearMap.id + TensorProduct.map LinearMap.id f₂) b ∧
      Module.End.HasEigenvalue
        (TensorProduct.map f₁ LinearMap.id + TensorProduct.map LinearMap.id f₂) c :=
  spec_eqw_tensor_three_eigenvalues f₁ f₂ hμ₁ hν₁ h₁ hμ₂ hν₂ h₂

/-- **Lemma TENSOR, idle form.** If `f₁`, `f₂` are semisimple and traceless and
`f₁ ⊗ 1 + 1 ⊗ f₂` squares to `-1` (so it has at most the two eigenvalues `±i`, as the Hodge
circle does in weight one), then one of them is zero: a nonzero traceless semisimple endomorphism
has two distinct eigenvalues, and `spec_eqw_tensor_three_eigenvalues` applies.
Source: F-1770 part (d), Lemma TENSOR (two active factors give at least three eigenvalues of the
Hodge circle, so one ideal is idle). -/
theorem spec_eqw_tensor_idle [FiniteDimensional ℂ W₁] [FiniteDimensional ℂ W₂]
    (f₁ : Module.End ℂ W₁) (f₂ : Module.End ℂ W₂) (hs₁ : f₁.IsSemisimple)
    (hs₂ : f₂.IsSemisimple) (ht₁ : LinearMap.trace ℂ W₁ f₁ = 0)
    (ht₂ : LinearMap.trace ℂ W₂ f₂ = 0)
    (hsq : (TensorProduct.map f₁ LinearMap.id + TensorProduct.map LinearMap.id f₂) *
      (TensorProduct.map f₁ LinearMap.id + TensorProduct.map LinearMap.id f₂) = -1) :
    f₁ = 0 ∨ f₂ = 0 :=
  spec_eqw_tensor_idle_aux f₁ f₂ hs₁ hs₂ ht₁ ht₂ hsq

example [FiniteDimensional ℂ W₁] [FiniteDimensional ℂ W₂]
    (f₁ : Module.End ℂ W₁) (f₂ : Module.End ℂ W₂) (hs₁ : f₁.IsSemisimple)
    (hs₂ : f₂.IsSemisimple) (ht₁ : LinearMap.trace ℂ W₁ f₁ = 0)
    (ht₂ : LinearMap.trace ℂ W₂ f₂ = 0)
    (hsq : (TensorProduct.map f₁ LinearMap.id + TensorProduct.map LinearMap.id f₂) *
      (TensorProduct.map f₁ LinearMap.id + TensorProduct.map LinearMap.id f₂) = -1) :
    f₁ = 0 ∨ f₂ = 0 :=
  spec_eqw_tensor_idle f₁ f₂ hs₁ hs₂ ht₁ ht₂ hsq

end Tensor

section Assembly

variable {V : Type*} [AddCommGroup V] [Module ℚ V] [FiniteDimensional ℚ V]
  {H : ℤ × ℤ → Submodule ℂ (ℂ ⊗[ℚ] V)} {hH : DirectSum.IsInternal H}

/-- **Assembly**: the implication from exact commutant `ℚ[J]` (the bridge binder; by
`spec_eqw_mem_centralizer_hodgeLieAlgebra_iff` it says `End_HS = K`), reductivity of the Hodge
Lie algebra, and the classification binder `EQWClassification` to the equality of
`F1575MemberHodgeGroupIsSU`'s shape, for a balanced weight-one Weil-type structure on `V` of
dimension `12` or `16` with `K = ℚ(√-3)`. It composes `spec_eqw_gradingOperator_mul_self`,
`spec_eqw_hodgeLieAlgebra_le_weilSU`, `spec_eqw_hasTrivialRadical` and
`spec_eqw_not_hasPlusMinusIntertwiner`.
Source: F-1770 (EQW), refereed CORRECT (hodge-EQWR); van Geemen, *An introduction to the Hodge
conjecture for abelian varieties*, §5–6. -/
theorem spec_eqw_hSU_of_centralizer_eq
    (hdim : Module.finrank ℚ V = 12 ∨ Module.finrank ℚ V = 16)
    (E : LinearMap.BilinForm ℚ V) (hE : E.Nondegenerate) (hAlt : E.IsAlt)
    (J : Module.End ℚ V) (hJ : J.comp J = (-3 : ℚ) • LinearMap.id)
    (hskew : ∀ x y, E (J x) y = -E x (J y))
    (hsupp : ∀ pq : ℤ × ℤ, pq ≠ (1, 0) → pq ≠ (0, 1) → H pq = ⊥)
    (hJH : ∀ pq, ∀ x ∈ H pq, J.baseChange ℂ x ∈ H pq)
    (hiso₁₀ : ∀ x ∈ H (1, 0), ∀ y ∈ H (1, 0), E.baseChange ℂ x y = 0)
    (hiso₀₁ : ∀ x ∈ H (0, 1), ∀ y ∈ H (0, 1), E.baseChange ℂ x y = 0)
    (hbalPos : Module.finrank ℂ ↥(H (1, 0) ⊓ Module.End.eigenspace (J.baseChange ℂ) root) =
      Module.finrank ℂ ↥(H (0, 1) ⊓ Module.End.eigenspace (J.baseChange ℂ) root))
    (hbalNeg : Module.finrank ℂ ↥(H (1, 0) ⊓ Module.End.eigenspace (J.baseChange ℂ) (-root)) =
      Module.finrank ℂ ↥(H (0, 1) ⊓ Module.End.eigenspace (J.baseChange ℂ) (-root)))
    (hred : LieAlgebra.radical ℚ (hodgeLieAlgebra H hH) =
      LieAlgebra.center ℚ (hodgeLieAlgebra H hH))
    (hcomm : Subalgebra.centralizer ℚ (hodgeLieAlgebra H hH : Set (Module.End ℚ V)) =
      Algebra.adjoin ℚ {J})
    (hclass : EQWClassification E hE J hJ hskew) :
    complexSpan (hodgeLieAlgebra H hH).toSubmodule =
      (complexSU E hE J hJ hskew).toSubmodule :=
  spec_eqw_hSU_of_centralizer_eq_aux hdim E hE hAlt J hJ hskew hsupp hJH hiso₁₀ hiso₀₁ hbalPos hbalNeg
    hred hcomm hclass

example
    (hdim : Module.finrank ℚ V = 12 ∨ Module.finrank ℚ V = 16)
    (E : LinearMap.BilinForm ℚ V) (hE : E.Nondegenerate) (hAlt : E.IsAlt)
    (J : Module.End ℚ V) (hJ : J.comp J = (-3 : ℚ) • LinearMap.id)
    (hskew : ∀ x y, E (J x) y = -E x (J y))
    (hsupp : ∀ pq : ℤ × ℤ, pq ≠ (1, 0) → pq ≠ (0, 1) → H pq = ⊥)
    (hJH : ∀ pq, ∀ x ∈ H pq, J.baseChange ℂ x ∈ H pq)
    (hiso₁₀ : ∀ x ∈ H (1, 0), ∀ y ∈ H (1, 0), E.baseChange ℂ x y = 0)
    (hiso₀₁ : ∀ x ∈ H (0, 1), ∀ y ∈ H (0, 1), E.baseChange ℂ x y = 0)
    (hbalPos : Module.finrank ℂ ↥(H (1, 0) ⊓ Module.End.eigenspace (J.baseChange ℂ) root) =
      Module.finrank ℂ ↥(H (0, 1) ⊓ Module.End.eigenspace (J.baseChange ℂ) root))
    (hbalNeg : Module.finrank ℂ ↥(H (1, 0) ⊓ Module.End.eigenspace (J.baseChange ℂ) (-root)) =
      Module.finrank ℂ ↥(H (0, 1) ⊓ Module.End.eigenspace (J.baseChange ℂ) (-root)))
    (hred : LieAlgebra.radical ℚ (hodgeLieAlgebra H hH) =
      LieAlgebra.center ℚ (hodgeLieAlgebra H hH))
    (hcomm : Subalgebra.centralizer ℚ (hodgeLieAlgebra H hH : Set (Module.End ℚ V)) =
      Algebra.adjoin ℚ {J})
    (hclass : EQWClassification E hE J hJ hskew) :
    complexSpan (hodgeLieAlgebra H hH).toSubmodule =
      (complexSU E hE J hJ hskew).toSubmodule :=
  spec_eqw_hSU_of_centralizer_eq hdim E hE hAlt J hJ hskew hsupp hJH hiso₁₀ hiso₀₁ hbalPos hbalNeg
    hred hcomm hclass

end Assembly

section Falsification

/-- Falsification check: for the CM structure `hsuCMHodge` of stage 3, which satisfies the
Weil-type hypotheses but has `hSU` failing (`spec_hsuCMHodge_hSU_fails`), the commutant of the
Hodge Lie algebra is not `ℚ[J]`: it contains `hsuCMTorus` (`spec_hodgeLieAlgebra_hsuCMHodge`),
which is `-J` on three blocks and `J` on the other three, not of the form `a + bJ`.
Source: `spec_hodgeLieAlgebra_hsuCMHodge`; Moonen, *An introduction to Mumford–Tate groups*
(2004), §2 (a CM structure has a large commutant). -/
theorem spec_eqw_hsuCMHodge_centralizer_ne :
    Subalgebra.centralizer ℚ
        (hodgeLieAlgebra hsuCMHodge spec_hsuCMHodge_isInternal : Set (Module.End ℚ (Fin 12 → ℚ))) ≠
      Algebra.adjoin ℚ {hsuJ} :=
  spec_eqw_hsuCMHodge_centralizer_ne_aux

example :
    Subalgebra.centralizer ℚ
        (hodgeLieAlgebra hsuCMHodge spec_hsuCMHodge_isInternal : Set (Module.End ℚ (Fin 12 → ℚ))) ≠
      Algebra.adjoin ℚ {hsuJ} :=
  spec_eqw_hsuCMHodge_centralizer_ne

end Falsification

end HodgeLean.Foundations
