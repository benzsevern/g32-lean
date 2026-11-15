import HodgeLean.Foundations.PositivePolarizationProofs
import HodgeLean.Adapters.PWTheorem42
import HodgeLean.Adapters.AbelianPowerLinkGeneral

/-! # Positive polarizations and the Rosati involution (FROZEN SPEC)

Track P1. For PW v0.3, Theorem 4.2 to take a **polarization** of `A` instead of a nondegenerate
class `pol` with a Rosati binder, this file defines positivity of a class `pol ∈ H²(A; ℚ)`
(`p1_IsPolarization`, Riemann relations on `H₁ ⊗ ℝ`), the Rosati involution of `End⁰(A)` as the
adjoint for the polarization form (`p1_rosati`, which takes the nondegeneracy witness and the
witness that the adjoints lie in the image of `End⁰(A)` as arguments), and states, as
implications from `p1_IsPolarization A pol`:

1. **Nondegeneracy**: `p1_isNondegenerate_of_isPositive` (linear algebra) and
   `p1_isNondegenerate` (`IsNondegenerate (polarizationVec … pol)`).
2. **The same notion as `PolarizationPositive`**: `p1_isPolarization_iff`, and the type `(1,1)`
   consequence `p1_mem_hdg`.
3. **The Rosati involution**: the `E_ω`-adjoint of the action of every `φ ∈ End⁰(A)` is the
   action of an element of `End⁰(A)` (`p1_adjoint_mem_range`), so `p1_rosati A pol
   (p1_isNondegenerate A hP) (p1_adjoint_mem_range A hP)` is defined and acts by the adjoint
   (`p1_abelianEnd0Action_rosati`, with `p1_dualForm_adjoint`); it is `ℚ`-linear, unital,
   anti-multiplicative and involutive (`p1_rosati_add`, `p1_rosati_smul`, `p1_rosati_one`,
   `p1_rosati_mul`, `p1_rosati_rosati`, assembled in `p1_rosati_antiInvolution`); it is
   positive, `tr(φ φ') > 0` for `φ ≠ 0` (`p1_rosati_pos`, from `p1_trace_pos`).
4. **CM conjugation**: for bijective `θ : L →ₐ[ℚ] End⁰(A)` and a CM field `L`, the Rosati
   involution is complex conjugation on `L` (`p1_rosati_conj`); hence the Rosati condition of
   `pwf_theorem_4_2` (`p1_hRos`) and `IsRosatiSkew` for `u² = -d`, `d > 0` (`p1_isRosatiSkew`).
5. **The adapter**: `p1_pw_inputs` produces the `hη` and `hRos` binders of the existing PW route,
   with an `example` feeding them to `spec_g3link2_generation_cup`.

Model checks on `ℚ²` and `ℚ⁴`: `p1_isPositive_model` (satisfiable: `e₀ ∧ e₁` with the standard
complex structure), `p1_not_isPositive_model_neg` (nondegenerate, not positive),
`p1_model₄` (nondegenerate of signature `(1,1)`, not positive, and Rosati positivity fails for
an endomorphism commuting with the complex structure: the trace is `-4`).

Statements 1–4 are implications from `p1_IsPolarization` (and, for 4, from bijectivity of `θ`
and the CM hypothesis). Not claimed: that any specific `A` has a polarization (an ample class is
not constructed here); that `pol` is integral or is the class of a line bundle; simplicity of
`A`. HC no distance; AV milestone no distance.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint TopologicalSpace Module
open scoped TensorProduct
open HodgeLean.RealDefs HodgeLean.Adapters HodgeLean.Foundations.Symplectic NumberField

namespace HodgeLean.Foundations

section Linear

variable {V : Type*} [AddCommGroup V] [Module ℚ V] [Module.Finite ℚ V]

/-- **Positivity implies nondegeneracy.** If `ω` is positive for some `I` (`p1_IsPositive`), the
contraction `contract ω : V^∨ → V` is bijective. Over `ℝ`, `c (φ) = 0` gives
`φ (c (φ ∘ I)) = -(φ ∘ I) (c φ) = 0` by alternation of `B_ω`, so `φ = 0`; injectivity descends
to `ℚ`, and `dim V^∨ = dim V`.
Source: Birkenhake–Lange, *Complex Abelian Varieties*, 2nd ed., §4.1 (the Riemann form of a
positive definite Hermitian form is nondegenerate); Bourbaki, *Algèbre*, ch. IX, §1. -/
theorem p1_isNondegenerate_of_isPositive {ω : ⋀[ℚ]^2 V}
    {I : ℝ ⊗[ℚ] V →ₗ[ℝ] ℝ ⊗[ℚ] V} (h : p1_IsPositive ω I) : IsNondegenerate ω :=
  p1_isNondegenerate_of_isPositive_aux h

/-- **The adjoint is the adjoint.** For nondegenerate `ω`,
`E_ω (f x, y) = E_ω (x, p1_adjoint ω hω f y)`.
Source: Bourbaki, *Algèbre*, ch. IX, §1 (adjoint for a nondegenerate bilinear form);
`Symplectic.dualForm_apply`. -/
theorem p1_dualForm_adjoint {ω : ⋀[ℚ]^2 V} (hω : IsNondegenerate ω)
    (f : Module.End ℚ V) (x y : V) :
    dualForm hω (f x) y = dualForm hω x (p1_adjoint ω hω f y) :=
  p1_dualForm_adjoint_aux hω f x y

/-- **Positivity of the adjoint trace form.** If `ω` is positive for a complex structure `I`
(`I² = -1`) and `f` commutes with `I`, then `tr(f ∘ f†) > 0` for `f ≠ 0`, `f†` the `E_ω`-adjoint:
`S(x, y) = E_ω(x, I y)` is a positive definite inner product on `V ⊗ ℝ`, `f†` is the
`S`-adjoint of `f`, and `tr(f f†) = ‖f‖²_S`. The adjoint is taken for the nondegeneracy witness
`p1_isNondegenerate_of_isPositive h`. The hypothesis on `f` is needed: for `f`
anticommuting with `I` the trace is negative.
Source: Mumford, *Abelian Varieties*, §21, Theorem 1 (positivity of the Rosati involution);
Birkenhake–Lange, *Complex Abelian Varieties*, 2nd ed., Theorem 5.1.8. -/
theorem p1_trace_pos {ω : ⋀[ℚ]^2 V} {I : ℝ ⊗[ℚ] V →ₗ[ℝ] ℝ ⊗[ℚ] V}
    (h : p1_IsPositive ω I) (hI : I ∘ₗ I = -LinearMap.id) {f : Module.End ℚ V}
    (hf : f.baseChange ℝ ∘ₗ I = I ∘ₗ f.baseChange ℝ) (hf0 : f ≠ 0) :
    0 < LinearMap.trace ℚ V (f ∘ₗ p1_adjoint ω (p1_isNondegenerate_of_isPositive h) f) :=
  p1_trace_pos_aux h hI hf hf0

/-- The identity commutes with every `I`: `tr(id ∘ id†) > 0` on a nonzero space. -/
example {ω : ⋀[ℚ]^2 V} {I : ℝ ⊗[ℚ] V →ₗ[ℝ] ℝ ⊗[ℚ] V} (h : p1_IsPositive ω I)
    (hI : I ∘ₗ I = -LinearMap.id) [Nontrivial V] :
    0 < LinearMap.trace ℚ V
      (LinearMap.id ∘ₗ p1_adjoint ω (p1_isNondegenerate_of_isPositive h) LinearMap.id) :=
  p1_trace_pos h hI (by rw [LinearMap.baseChange_id, LinearMap.id_comp, LinearMap.comp_id])
    (fun h0 => by
      obtain ⟨v, hv⟩ := exists_ne (0 : V)
      exact hv (by simpa using LinearMap.congr_fun h0 v))

end Linear

section Model

/-- **Satisfiable instance (model).** `e₀ ∧ e₁` on `ℚ²` is positive for the complex structure
`J e₀ = e₁`, `J e₁ = -e₀`: `B (φ ∘ J, φ) = φ₀² + φ₁²` (the Riemann form of `ℂ / (ℤ + ℤ i)`).
Source: Birkenhake–Lange, *Complex Abelian Varieties*, 2nd ed., §4.1 (the Riemann form of an
elliptic curve); direct computation with `Symplectic.contract_ιMulti`. -/
theorem p1_isPositive_model : p1_IsPositive p1_modelForm (p1_modelJ.baseChange ℝ) :=
  p1_isPositive_model_aux

example : IsNondegenerate p1_modelForm :=
  p1_isNondegenerate_of_isPositive p1_isPositive_model

/-- **Degenerate case ruled out (model): nondegenerate but not positive.** `-(e₀ ∧ e₁)` is
nondegenerate and `B (φ ∘ J, φ) = -(φ₀² + φ₁²)`: it is not positive, so nondegeneracy alone does
not give `p1_IsPositive`.
Source: Birkenhake–Lange, *Complex Abelian Varieties*, 2nd ed., §4.1 (the sign of a Riemann
form); direct computation. -/
theorem p1_not_isPositive_model_neg :
    IsNondegenerate (-p1_modelForm) ∧
      ¬ p1_IsPositive (-p1_modelForm) (p1_modelJ.baseChange ℝ) :=
  p1_not_isPositive_model_neg_aux

example : ¬ p1_IsPositive (-p1_modelForm) (p1_modelJ.baseChange ℝ) :=
  p1_not_isPositive_model_neg.2

/-- **Degenerate case ruled out (model): Rosati positivity fails without positivity.**
`ω₄ = e₀ ∧ e₁ - e₂ ∧ e₃` on `ℚ⁴` is nondegenerate, of type `(1,1)` for `J ⊕ J` but of signature
`(1,1)`, hence not positive; the swap `f` of the two factors commutes with `J ⊕ J`, and its
`E_{ω₄}`-adjoint is `-f`, so `tr(f f†) = -4 < 0`.
Source: Mumford, *Abelian Varieties*, §21 (positivity needs an ample class); direct
computation. -/
theorem p1_model₄ :
    ∃ hω : IsNondegenerate p1_modelForm₄,
      ¬ p1_IsPositive p1_modelForm₄ (p1_modelJ₄.baseChange ℝ) ∧
      p1_modelSwap₄ ∘ₗ p1_modelJ₄ = p1_modelJ₄ ∘ₗ p1_modelSwap₄ ∧ p1_modelSwap₄ ≠ 0 ∧
      LinearMap.trace ℚ (Fin 4 → ℚ) (p1_modelSwap₄ ∘ₗ p1_adjoint p1_modelForm₄ hω p1_modelSwap₄) =
        -4 :=
  p1_model₄_aux

example : ∃ hω : IsNondegenerate p1_modelForm₄, LinearMap.trace ℚ (Fin 4 → ℚ)
    (p1_modelSwap₄ ∘ₗ p1_adjoint p1_modelForm₄ hω p1_modelSwap₄) < 0 := by
  obtain ⟨hω, -, -, -, h⟩ := p1_model₄
  exact ⟨hω, by rw [h]; norm_num⟩

end Model

section Abelian

variable (A : Over (Spec ↧ℂ)) [GrpObj A] [IsIntegral A.left] [Smooth A.hom] [IsProjective A.hom]

/-- **A polarization is nondegenerate.** `IsNondegenerate (polarizationVec … pol)` follows from
`p1_IsPolarization A pol` by `p1_isNondegenerate_of_isPositive`.
Source: Birkenhake–Lange, *Complex Abelian Varieties*, 2nd ed., §4.1;
`p1_isNondegenerate_of_isPositive`. -/
theorem p1_isNondegenerate {pol : HQ A 2} (hP : p1_IsPolarization A pol) :
    IsNondegenerate (polarizationVec (torusCohomology_cupProductOf A) pol) :=
  letI := (torusCohomology_cupProductOf A).finite
  p1_isNondegenerate_of_isPositive hP

example {pol : HQ A 2} (hP : p1_IsPolarization A pol) :
    (polarizationForm (torusCohomology_cupProductOf A) (p1_isNondegenerate A hP)).Nondegenerate :=
  nondegenerate_polarizationForm _ _

/-- **`p1_IsPolarization` is `PolarizationPositive`.** A class is a polarization exactly when
its 2-vector is nondegenerate and its form `E_ω` is a polarization of the weight-one Hodge
structure (the existing `PolarizationPositive`, used by F-1569's `IsMemberOfM` and by G34). For
nondegenerate `ω` and `I² = -1`, invariance of `B_ω` under `Iᵀ` is invariance of `E_ω` under `I`
(the first Riemann relation, `spec_firstRiemannRelation`), and `B_ω (φ ∘ I, φ) = E_ω (x, I x)`
for `x = contract ω φ` (`spec_polarizationPositive_iff`).
Source: Birkenhake–Lange, *Complex Abelian Varieties*, 2nd ed., §4.1–4.2;
`spec_polarizationPositive_iff`, `spec_firstRiemannRelation`. -/
theorem p1_isPolarization_iff (pol : HQ A 2) :
    p1_IsPolarization A pol ↔
      ∃ hη : IsNondegenerate (polarizationVec (torusCohomology_cupProductOf A) pol),
        PolarizationPositive (finiteBetti_abelian A) (spec_bettiDeRhamIso_abelian A)
          (hodgeDecomposition_of_abelian A) (torusCohomology_cupProductOf A) hη :=
  p1_isPolarization_iff_aux A pol

example (pol : HQ A 2) (hP : p1_IsPolarization A pol) :
    PolarizationPositive (finiteBetti_abelian A) (spec_bettiDeRhamIso_abelian A)
      (hodgeDecomposition_of_abelian A) (torusCohomology_cupProductOf A)
      (p1_isNondegenerate A hP) :=
  ((p1_isPolarization_iff A pol).1 hP).2

/-- **A polarization is of type `(1,1)`.** `pol ∈ Hdg¹(A; ℚ)`.
Source: Birkenhake–Lange, *Complex Abelian Varieties*, 2nd ed., §4.1 (first Riemann relation);
`p1_isPolarization_iff`, `spec_polarizationPositive_iff`. -/
theorem p1_mem_hdg {pol : HQ A 2} (hP : p1_IsPolarization A pol) :
    (pol : H^(2 * 1)(A; ℚ)) ∈ Hdg^1(A; ℚ) :=
  p1_mem_hdg_aux A hP

example {pol : HQ A 2} (hP : p1_IsPolarization A pol) :
    (pol : H^(2 * 1)(A; ℚ)) ∈ Hdg^1(A; ℚ) :=
  p1_mem_hdg A hP

variable [IsCommMonObj A]

/-- **The adjoint of an endomorphism action is an endomorphism action.** For a polarization,
the `E_ω`-adjoint of the action of every `φ ∈ End⁰(A)` on `H¹(A; ℚ)` is the action of an
element of `End⁰(A)`. The action of `φ` is a Hodge endomorphism, the adjoint of a Hodge
endomorphism is a Hodge endomorphism (`E_ω` is `I`-invariant), and every Hodge endomorphism of
`H¹` is the action of an element of `End⁰(A)` (`gagaw_spec_abelianEnd0Action_range`). This is the
witness `hR` that `p1_rosati` takes.
Source: Birkenhake–Lange, *Complex Abelian Varieties*, 2nd ed., §5.1 (the Rosati involution is
the adjoint for the Riemann form) and Proposition 1.2.1; Mumford, *Abelian Varieties*, §20;
`gagaw_spec_abelianEnd0Action_range`. -/
theorem p1_adjoint_mem_range {pol : HQ A 2} (hP : p1_IsPolarization A pol)
    (φ : AbelianEnd0 A) :
    letI := (torusCohomology_cupProductOf A).finite
    p1_adjoint (polarizationVec (torusCohomology_cupProductOf A) pol) (p1_isNondegenerate A hP)
        (abelianEnd0Action A φ).unop ∈
      Set.range fun ψ : AbelianEnd0 A => (abelianEnd0Action A ψ).unop :=
  p1_adjoint_mem_range_aux A hP φ

example {pol : HQ A 2} (hP : p1_IsPolarization A pol) (φ : AbelianEnd0 A) :
    letI := (torusCohomology_cupProductOf A).finite
    ∃ ψ : AbelianEnd0 A, (abelianEnd0Action A ψ).unop =
      p1_adjoint (polarizationVec (torusCohomology_cupProductOf A) pol) (p1_isNondegenerate A hP)
        (abelianEnd0Action A φ).unop :=
  p1_adjoint_mem_range A hP φ

/-- **The Rosati involution acts by the adjoint.** For a polarization, the action of
`p1_rosati A pol (p1_isNondegenerate A hP) (p1_adjoint_mem_range A hP) φ` on `H¹(A; ℚ)` is the
`E_ω`-adjoint of the action of `φ`: `p1_rosati` is the transport of the adjoint along the
faithful action, and `p1_adjoint_mem_range` puts the adjoint in its image.
Source: Birkenhake–Lange, *Complex Abelian Varieties*, 2nd ed., §5.1; Mumford, *Abelian
Varieties*, §20; `p1_rosati`, `p1_adjoint_mem_range`, `Equiv.apply_ofInjective_symm`. -/
theorem p1_abelianEnd0Action_rosati {pol : HQ A 2} (hP : p1_IsPolarization A pol)
    (φ : AbelianEnd0 A) :
    letI := (torusCohomology_cupProductOf A).finite
    (abelianEnd0Action A
        (p1_rosati A pol (p1_isNondegenerate A hP) (p1_adjoint_mem_range A hP) φ)).unop =
      p1_adjoint (polarizationVec (torusCohomology_cupProductOf A) pol) (p1_isNondegenerate A hP)
        (abelianEnd0Action A φ).unop :=
  Equiv.apply_ofInjective_symm
    (f := fun ψ : AbelianEnd0 A => (abelianEnd0Action A ψ).unop) _ ⟨_, p1_adjoint_mem_range A hP φ⟩

/-- In terms of the polarization form: `E (φ x, y) = E (x, φ' y)`. -/
example {pol : HQ A 2} (hP : p1_IsPolarization A pol) (φ : AbelianEnd0 A) (x y : HQ A 1) :
    polarizationForm (torusCohomology_cupProductOf A) (p1_isNondegenerate A hP)
        ((abelianEnd0Action A φ).unop x) y =
      polarizationForm (torusCohomology_cupProductOf A) (p1_isNondegenerate A hP) x
        ((abelianEnd0Action A
          (p1_rosati A pol (p1_isNondegenerate A hP) (p1_adjoint_mem_range A hP) φ)).unop y) := by
  let _ := (torusCohomology_cupProductOf A).finite
  rw [p1_abelianEnd0Action_rosati A hP φ]
  exact p1_dualForm_adjoint _ _ x y

/-- The Rosati involution is additive.
Source: Mumford, *Abelian Varieties*, §20 (`(φ + ψ)' = φ' + ψ'`); `p1_abelianEnd0Action_rosati`. -/
theorem p1_rosati_add {pol : HQ A 2} (hP : p1_IsPolarization A pol) (φ ψ : AbelianEnd0 A) :
    p1_rosati A pol (p1_isNondegenerate A hP) (p1_adjoint_mem_range A hP) (φ + ψ) =
      p1_rosati A pol (p1_isNondegenerate A hP) (p1_adjoint_mem_range A hP) φ +
        p1_rosati A pol (p1_isNondegenerate A hP) (p1_adjoint_mem_range A hP) ψ :=
  p1_rosati_add_aux A hP φ ψ

example {pol : HQ A 2} (hP : p1_IsPolarization A pol) (φ : AbelianEnd0 A) :
    p1_rosati A pol (p1_isNondegenerate A hP) (p1_adjoint_mem_range A hP) (φ + φ) =
      p1_rosati A pol (p1_isNondegenerate A hP) (p1_adjoint_mem_range A hP) φ +
        p1_rosati A pol (p1_isNondegenerate A hP) (p1_adjoint_mem_range A hP) φ :=
  p1_rosati_add A hP φ φ

/-- The Rosati involution is `ℚ`-linear.
Source: Mumford, *Abelian Varieties*, §20; `p1_abelianEnd0Action_rosati`. -/
theorem p1_rosati_smul {pol : HQ A 2} (hP : p1_IsPolarization A pol) (q : ℚ)
    (φ : AbelianEnd0 A) :
    p1_rosati A pol (p1_isNondegenerate A hP) (p1_adjoint_mem_range A hP) (q • φ) =
      q • p1_rosati A pol (p1_isNondegenerate A hP) (p1_adjoint_mem_range A hP) φ :=
  p1_rosati_smul_aux A hP q φ

example {pol : HQ A 2} (hP : p1_IsPolarization A pol) (φ : AbelianEnd0 A) :
    p1_rosati A pol (p1_isNondegenerate A hP) (p1_adjoint_mem_range A hP) ((2 : ℚ) • φ) =
      (2 : ℚ) • p1_rosati A pol (p1_isNondegenerate A hP) (p1_adjoint_mem_range A hP) φ :=
  p1_rosati_smul A hP 2 φ

/-- The Rosati involution fixes `1`.
Source: Mumford, *Abelian Varieties*, §20; `p1_abelianEnd0Action_rosati`. -/
theorem p1_rosati_one {pol : HQ A 2} (hP : p1_IsPolarization A pol) :
    p1_rosati A pol (p1_isNondegenerate A hP) (p1_adjoint_mem_range A hP) 1 = 1 :=
  p1_rosati_one_aux A hP

example {pol : HQ A 2} (hP : p1_IsPolarization A pol) (q : ℚ) :
    p1_rosati A pol (p1_isNondegenerate A hP) (p1_adjoint_mem_range A hP) (q • 1) = q • 1 := by
  rw [p1_rosati_smul A hP, p1_rosati_one A hP]

/-- **The Rosati involution reverses products**: `(φ ψ)' = ψ' φ'`.
Source: Mumford, *Abelian Varieties*, §20; Birkenhake–Lange, *Complex Abelian Varieties*, 2nd ed.,
§5.1; `p1_abelianEnd0Action_rosati`. -/
theorem p1_rosati_mul {pol : HQ A 2} (hP : p1_IsPolarization A pol) (φ ψ : AbelianEnd0 A) :
    p1_rosati A pol (p1_isNondegenerate A hP) (p1_adjoint_mem_range A hP) (φ * ψ) =
      p1_rosati A pol (p1_isNondegenerate A hP) (p1_adjoint_mem_range A hP) ψ *
        p1_rosati A pol (p1_isNondegenerate A hP) (p1_adjoint_mem_range A hP) φ :=
  p1_rosati_mul_aux A hP φ ψ

example {pol : HQ A 2} (hP : p1_IsPolarization A pol) (φ : AbelianEnd0 A) :
    p1_rosati A pol (p1_isNondegenerate A hP) (p1_adjoint_mem_range A hP) (φ * φ) =
      p1_rosati A pol (p1_isNondegenerate A hP) (p1_adjoint_mem_range A hP) φ *
        p1_rosati A pol (p1_isNondegenerate A hP) (p1_adjoint_mem_range A hP) φ :=
  p1_rosati_mul A hP φ φ

/-- **The Rosati involution is an involution**: `φ'' = φ` (`E_ω` is alternating).
Source: Mumford, *Abelian Varieties*, §20; Birkenhake–Lange, *Complex Abelian Varieties*, 2nd ed.,
§5.1; `p1_abelianEnd0Action_rosati`. -/
theorem p1_rosati_rosati {pol : HQ A 2} (hP : p1_IsPolarization A pol)
    (φ : AbelianEnd0 A) :
    p1_rosati A pol (p1_isNondegenerate A hP) (p1_adjoint_mem_range A hP)
      (p1_rosati A pol (p1_isNondegenerate A hP) (p1_adjoint_mem_range A hP) φ) = φ :=
  p1_rosati_rosati_aux A hP φ

example {pol : HQ A 2} (hP : p1_IsPolarization A pol) :
    Function.Bijective (p1_rosati A pol (p1_isNondegenerate A hP) (p1_adjoint_mem_range A hP)) :=
  Function.Involutive.bijective (p1_rosati_rosati A hP)

/-- **The Rosati involution as an anti-involution of `End⁰(A)`**: an algebra isomorphism
`End⁰(A) ≃ End⁰(A)ᵐᵒᵖ` whose underlying map is `p1_rosati`, together with `φ'' = φ`.
Source: Mumford, *Abelian Varieties*, §20; assembled from `p1_rosati_add`, `p1_rosati_smul`,
`p1_rosati_one`, `p1_rosati_mul`, `p1_rosati_rosati`. -/
theorem p1_rosati_antiInvolution {pol : HQ A 2} (hP : p1_IsPolarization A pol) :
    ∃ R : AbelianEnd0 A ≃ₐ[ℚ] (AbelianEnd0 A)ᵐᵒᵖ,
      (∀ φ, R φ = MulOpposite.op
        (p1_rosati A pol (p1_isNondegenerate A hP) (p1_adjoint_mem_range A hP) φ)) ∧
        ∀ φ, p1_rosati A pol (p1_isNondegenerate A hP) (p1_adjoint_mem_range A hP)
          (p1_rosati A pol (p1_isNondegenerate A hP) (p1_adjoint_mem_range A hP) φ) = φ :=
  ⟨AlgEquiv.ofBijective
    { toFun := fun φ => MulOpposite.op
        (p1_rosati A pol (p1_isNondegenerate A hP) (p1_adjoint_mem_range A hP) φ)
      map_one' := by rw [p1_rosati_one A hP, MulOpposite.op_one]
      map_mul' := fun φ ψ => by rw [p1_rosati_mul A hP, MulOpposite.op_mul]
      map_zero' := by
        have h := p1_rosati_smul A hP 0 0
        rw [zero_smul, zero_smul] at h
        rw [h, MulOpposite.op_zero]
      map_add' := fun φ ψ => by rw [p1_rosati_add A hP, MulOpposite.op_add]
      commutes' := fun q => by
        rw [Algebra.algebraMap_eq_smul_one, p1_rosati_smul A hP, p1_rosati_one A hP,
          MulOpposite.op_smul, MulOpposite.op_one, ← Algebra.algebraMap_eq_smul_one] }
    (MulOpposite.opEquiv.bijective.comp
      (Function.Involutive.bijective (p1_rosati_rosati A hP))),
    fun _ => rfl, p1_rosati_rosati A hP⟩

/-- Model of the anti-involution on `ℚ²`: for `ω = e₀ ∧ e₁`, the adjoint reverses products,
`(J ∘ J')† = J'† ∘ J†` for `J` the model complex structure and `J'` the swap of coordinates. -/
example :
    p1_adjoint p1_modelForm Symplectic.isNondegenerate_e₀e₁
        (p1_modelJ ∘ₗ LinearMap.funLeft ℚ ℚ ![1, 0]) =
      p1_adjoint p1_modelForm Symplectic.isNondegenerate_e₀e₁ (LinearMap.funLeft ℚ ℚ ![1, 0]) ∘ₗ
        p1_adjoint p1_modelForm Symplectic.isNondegenerate_e₀e₁ p1_modelJ := by
  simp only [p1_adjoint, ← LinearMap.dualMap_comp_dualMap]
  ext x
  simp

/-- **The Rosati involution is positive**: `tr(φ φ') > 0` for `φ ≠ 0`, the trace of the action on
`H¹(A; ℚ)`. The action of `φ φ'` is `T† ∘ T` for `T` the action of `φ`, which commutes with the
complex structure, and `p1_trace_pos` applies.
Source: Mumford, *Abelian Varieties*, §21, Theorem 1; Birkenhake–Lange, *Complex Abelian
Varieties*, 2nd ed., Theorem 5.1.8; `p1_trace_pos`. -/
theorem p1_rosati_pos {pol : HQ A 2} (hP : p1_IsPolarization A pol) {φ : AbelianEnd0 A}
    (hφ : φ ≠ 0) :
    0 < LinearMap.trace ℚ (HQ A 1) (abelianEnd0Action A
      (φ * p1_rosati A pol (p1_isNondegenerate A hP) (p1_adjoint_mem_range A hP) φ)).unop :=
  p1_rosati_pos_aux A hP hφ

example {pol : HQ A 2} (hP : p1_IsPolarization A pol) {φ : AbelianEnd0 A}
    (hφ : φ ≠ 0) :
    φ * p1_rosati A pol (p1_isNondegenerate A hP) (p1_adjoint_mem_range A hP) φ ≠ 0 :=
  fun h0 => by
    have := p1_rosati_pos A hP hφ
    rw [h0, map_zero, MulOpposite.unop_zero, map_zero] at this
    exact lt_irrefl _ this

variable {L : Type*} [Field L] [NumberField L] [IsCMField L]

/-- **On `End⁰(A) = L`, the Rosati involution is complex conjugation.** If
`θ : L →ₐ[ℚ] End⁰(A)` is bijective and `L` is a CM field, then `θ(a)' = θ(ā)`. The Rosati
involution transported to `L` is a field automorphism `σ` with `Tr_{L/ℚ}(a σ(a)) > 0` for
`a ≠ 0` (`p1_rosati_pos`; `H¹` is a free `L`-module of positive rank); the only positive
involution of a CM field is complex conjugation.
Source: PW v0.3, `docs/specs/inputs/papers/powers-weil-v0.3.tex` line 147; Mumford, *Abelian
Varieties*, §21 (positive involutions of number fields); Birkenhake–Lange, *Complex Abelian
Varieties*, 2nd ed., §5.5. -/
theorem p1_rosati_conj {pol : HQ A 2} (hP : p1_IsPolarization A pol)
    (θ : L →ₐ[ℚ] AbelianEnd0 A) (hθ : Function.Bijective θ) (a : L) :
    p1_rosati A pol (p1_isNondegenerate A hP) (p1_adjoint_mem_range A hP) (θ a) =
      θ (IsCMField.complexConj L a) :=
  p1_rosati_conj_aux A hP θ hθ a

example {pol : HQ A 2} (hP : p1_IsPolarization A pol)
    (θ : L →ₐ[ℚ] AbelianEnd0 A) (hθ : Function.Bijective θ)
    (a : NumberField.maximalRealSubfield L) :
    p1_rosati A pol (p1_isNondegenerate A hP) (p1_adjoint_mem_range A hP) (θ (a : L)) =
      θ (a : L) := by
  rw [p1_rosati_conj A hP θ hθ, IsCMField.complexConj_apply_eq_self]

/-- **The Rosati condition of `pwf_theorem_4_2`, derived.** For a polarization and bijective
`θ`, `E (θ(a)^* x, y) = E (x, θ(ā)^* y)` for the form of the derived `hη`, in the exact form of
the binder `hRos` of `pwf_theorem_4_2` and `spec_g3link2_generation_cup`.
Source: PW v0.3, line 147; `p1_rosati_conj`, `p1_abelianEnd0Action_rosati`,
`p1_dualForm_adjoint`. -/
theorem p1_hRos {pol : HQ A 2} (hP : p1_IsPolarization A pol)
    (θ : L →ₐ[ℚ] AbelianEnd0 A) (hθ : Function.Bijective θ) :
    ∀ (a : L) (x y : HQ A 1),
      polarizationForm (torusCohomology_cupProductOf A) (p1_isNondegenerate A hP)
          (pwAction A θ a x) y =
        polarizationForm (torusCohomology_cupProductOf A) (p1_isNondegenerate A hP) x
          (pwAction A θ (IsCMField.complexConj L a) y) := by
  intro a x y
  let _ := (torusCohomology_cupProductOf A).finite
  change dualForm _ ((abelianEnd0Action A (θ a)).unop x) y =
    dualForm _ x ((abelianEnd0Action A (θ (IsCMField.complexConj L a))).unop y)
  rw [← p1_rosati_conj A hP θ hθ a, p1_abelianEnd0Action_rosati A hP]
  exact p1_dualForm_adjoint _ _ x y

/-- Model of the Rosati condition on `ℚ²`: for `ω = e₀ ∧ e₁` and `L = ℚ(i)` acting through the
model complex structure `J` (`i ↦ J`, so `ī = -i ↦ -J`), `E (J x, y) = E (x, (-J) y)`. -/
example (x y : Fin 2 → ℚ) :
    dualForm Symplectic.isNondegenerate_e₀e₁ (p1_modelJ x) y =
      dualForm Symplectic.isNondegenerate_e₀e₁ x ((-p1_modelJ) y) := by
  rw [Symplectic.dualForm_e₀e₁]
  simp [WeilHermitian.exE_apply, p1_modelJ, dotProduct]
  ring

/-- **`IsRosatiSkew` for `u² = -d`, derived.** For a polarization, bijective `θ` and
`u² = -d`, `d > 0`, the action of `u` is Rosati-skew for the polarization.
Source: PW v0.3, line 147; `p1_hRos`, `f2_isRosatiSkew_of_rosati`. -/
theorem p1_isRosatiSkew {pol : HQ A 2} (hP : p1_IsPolarization A pol)
    (θ : L →ₐ[ℚ] AbelianEnd0 A) (hθ : Function.Bijective θ) (u : L) {d : ℚ} (hd : 0 < d)
    (hu : u ^ 2 = -algebraMap ℚ L d) :
    IsRosatiSkew (polarizationVec (torusCohomology_cupProductOf A) pol) (pwAction A θ u) :=
  f2_isRosatiSkew_of_rosati A θ u hd hu pol (p1_isNondegenerate A hP) (p1_hRos A hP θ hθ)

/-- Model of `IsRosatiSkew` on `ℚ²`: `u = i`, `d = 1`, acting by the model complex structure
`J` (`J² = -1`), is Rosati-skew for `ω = e₀ ∧ e₁`. -/
example : IsRosatiSkew p1_modelForm p1_modelJ := by
  refine (isRosatiSkew_iff_dualForm Symplectic.isNondegenerate_e₀e₁ _).2 fun x y => ?_
  rw [Symplectic.dualForm_e₀e₁]
  simp [WeilHermitian.exE_apply, p1_modelJ, dotProduct]
  ring

/-- **The adapter**: from a polarization and bijective `θ`, the `hη` and `hRos` arguments that
the PW route (`spec_g3link2_generation_cup`, `pwf_theorem_4_2`) consumes.
Source: `p1_isNondegenerate`, `p1_hRos`. -/
theorem p1_pw_inputs {pol : HQ A 2} (hP : p1_IsPolarization A pol)
    (θ : L →ₐ[ℚ] AbelianEnd0 A) (hθ : Function.Bijective θ) :
    ∃ hη : IsNondegenerate (polarizationVec (torusCohomology_cupProductOf A) pol),
      ∀ (a : L) (x y : HQ A 1),
        polarizationForm (torusCohomology_cupProductOf A) hη (pwAction A θ a x) y =
          polarizationForm (torusCohomology_cupProductOf A) hη x
            (pwAction A θ (IsCMField.complexConj L a) y) :=
  ⟨p1_isNondegenerate A hP, p1_hRos A hP θ hθ⟩

/-- The adapter feeds the generation statement of the PW route: the binders `hη` and `hRos` of
`spec_g3link2_generation_cup` are supplied by a polarization and bijective `θ`. -/
example {pol : HQ A 2} (hP : p1_IsPolarization A pol)
    (θ : L →ₐ[ℚ] AbelianEnd0 A) (hθ : Function.Bijective θ) (u : L) {d : ℚ}
    (hd : 0 < d) (hu : u ^ 2 = -algebraMap ℚ L d)
    (hGk : letI := (finiteBetti_abelian A).finite 1
      HodgeLieIsGk (abelianWeightOneHodgeStructure A).H
        (abelianWeightOneHodgeStructure A).isInternal
        (polarizationForm (torusCohomology_cupProductOf A) (p1_isNondegenerate A hP))
        (pwActionRange A θ) (pwAction A θ u))
    (r : ℕ) :
    letI := (finiteBetti_abelian A).finite 1
    ∀ p : ℕ, Hdg^p(g3_power A r; ℚ) = f1_pulledWeilCupSpan A θ u d hu
      (isWeilType_of_hodgeLieIsGk hd (f1_weilAction A θ u d hu)
        (h10_sup_h01_eq_top (finiteBetti_abelian A) (spec_bettiDeRhamIso_abelian A)
          (hodgeDecomposition_of_abelian A) (torusCohomology_cupProductOf A)) _ _ hGk)
      (g3_powerData A r) Hdg^1(g3_power A r; ℚ) p :=
  spec_g3link2_generation_cup A θ u hd hu pol (p1_isNondegenerate A hP) (p1_hRos A hP θ hθ)
    hGk r

end Abelian

end HodgeLean.Foundations
