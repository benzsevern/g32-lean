import HodgeLean.Adapters.PolarizedHodgeAbelian
import HodgeLean.Adapters.AbelianCMData

/-! # Positive polarizations and the Rosati involution: definitions (FROZEN)

Definitions for Track P1 (`PositivePolarization`). Notation: `V` is a finite-dimensional
`ℚ`-space (for an abelian variety, `V = H¹(A; ℚ)`), `ω ∈ ⋀² V` a 2-vector, `c = contract ω :
V^∨ → V` its contraction, and `B_ω (φ, ψ) = ψ (c φ)` the alternating form of `ω` on
`V^∨ = H₁(A; ℚ)`, where the Riemann form of a polarization lives.

* `p1_realContract ω`: the contraction of `ω` after base change to `ℝ`, as a map
  `Dual ℝ (ℝ ⊗ V) → ℝ ⊗ V`, through Mathlib's identification `ℝ ⊗ V^∨ ≅ (ℝ ⊗ V)^∨`.
* `p1_IsPositive ω I`: for a real endomorphism `I` of `ℝ ⊗ V`, the form `B_ω` is invariant under
  the transpose of `I`, and `B_ω (φ ∘ I, φ) = φ (c (φ ∘ I)) > 0` for every nonzero real
  functional `φ`: the Riemann relations on `H₁ ⊗ ℝ`, stated without assuming that `ω` is
  nondegenerate.
* `p1_adjoint ω hω f`: for nondegenerate `ω` (the witness `hω` is an argument), the adjoint of
  `f ∈ End(V)` for the dual form `E_ω = dualForm` on `V`, `c ∘ fᵀ ∘ c⁻¹`.
* `p1_IsPolarization A pol`: `p1_IsPositive` for `ω = polarizationVec … pol` and the canonical
  real complex structure `weightOneComplexStructure A …` of `H¹(A; ℚ) ⊗ ℝ`.
* `p1_rosati A pol hη hR`: the Rosati involution of `End⁰(A)`, computed: the `E_ω`-adjoint of the
  action of `φ` on `H¹`, transported back along the faithful action `End⁰(A) → End(H¹)` through
  the inverse of `Equiv.ofInjective` on its image. It takes the nondegeneracy witness `hη` and the
  witness `hR` that each adjoint lies in the image as arguments.
* Model data on `ℚ²` and `ℚ⁴` for the satisfiable and degenerate instances.

No definition asserts positivity, nondegeneracy, an involution property or a relation with a CM
field. HC no distance; AV milestone no distance.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint TopologicalSpace Module
open scoped TensorProduct
open HodgeLean.RealDefs HodgeLean.Adapters HodgeLean.Foundations.Symplectic

namespace HodgeLean.Foundations

section Linear

variable {V : Type*} [AddCommGroup V] [Module ℚ V] [Module.Finite ℚ V]

/-- **The contraction of `ω` over `ℝ`.** `(contract ω).baseChange ℝ`, precomposed with the inverse
of Mathlib's isomorphism `ℝ ⊗[ℚ] V^∨ ≃ (ℝ ⊗[ℚ] V)^∨` (`IsBaseChange.toDualBaseChange`). On a
functional `1 ⊗ φ` it is `1 ⊗ contract ω φ`.
Source: Bourbaki, *Algebra I*, Ch. II, §5 (extension of scalars of duals) and Ch. III (interior
products); Mathlib `IsBaseChange.toDualBaseChange`, `Symplectic.contract`. -/
def p1_realContract (ω : ⋀[ℚ]^2 V) : Dual ℝ (ℝ ⊗[ℚ] V) →ₗ[ℝ] ℝ ⊗[ℚ] V :=
  (contract ω).baseChange ℝ ∘ₗ
    ((TensorProduct.isBaseChange ℚ V ℝ).toDualBaseChange).symm.toLinearMap

/-- The real contraction of `ω = 0` is zero. -/
example : p1_realContract (0 : ⋀[ℚ]^2 V) = 0 := by
  ext φ
  simp [p1_realContract]

/-- **Positivity of a 2-vector for a real complex structure (the Riemann relations on `H₁`).**
For `ω ∈ ⋀² V` and `I : ℝ ⊗ V → ℝ ⊗ V`, with `c = p1_realContract ω` and
`B (φ, ψ) = ψ (c φ)` on `(ℝ ⊗ V)^∨ = H₁ ⊗ ℝ`:
* `B (φ ∘ I, ψ ∘ I) = B (φ, ψ)` for all `φ, ψ` (the first Riemann relation, `ω` of type `(1,1)`);
* `B (φ ∘ I, φ) = φ (c (φ ∘ I)) > 0` for `φ ≠ 0` (the second, positivity: the Hermitian form
  `H (φ, ψ) = B (φ ∘ I, ψ) + i B (φ, ψ)` is positive definite).
Nondegeneracy of `ω` is not part of the definition; it follows (`p1_isNondegenerate_of_isPositive`).
For nondegenerate `ω` and `I² = -1` this is positivity of `E_ω (x, I x)` on `H¹ ⊗ ℝ`, the form of
`PolarizationPositive` (`p1_isPolarization_iff`).
Source: Birkenhake–Lange, *Complex Abelian Varieties*, 2nd ed., Grundlehren 302, §4.1–4.2
(Riemann relations, the positive definite Hermitian form `H(x, y) = E(ix, y) + i E(x, y)` on the
lattice side `H₁`); Mumford, *Abelian Varieties*, §4 (Riemann forms). -/
def p1_IsPositive (ω : ⋀[ℚ]^2 V) (I : ℝ ⊗[ℚ] V →ₗ[ℝ] ℝ ⊗[ℚ] V) : Prop :=
  (∀ φ ψ : Dual ℝ (ℝ ⊗[ℚ] V),
      (ψ ∘ₗ I) (p1_realContract ω (φ ∘ₗ I)) = ψ (p1_realContract ω φ)) ∧
    ∀ φ : Dual ℝ (ℝ ⊗[ℚ] V), φ ≠ 0 → 0 < φ (p1_realContract ω (φ ∘ₗ I))

/-- On the zero space every 2-vector is positive: there is no nonzero functional. -/
example (I : ℝ ⊗[ℚ] (Fin 0 → ℚ) →ₗ[ℝ] ℝ ⊗[ℚ] (Fin 0 → ℚ)) (ω : ⋀[ℚ]^2 (Fin 0 → ℚ)) :
    p1_IsPositive ω I := by
  have hV : ∀ v : ℝ ⊗[ℚ] (Fin 0 → ℚ), v = 0 := fun v => Subsingleton.elim v 0
  have hD : ∀ φ : Dual ℝ (ℝ ⊗[ℚ] (Fin 0 → ℚ)), φ = 0 := fun φ =>
    LinearMap.ext fun v => by rw [hV v, map_zero, map_zero]
  exact ⟨fun φ ψ => by rw [hD φ, hD ψ]; simp, fun φ hφ => absurd (hD φ) hφ⟩

/-- **The adjoint for the dual form `E_ω`.** For nondegenerate `ω`, with `e = contractEquiv hω :
V^∨ ≃ V`, `p1_adjoint ω hω f = e ∘ fᵀ ∘ e⁻¹`; it satisfies
`E_ω (f x, y) = E_ω (x, p1_adjoint ω hω f y)` (`p1_dualForm_adjoint`). There is no value for
degenerate `ω`: the witness `hω` is an argument.
Source: Bourbaki, *Algèbre*, ch. IX, §1 (adjoint for a nondegenerate bilinear form);
`Symplectic.contractEquiv`, `Symplectic.dualForm`. -/
def p1_adjoint (ω : ⋀[ℚ]^2 V) (hω : IsNondegenerate ω) (f : Module.End ℚ V) : Module.End ℚ V :=
  (contractEquiv hω).toLinearMap ∘ₗ f.dualMap ∘ₗ (contractEquiv hω).symm.toLinearMap

/-- On a contracted functional, the adjoint is the contraction of the transpose:
`f† (c φ) = c (φ ∘ f)`. -/
example (ω : ⋀[ℚ]^2 V) (hω : IsNondegenerate ω) (f : Module.End ℚ V) (φ : Dual ℚ V) :
    p1_adjoint ω hω f (contract ω φ) = contract ω (f.dualMap φ) := by
  simp [p1_adjoint]

/-- The adjoint of the identity is the identity. -/
example (ω : ⋀[ℚ]^2 V) (hω : IsNondegenerate ω) : p1_adjoint ω hω LinearMap.id = LinearMap.id := by
  ext x
  simp [p1_adjoint]

end Linear

section Model

/-- The model 2-vector `e₀ ∧ e₁` on `ℚ²`.
Source: Birkenhake–Lange, *Complex Abelian Varieties*, 2nd ed., §4.1 (the standard Riemann form
of an elliptic curve `ℂ / (ℤ + ℤ i)`, here on `H¹`). -/
def p1_modelForm : ⋀[ℚ]^2 (Fin 2 → ℚ) :=
  exteriorPower.ιMulti ℚ 2 ![Pi.single 0 1, Pi.single 1 1]

example : contract p1_modelForm (LinearMap.proj 0) = Pi.single 1 1 := by
  simp [p1_modelForm]

/-- The model complex structure `J e₀ = e₁`, `J e₁ = -e₀` on `ℚ²` (the matrix `[[0, -1], [1, 0]]`).
Source: Birkenhake–Lange, *Complex Abelian Varieties*, 2nd ed., §1.1 (multiplication by `i` on
`ℂ = ℝ²`). -/
def p1_modelJ : Module.End ℚ (Fin 2 → ℚ) :=
  Matrix.toLin' !![0, -1; 1, 0]

example : p1_modelJ (Pi.single 0 1) = Pi.single 1 1 := by
  ext i; fin_cases i <;> simp [p1_modelJ, Matrix.mulVec, dotProduct]

/-- The model 2-vector `e₀ ∧ e₁ - e₂ ∧ e₃` on `ℚ⁴`: nondegenerate, of type `(1,1)` for
`p1_modelJ₄`, of signature `(1,1)`.
Source: Birkenhake–Lange, *Complex Abelian Varieties*, 2nd ed., §4.1 (nondegenerate Riemann forms
of mixed signature; these give non-ample line bundles). -/
def p1_modelForm₄ : ⋀[ℚ]^2 (Fin 4 → ℚ) :=
  exteriorPower.ιMulti ℚ 2 ![Pi.single 0 1, Pi.single 1 1] -
    exteriorPower.ιMulti ℚ 2 ![Pi.single 2 1, Pi.single 3 1]

example : contract p1_modelForm₄ (LinearMap.proj 2) = -Pi.single 3 1 := by
  simp [p1_modelForm₄]

/-- The model complex structure `J ⊕ J` on `ℚ⁴ = ℚ² ⊕ ℚ²`.
Source: Birkenhake–Lange, *Complex Abelian Varieties*, 2nd ed., §1.1. -/
def p1_modelJ₄ : Module.End ℚ (Fin 4 → ℚ) :=
  Matrix.toLin' !![0, -1, 0, 0; 1, 0, 0, 0; 0, 0, 0, -1; 0, 0, 1, 0]

example : p1_modelJ₄ (Pi.single 2 1) = Pi.single 3 1 := by
  ext i; fin_cases i <;> simp [p1_modelJ₄, Matrix.mulVec, dotProduct, Fin.sum_univ_four]

/-- The model swap `e₀ ↔ e₂`, `e₁ ↔ e₃` of the two factors of `ℚ⁴ = ℚ² ⊕ ℚ²`; it commutes with
`p1_modelJ₄`.
Source: Mumford, *Abelian Varieties*, §21 (endomorphisms of `E × E`). -/
def p1_modelSwap₄ : Module.End ℚ (Fin 4 → ℚ) :=
  LinearMap.funLeft ℚ ℚ ![2, 3, 0, 1]

example : p1_modelSwap₄ (Pi.single 0 1) = Pi.single 2 1 := by
  ext i; fin_cases i <;> simp [p1_modelSwap₄, LinearMap.funLeft]

end Model

section Abelian

variable (A : Over (Spec ↧ℂ)) [GrpObj A] [IsIntegral A.left] [Smooth A.hom] [IsProjective A.hom]

/-- **A polarization of `A` (Riemann relations, positivity constructed).** The class
`pol ∈ H²(A; ℚ)`, through its 2-vector `ω = polarizationVec … pol ∈ ⋀² H¹(A; ℚ)` (C7), is positive
for the canonical real complex structure `I = weightOneComplexStructure A …` of `H¹(A; ℝ)` (the
real operator whose complexification is `-C`, `C` the Weil operator of the weight-one Hodge
structure): `p1_IsPositive ω I`. This is a `Prop` about the class `pol`; it does not include
nondegeneracy (`p1_isNondegenerate`) and is equivalent to the existing `PolarizationPositive`
(`p1_isPolarization_iff`), so it fixes the same sign convention.
Source: Birkenhake–Lange, *Complex Abelian Varieties*, 2nd ed., Grundlehren 302, §4.1–4.2
(Riemann relations; a polarization is the class of a positive definite Hermitian form `H` with
`Im H` integral on the lattice); Mumford, *Abelian Varieties*, §4 and §23. -/
def p1_IsPolarization (pol : HQ A 2) : Prop :=
  letI := (torusCohomology_cupProductOf A).finite
  p1_IsPositive (polarizationVec (torusCohomology_cupProductOf A) pol)
    (weightOneComplexStructure A (finiteBetti_abelian A) (spec_bettiDeRhamIso_abelian A))

example (pol : HQ A 2) :
    p1_IsPolarization A pol ↔
      letI := (torusCohomology_cupProductOf A).finite
      p1_IsPositive (polarizationVec (torusCohomology_cupProductOf A) pol)
        (weightOneComplexStructure A (finiteBetti_abelian A) (spec_bettiDeRhamIso_abelian A)) :=
  Iff.rfl

variable [IsCommMonObj A]

/-- **The Rosati involution of `End⁰(A)`, computed.** For nondegenerate
`ω = polarizationVec … pol` (witness `hη`) and `φ ∈ End⁰(A)` with action
`T = (abelianEnd0Action A φ).unop` on `H¹(A; ℚ)`, `p1_rosati A pol hη hR φ` is the element of
`End⁰(A)` whose action is the `E_ω`-adjoint `p1_adjoint ω hη T`: the transport of the adjoint
along the faithful action (injective by `spec_g4_abelianEnd0Action_injective`), through the
inverse of `Equiv.ofInjective` on the image. The argument `hR` says that every such adjoint lies in
the image; for a polarization it is `p1_adjoint_mem_range`. This is the Rosati involution
`φ ↦ φ' = λ⁻¹ φ̂ λ` read on `H¹`: `E(φ x, y) = E(x, φ' y)`.
Source: Birkenhake–Lange, *Complex Abelian Varieties*, 2nd ed., §5.1 (the Rosati involution is
the adjoint for the Riemann form); Mumford, *Abelian Varieties*, §20; `p1_adjoint`,
`abelianEnd0Action`. -/
def p1_rosati (pol : HQ A 2)
    (hη : IsNondegenerate (polarizationVec (torusCohomology_cupProductOf A) pol))
    (hR : ∀ φ : AbelianEnd0 A,
      letI := (torusCohomology_cupProductOf A).finite
      p1_adjoint _ hη (abelianEnd0Action A φ).unop ∈
        Set.range fun ψ : AbelianEnd0 A => (abelianEnd0Action A ψ).unop)
    (φ : AbelianEnd0 A) : AbelianEnd0 A :=
  (Equiv.ofInjective _
    (MulOpposite.unop_injective.comp (spec_g4_abelianEnd0Action_injective A))).symm ⟨_, hR φ⟩

/-- The action of `p1_rosati A pol hη hR φ` is the adjoint of the action of `φ`. -/
example (pol : HQ A 2)
    (hη : IsNondegenerate (polarizationVec (torusCohomology_cupProductOf A) pol))
    (hR : ∀ φ : AbelianEnd0 A,
      letI := (torusCohomology_cupProductOf A).finite
      p1_adjoint _ hη (abelianEnd0Action A φ).unop ∈
        Set.range fun ψ : AbelianEnd0 A => (abelianEnd0Action A ψ).unop)
    (φ : AbelianEnd0 A) :
    letI := (torusCohomology_cupProductOf A).finite
    (abelianEnd0Action A (p1_rosati A pol hη hR φ)).unop =
      p1_adjoint _ hη (abelianEnd0Action A φ).unop :=
  Equiv.apply_ofInjective_symm
    (f := fun ψ : AbelianEnd0 A => (abelianEnd0Action A ψ).unop) _ ⟨_, hR φ⟩

end Abelian

end HodgeLean.Foundations
