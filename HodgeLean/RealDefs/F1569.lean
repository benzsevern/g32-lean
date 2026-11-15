import HodgeLean.RealDefs.WeilClasses
import HodgeLean.Foundations.DualForm
import HodgeLean.Foundations.WeilHermitian
import HodgeLean.Blocks.HodgeStructure.Polarisation

/-! # F-1569 as a Lean statement over all of `M = (3, ℚ(√−3), [−2])`

Brief `f1569`. **Nothing in this file asserts F-1569.** `F1569StatementFor cup` is a definition: a
`Prop` stated for a chosen family of cup products and not proved. Until S7 constructs the
topological cup product, `cup` is a parameter.

## Setting

`X` is abelian (`[GrpObj X]`) with a cup product `μ`, C1, C2, C4 and C7 (`hF hB hD hT`), and the
package `S := abelianVarietyCohomologyOf hF hB hD hT` (F-1689). `A : WeilAction S.weight1 d` is a
Weil action on `V := H¹(X(ℂ); ℚ)`, `J := A.J`, `J² = −d`. `η : H²(X(ℂ); ℚ)` is a polarization class
and `ω := (hT.cupWedgeEquiv 2).symm η ∈ ⋀² V` its preimage under the torus isomorphism (C7).

## Main definitions

* `polarizationVec hT η`: `ω`.
* `polarizationForm hT hω`: the dual form `E_ω` on `V` (`Symplectic.dualForm`), the dual of the
  Riemann form `B_ω` on `V^∨ = H₁`.
* `weilDatumClass hF hB hD hT A hω hR`: the class `weilDetClass E_ω J` in `ℚˣ ⧸ Nm(Kˣ)`,
  `K = ℚ(√−d)`, when `J` satisfies the Rosati condition `hR : IsRosatiSkew ω J`.
* `PolarizationPositive hF hB hD hT hω`: `E_ω` is a polarization of the weight-one Hodge structure
  `S.weight1` (the Hodge–Riemann bilinear relations).
* `IsMemberOfM hF hB hD hT A η`: `(X, A, η)` is a member of F-1569's family `M = (3, ℚ(√−3), [−2])`.
* `SignatureDictionary hF hB hD hT A I`: the eigenspace dictionary for a complex structure `I` on
  `H¹_ℝ` (a stated hypothesis with a `Source:` line; not proved).
* `F1569StatementFor cup`: F-1569 for the chosen cup-product family `cup`, intended to be the
  topological cup product constructed at S7. **Stated, not proved.**

## Main results

* `isRosatiSkew_iff`: the Rosati condition on `ω` (`⋀² J ω = d ω`) is skewness of `J` for `E_ω`.
* `isWeilType_iff_hermSignature_eq`: for a sixfold, `A.IsWeilType` iff the Hermitian form
  `weilHermitian E_ω J` has signature `(3, 3)`, for a complex structure `I` on `H¹_ℝ` positive for
  `E_ω`, **conditional on `SignatureDictionary`** (the eigenspace dictionary, not proved: building
  `I` from the Hodge decomposition is the disclosed gap of item 4).
* `weilClassesAlgebraic_of_f1569Statement`: `F1569StatementFor cup` gives
  `WeilClassesAlgebraic` for each member.
* `hdg_le_span_of_f1569Statement` (milestone): `F1569StatementFor cup`, generation, C9 and
  Lefschetz (1,1) give the Hodge conjecture against upstream's `Hdg` for each member of `M`.

Relation to the goal: HC no distance. AV milestone no distance. F-1569 becomes a precise Lean
statement; it is not proved.
-/

open CategoryTheory AlgebraicGeometry ComplexPoint TopologicalSpace Module
open scoped TensorProduct

namespace HodgeLean.RealDefs

open HodgeLean.Foundations HodgeLean.Foundations.Symplectic HodgeLean.Foundations.WeilHermitian
  HodgeLean.Foundations.HermitianForm

variable {X : Over (Spec ↧ℂ)} [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
variable {μ : CupProduct X} [GrpObj X]

section Polarization

/-- The preimage `ω = (cupWedgeEquiv 2)⁻¹ η ∈ ⋀² H¹(X(ℂ); ℚ)` of a class `η ∈ H²(X(ℂ); ℚ)` under
the torus isomorphism `⋀² H¹ ≅ H²` (C7). For `η` a polarization class, `ω` is the polarization as a
2-vector, the object that `Adapters.hardLefschetz_of_torusCohomology` takes.

Source: Birkenhake–Lange, *Complex Abelian Varieties*, 2nd ed., Grundlehren 302, Lemma 1.3.1
(`⋀^* H¹ ≅ H^*`, through `TorusCohomology`). -/
noncomputable def polarizationVec (hT : TorusCohomology μ) (η : HQ X 2) : ⋀[ℚ]^2 (HQ X 1) :=
  (hT.cupWedgeEquiv 2).symm η

/-- `ω` is carried back to `η` by the cup product. -/
theorem cupWedgeMap_polarizationVec (hT : TorusCohomology μ) (η : HQ X 2) :
    μ.cupWedgeMap 2 (polarizationVec hT η) = η := by
  rw [polarizationVec, ← hT.cupWedgeEquiv_apply, LinearEquiv.apply_symm_apply]

/-- **The polarization form `E_ω` on `H¹`.** For `ω = polarizationVec hT η` nondegenerate, the
dual form `Symplectic.dualForm hω`: `E_ω (x, y) = (contract ω)⁻¹ y x`. The 2-vector `ω` is the
alternating form `B_ω (φ, ψ) = ψ (contract ω φ)` on `V^∨ = H₁(X; ℚ)`, which is where the Riemann
form of the polarization lives; `E_ω` is `B_ω` transported to `V = H¹` along
`contract ω : V^∨ ≃ V` (`dualForm_contract_contract`). It is alternating (`isAlt_dualForm`) and
nondegenerate (`nondegenerate_dualForm`).

Using the dual form instead of `B_ω` itself does not change the Weil datum at `dim_K = 6`: the Gram
matrix of the dual Hermitian form is the inverse, and `[δ⁻¹] = [δ]` in `ℚˣ ⧸ Nm(Kˣ)` (F-1712's
review; not formalized here).

Source: Birkenhake–Lange, *Complex Abelian Varieties*, 2nd ed., Grundlehren 302, Ch. 4 (the
Riemann form of a polarization, on `H₁`); the transport is `Symplectic.dualForm`. -/
noncomputable def polarizationForm (hT : TorusCohomology μ) {η : HQ X 2}
    (hω : IsNondegenerate (polarizationVec hT η)) : LinearMap.BilinForm ℚ (HQ X 1) :=
  dualForm hω

/-- `E_ω` is alternating. -/
theorem isAlt_polarizationForm (hT : TorusCohomology μ) {η : HQ X 2}
    (hω : IsNondegenerate (polarizationVec hT η)) : (polarizationForm hT hω).IsAlt :=
  letI := hT.finite
  isAlt_dualForm hω

/-- `E_ω` is nondegenerate. -/
theorem nondegenerate_polarizationForm (hT : TorusCohomology μ) {η : HQ X 2}
    (hω : IsNondegenerate (polarizationVec hT η)) : (polarizationForm hT hω).Nondegenerate :=
  letI := hT.finite
  nondegenerate_dualForm hω

/-- **The compatibility of `J` with the polarization (item 1).** For `J² = −d`, `d ≠ 0`, these are
equivalent:
* `⋀² J ω = d • ω` (for `d = 3`: `⋀² J ω = 3 ω`), an equation on the class;
* `IsRosatiSkew ω J`: `Jᵀ` is skew for the Riemann form `B_ω` on `H₁`, i.e. the Rosati
  involution sends the endomorphism `J` to `−J`, so it restricts to complex conjugation on
  `ℚ(J) ≅ ℚ(√−d)`;
* `J` is skew for `E_ω`: `E_ω (J x, y) = − E_ω (x, J y)`, the hypothesis `WeilHermitian` takes.

Source: Birkenhake–Lange, *Complex Abelian Varieties*, 2nd ed., Grundlehren 302, §5.1 (the Rosati
involution); proved here from `Symplectic.isRosatiSkew_iff_dualForm` and
`Symplectic.map_eq_smul_iff_isRosatiSkew`. -/
theorem isRosatiSkew_iff (hT : TorusCohomology μ) {η : HQ X 2}
    (hω : IsNondegenerate (polarizationVec hT η)) {d : ℚ} (hd : d ≠ 0) {J : HQ X 1 →ₗ[ℚ] HQ X 1}
    (hJ : J ∘ₗ J = -d • LinearMap.id) :
    (exteriorPower.map 2 J (polarizationVec hT η) = d • polarizationVec hT η ↔
        IsRosatiSkew (polarizationVec hT η) J) ∧
      (IsRosatiSkew (polarizationVec hT η) J ↔
        ∀ x y, polarizationForm hT hω (J x) y = -polarizationForm hT hω x (J y)) :=
  letI := hT.finite
  ⟨map_eq_smul_iff_isRosatiSkew hd hJ _, isRosatiSkew_iff_dualForm hω J⟩

end Polarization

section Datum

/-- **The Weil datum of a polarized Weil-type package (item 2).** For a Weil action `A` with
`J² = −d` on `H¹(X(ℂ); ℚ)`, a class `η` whose 2-vector `ω` is nondegenerate (`hω`) and satisfies
the Rosati condition for `J` (`hR`), the determinant class
`weilDetClass E_ω J ∈ ℚˣ ⧸ Nm(Kˣ)`, `K = ℚ(√−d)`, of the Weil-type Hermitian form
`h(x, y) = E_ω(x, J y) + √−d · E_ω(x, y)` (F-1712). For `d = 3` and `dim X = 6` this is the `[δ]` of
F-1569's family `M = (3, ℚ(√−3), [δ])`.

`A` is a Weil action on `H¹(X(ℂ); ℚ)`: a rational endomorphism `J` of `H¹` with `J² = −d` that
preserves the Hodge pieces. Such endomorphisms are exactly `End⁰(X)` acting on `H¹`
(Birkenhake–Lange, Ch. 1); that identification is not formalized.

Source: van Geemen, *An introduction to the Hodge conjecture for abelian varieties*, LNM 1594
(1994), §5 (the determinant of the Hermitian form of a Weil-type polarized abelian variety), through
`WeilHermitian.weilDetClass`. -/
noncomputable def weilDatumClass (hF : FiniteBetti X) (hB : BettiDeRhamIso X)
    (hD : HodgeDecomposition X) (hT : TorusCohomology μ) {d : ℚ}
    [Fact (∀ r : ℚ, r ^ 2 ≠ -d + 0 * r)]
    (A : letI := hT.finite
      HodgeBlocks.WeilAction (abelianVarietyCohomologyOf hF hB hD hT).weight1 d)
    {η : HQ X 2} (hω : IsNondegenerate (polarizationVec hT η))
    (hR : letI := hT.finite; IsRosatiSkew (polarizationVec hT η) A.J) :
    ℚˣ ⧸ normSubgroup (QuadraticAlgebra ℚ (-d) 0) :=
  letI := hT.finite
  weilDetClass (polarizationForm hT hω) ⟨A.J, A.J_sq⟩
    ((isRosatiSkew_iff_dualForm hω A.J).1 hR) (isAlt_polarizationForm hT hω)
    (nondegenerate_polarizationForm hT hω)

/-- The class `[−2] ∈ ℚˣ ⧸ Nm(ℚ(√−3)ˣ)`, F-1569's `δ`. The register's `[−2]` is the class of the
Gram determinant (`−2/81`, F-1569 (1)), with no sign factor; `[−2/81] = [−2]` since
`81 = Nm(9)`.

Source: F-1569 (1), through `HermitianForm.detClass`'s convention (determinant, no sign factor). -/
noncomputable def classNegTwo : ℚˣ ⧸ normSubgroup (QuadraticAlgebra ℚ (-3) 0) :=
  ((Units.mk0 (-2 : ℚ) (by norm_num) : ℚˣ) : ℚˣ ⧸ normSubgroup (QuadraticAlgebra ℚ (-3) 0))

/-- `[−2] ≠ [1]`: norms from `ℚ(√−3)` are positive (`HermitianForm.class_neg_two_ne_one`). -/
example : classNegTwo ≠ 1 := class_neg_two_ne_one

/-- `[−2] = [−2/81]`, the determinant in F-1569 (1) (`HermitianForm.classes_F1569`). -/
example : classNegTwo = ((Units.mk0 (-2 / 81 : ℚ) (by norm_num) : ℚˣ) :
    ℚˣ ⧸ normSubgroup (QuadraticAlgebra ℚ (-3) 0)) := classes_F1569.1.symm

end Datum

section Member

/-- **The polarization is positive: `E_ω` is a polarization of `H¹(X(ℂ); ℚ)` (Hodge–Riemann).**
There is a polarization `P` of the weight-one Hodge structure `S.weight1` (Blocks'
`HodgeBlocks.Polarisation`, the rational form of Cattani–El Zein–Griffiths–Lê, Definition 3.1.8)
whose form is `E_ω`. For weight one this says:
* `E_ω (x, y) = − E_ω (y, x)` and `E_ω` is nondegenerate;
* `H^{1,0}` and `H^{0,1}` are isotropic for `E_ω ⊗ ℂ` (the first Riemann relation: `η` has type
  `(1, 1)`; equivalently `E_ω (I x, I y) = E_ω (x, y)` for the complex structure `I` of `H¹_ℝ`);
* `i · E_ω(x, x̄) > 0` for `0 ≠ x ∈ H^{1,0}` (the second Riemann relation, positivity; it is
  `E_ω (x, I x) > 0` on `H¹_ℝ` for the complex structure `I` that is `−i` on `H^{1,0}`
  (equivalently, `i` on `H^{0,1}`)).

This is how "`η` is the class of a polarization (an ample class, up to `ℚ^×`)" enters: by Riemann's
theorem a rational weight-one Hodge structure with such a form is `H¹` of a polarized abelian
variety. The sign is fixed by `ω = (i/2) Σ dz_j ∧ dz̄_j` for the Kähler class of an ample bundle,
read through `Symplectic.contract`: `E_ω(dz, dz̄) = −2i`, so `i E_ω(dz, dz̄) = 2 > 0`. Replacing `η`
by `−η` flips the sign; since `−1 = (−1)` is a scalar, the Weil datum is unchanged at `dim_K = 6`
(`WeilHermitian.weilDetClass_smul_of_even`), so the sign convention does not change which
`(X, A)` are members of `M`.

It is a named condition in the predicate `IsMemberOfM`, not an assumption about every `X`; it is
not proved for any `X` here.

Source: Birkenhake–Lange, *Complex Abelian Varieties*, 2nd ed., Grundlehren 302, Ch. 4, §4.1–4.2
(Riemann relations, the positive definite Hermitian form of a polarization); Cattani–El Zein–
Griffiths–Lê, *Hodge Theory*, Definition 3.1.8 (through `HodgeBlocks.Polarisation`). -/
def PolarizationPositive (hF : FiniteBetti X) (hB : BettiDeRhamIso X)
    (hD : HodgeDecomposition X) (hT : TorusCohomology μ) {η : HQ X 2}
    (hω : IsNondegenerate (polarizationVec hT η)) : Prop :=
  letI := hT.finite
  ∃ P : HodgeBlocks.Polarisation (abelianVarietyCohomologyOf hF hB hD hT).weight1,
    P.form = polarizationForm hT hω

/-- **Membership in F-1569's family `M = (3, ℚ(√−3), [−2])` (item 3).** For an abelian `X` with
the package of C1, C2, C4 and C7, a Weil action `A` of `ℚ(√−3)` on `H¹(X(ℂ); ℚ)` (`J² = −3`) and a
class `η ∈ H²(X(ℂ); ℚ)`, `IsMemberOfM … A η` says:
* `dim X = 6` (an abelian sixfold; `dim_ℚ H¹ = 12`, so `dim_K H¹ = 6`);
* `A.IsWeilType` (`dim (V_s ∩ H^{1,0}) = dim (V_{s̄} ∩ H^{1,0}) = 3`: signature `(3, 3)` of the
  Hermitian form, by `WeilHermitian.hermSignature_weilHermitian` and the eigenspace dictionary,
  which is **not formalized**: `isWeilType_iff_hermSignature_eq` below takes it as the
  hypothesis `SignatureDictionary`);
* `IsNondegenerate ω` for `ω = polarizationVec hT η`;
* the Rosati condition `IsRosatiSkew ω J`, equivalently `⋀² J ω = 3 ω`, equivalently `J` skew for
  `E_ω` (`isRosatiSkew_iff`);
* `PolarizationPositive`: `E_ω` is a polarization (the Hodge–Riemann relations), so `η` is a
  polarization class;
* `weilDatumClass … = [−2]`.

This is F-1569's family `M = (3, ℚ(√−3), [−2])`. The `3` is half of `dim_K H¹ = 6`, and Weil type
is signature `(3, 3)`. At `dim_K = 6` the class depends on no choice: not the scale of `η`
(`weilDetClass_smul_of_even`, F-1712), not the sign of `J` (`[−1]^6 = 1`, F-1712's review, not
formalized), not dual versus original form (`[δ⁻¹] = [δ]`, F-1712's review, not formalized).

`A` is a Weil action on `H¹(X(ℂ); ℚ)`: a rational endomorphism `J` of `H¹` that preserves the Hodge
pieces. Such endomorphisms are exactly `End⁰(X)` acting on `H¹` (Birkenhake–Lange, Ch. 1); that
identification is not formalized.

Source: F-1569 (the family `M = (3, ℚ(√−3), [−2])`: an abelian sixfold of Weil type for
`ℚ(√−3)` whose Hermitian form has signature `(3, 3)` and determinant `−2/81`); van Geemen, LNM 1594,
§5 (Weil-type abelian varieties and their determinant). -/
structure IsMemberOfM (hF : FiniteBetti X) (hB : BettiDeRhamIso X)
    (hD : HodgeDecomposition X) (hT : TorusCohomology μ)
    (A : letI := hT.finite
      HodgeBlocks.WeilAction (abelianVarietyCohomologyOf hF hB hD hT).weight1 3)
    (η : HQ X 2) : Prop where
  dim_eq : dim X.left = 6
  isWeilType : letI := hT.finite; A.IsWeilType
  nondegenerate : IsNondegenerate (polarizationVec hT η)
  rosati : letI := hT.finite; IsRosatiSkew (polarizationVec hT η) A.J
  positive : PolarizationPositive hF hB hD hT nondegenerate
  datum : weilDatumClass hF hB hD hT A nondegenerate rosati = classNegTwo

/-- For a member of `M`, `k = dim (V_s ∩ H^{1,0}) = 3`: its Weil classes lie in `H⁶`. -/
theorem IsMemberOfM.finrank_eq_three {hF : FiniteBetti X} {hB : BettiDeRhamIso X}
    {hD : HodgeDecomposition X} {hT : TorusCohomology μ}
    {A : letI := hT.finite
      HodgeBlocks.WeilAction (abelianVarietyCohomologyOf hF hB hD hT).weight1 3}
    {η : HQ X 2} (h : IsMemberOfM hF hB hD hT A η) :
    letI := hT.finite
    Module.finrank ℂ ↥(A.Vs ⊓ (abelianVarietyCohomologyOf hF hB hD hT).weight1.H (1, 0)) = 3 := by
  have := two_mul_finrank_vs_inf_h10_eq hF hB hD hT (by norm_num) A h.isWeilType
  rw [h.dim_eq] at this
  omega

/-- For a member of `M`, `dim_K H¹ = 6` for `K = ℚ(√−3)` acting through `J`. -/
theorem IsMemberOfM.finrank_withJ {hF : FiniteBetti X} {hB : BettiDeRhamIso X}
    {hD : HodgeDecomposition X} {hT : TorusCohomology μ}
    {A : letI := hT.finite
      HodgeBlocks.WeilAction (abelianVarietyCohomologyOf hF hB hD hT).weight1 3}
    {η : HQ X 2} (h : IsMemberOfM hF hB hD hT A η) :
    letI := hT.finite
    finrank (QuadraticAlgebra ℚ (-3) 0) (WithJ (HQ X 1) ⟨A.J, A.J_sq⟩) = 6 := by
  let := hT.finite
  have h1 := WeilHermitian.finrank_withJ (V := HQ X 1) ⟨A.J, A.J_sq⟩
  rw [hT.finrank_eq, h.dim_eq] at h1
  omega

end Member

section Statement

/-- **F-1569 for a chosen cup product, stated (not proved).** Fix one cup product `cup X` for every
smooth projective integral `X`; this is intended to be the topological cup product, which will be
constructed in torus-track stage S7. For every abelian `X` (over `ℂ`, integral, smooth,
projective, with a group structure) with C1, C2, C4 and C7, every Weil action `A` of
`ℚ(√−3)` on `H¹(X(ℂ); ℚ)` (`J² = −3`) of Weil type, and every class `η ∈ H²`: if `(X, A, η)` is a
member of `M = (3, ℚ(√−3), [−2])` (`IsMemberOfM`), then the rational Weil classes of `A` are
algebraic (`WeilClassesAlgebraic`, against upstream's `algebraicCycleClassSpan`).

F-1569's claim, word for word: "the rational Weil classes are algebraic on every member of
`M = (3, ℚ(√−3), [−2])`".

**This is stated, not proved; nothing in this repository proves it.** It is a definition, used
as a premise; every theorem that takes it lists it in its hypothesis table.

**Conditional on the package.** C1 (`FiniteBetti`), C2 (`BettiDeRhamIso`), C4
(`HodgeDecomposition`) and C7 (`TorusCohomology`) enter through the package `S`: they are bound for
each `X`, so the statement says nothing about an `X` for which one of them fails. F-1569 itself is
about abelian sixfolds over `ℂ`, which satisfy all four classically (Hatcher §3.1, Voisin I Ch. 6,
Birkenhake–Lange Lemma 1.3.1); none of them is proved in this repository.

**Binders and scope.**
* `X` with `[GrpObj X]` and C7: an abelian variety with its torus cohomology. `IsMemberOfM` adds
  `dim X = 6`.
* `A`, `hW`: any rational endomorphism of `H¹` with `J² = −3` preserving the Hodge pieces, of Weil
  type. Hodge-preserving rational endomorphisms of `H¹` are exactly `End⁰(X)` (Birkenhake–Lange,
  Ch. 1; not formalized), so this is F-1569's `ℚ(√−3)`-action. `hW` duplicates
  `IsMemberOfM.isWeilType`; `WeilClassesAlgebraic` needs it as an argument, and since it is a
  proof, its choice does not matter.
* `η`: any class whose 2-vector is nondegenerate, Rosati-compatible with `J`, **a polarization**
  (`PolarizationPositive`) and of Weil datum `[−2]`. Without positivity the statement would be
  stronger than F-1569. Every nondegenerate `K`-Hermitian form on `H¹` is `weilHermitian E J` for
  the `J`-skew alternating form `E` that is its `ω`-coefficient, and on `K⁶` there are Hermitian
  forms of determinant `−2` with signature `(5, 1)`. So on any Weil-type sixfold for `ℚ(√−3)`, of
  any family, some non-polarization `E` (hence some `η`) has class `[−2]`, and without positivity
  every such sixfold would count as a member of `M`.
* `cup`: one chosen cup product for each smooth projective integral `X`. F-1569 is recovered when
  this family is the topological cup product. Until S7 constructs that family, it is an explicit
  parameter; choosing a different family gives a different statement.
* Non-vacuity: `IsMemberOfM` is satisfiable for real abelian sixfolds in `M` (F-1569's family is
  nonempty, by the construction behind F-1569); this is not checked in Lean, since Lean has no
  abelian sixfold with this package.

`A` is a Weil action on `H¹(X(ℂ); ℚ)`: a rational endomorphism `J` of `H¹` that preserves the Hodge
pieces. Such endomorphisms are exactly `End⁰(X)` acting on `H¹` (Birkenhake–Lange, Ch. 1); that
identification is not formalized.

Source: F-1569 (register), its family `M = (3, ℚ(√−3), [−2])` (`IsMemberOfM`) and its claim
(`WeilClassesAlgebraic`, F-1708).

Relation to the goal: HC no distance. AV milestone no distance. F-1569 becomes a precise Lean
statement; it is not proved. -/
def F1569StatementFor (cup : ∀ (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom]
    [IsProjective X.hom], CupProduct X) : Prop :=
  ∀ (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] [GrpObj X]
    (hF : FiniteBetti X) (hB : BettiDeRhamIso X) (hD : HodgeDecomposition X)
    (hT : TorusCohomology (cup X))
    (A : letI := hT.finite
      HodgeBlocks.WeilAction (abelianVarietyCohomologyOf hF hB hD hT).weight1 3)
    (hW : letI := hT.finite; A.IsWeilType) (η : HQ X 2),
    IsMemberOfM hF hB hD hT A η → WeilClassesAlgebraic hF hB hD hT A hW

/-- **Consistency: `F1569StatementFor cup` gives F-1569 for each member when `cup` is the
topological cup product.** Applied to one member `(X, A, η)` of `M`, it gives
`WeilClassesAlgebraic A`, the claim for that `X` (F-1708). The family `cup` remains a parameter
until S7 constructs the topological family; `F1569StatementFor cup` is **stated, not proved**.

| hypothesis | roadmap / role |
| --- | --- |
| `cup` | chosen cup-product family; topological cup product for F-1569, parameter until S7 |
| `hF1569 : F1569StatementFor cup` | F-1569 for `cup`: **stated, not proved** |
| `hF hB hD hT` | C1, C2, C4, C7 |
| `A`, `η`, `hM : IsMemberOfM … A η` | a member of `M` |

Relation to the goal: HC no distance. AV milestone no distance. -/
theorem weilClassesAlgebraic_of_f1569Statement
    (cup : ∀ (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom]
      [IsProjective X.hom], CupProduct X) (hF1569 : F1569StatementFor cup)
    (hF : FiniteBetti X) (hB : BettiDeRhamIso X) (hD : HodgeDecomposition X)
    (hT : TorusCohomology (cup X))
    (A : letI := hT.finite
      HodgeBlocks.WeilAction (abelianVarietyCohomologyOf hF hB hD hT).weight1 3)
    {η : HQ X 2} (hM : IsMemberOfM hF hB hD hT A η) :
    WeilClassesAlgebraic hF hB hD hT A hM.isWeilType :=
  hF1569 X hF hB hD hT A hM.isWeilType η hM

/-- The same, with the Weil-type proof given separately, as `F1569StatementFor cup` binds it. -/
example (cup : ∀ (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom]
    [IsProjective X.hom], CupProduct X) (hF1569 : F1569StatementFor cup)
    (hF : FiniteBetti X) (hB : BettiDeRhamIso X)
    (hD : HodgeDecomposition X) (hT : TorusCohomology (cup X))
    (A : letI := hT.finite
      HodgeBlocks.WeilAction (abelianVarietyCohomologyOf hF hB hD hT).weight1 3)
    (hW : letI := hT.finite; A.IsWeilType) {η : HQ X 2} (hM : IsMemberOfM hF hB hD hT A η) :
    WeilClassesAlgebraic hF hB hD hT A hW :=
  hF1569 X hF hB hD hT A hW η hM

/-- **F-1569 plus generation gives HC on each member of `M` (item 6).** For a member `(X, A, η)` of
`M = (3, ℚ(√−3), [−2])`: `F1569StatementFor cup`, generation of the Hodge ring by divisors and the Weil
classes of `A`, C9 and Lefschetz (1,1) give `Hdg^p(X; ℚ) ≤ algebraicCycleClassSpan X p` for every
`p`, upstream's Hodge conjecture for `X`. It is the connector `hdg_le_span_of_weilClassesAlgebraic`
(F-1708) applied to `weilClassesAlgebraic_of_f1569Statement`.

This is the formal form of "F-1569 plus generation gives HC on each member of `M`".

`A` is a Weil action on `H¹(X(ℂ); ℚ)`: a rational endomorphism `J` of `H¹` that preserves the Hodge
pieces. Such endomorphisms are exactly `End⁰(X)` acting on `H¹` (Birkenhake–Lange, Ch. 1); that
identification is not formalized.

Source: the reduction is `hdg_le_span_of_weilClassesAlgebraic` (Fulton, *Intersection Theory*,
Corollary 19.2, through `CycleClassMultiplicative`; Griffiths–Harris, Ch. 1 §2, through
`LefschetzOneOneHyp`); the generation hypothesis is van Geemen, LNM 1594 (Hodge group `SU_H`),
through `HodgeRingGeneratedByDivisorsAndWeil`.

| hypothesis | roadmap / role |
| --- | --- |
| `cup` | chosen cup-product family; topological cup product for F-1569, parameter until S7 |
| `hF1569 : F1569StatementFor cup` | F-1569 for `cup`: **stated, not proved** |
| `hF hB hD hT` | C1, C2, C4, C7; fix the package `S` |
| `A`, `η`, `hM : IsMemberOfM … A η` | a member of `M` |
| `hGen : HodgeRingGeneratedByDivisorsAndWeil A hM.isWeilType` | generation: **not proved**; for the sixfolds of `M` it is F-1575's case `m = 1` (Hodge group `SU_H`, van Geemen) |
| `hC9 : CycleClassMultiplicative μ` | C9 |
| `h11 : LefschetzOneOneHyp` | Lefschetz (1,1) |

Relation to the goal: HC no distance. AV milestone no distance; HC on each member of `M` is
reduced to F-1569 plus generation, both outside Lean. -/
@[hodge_milestone] theorem hdg_le_span_of_f1569Statement
    (cup : ∀ (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom]
      [IsProjective X.hom], CupProduct X) (hF1569 : F1569StatementFor cup)
    (hF : FiniteBetti X) (hB : BettiDeRhamIso X) (hD : HodgeDecomposition X)
    (hT : TorusCohomology (cup X))
    (A : letI := hT.finite
      HodgeBlocks.WeilAction (abelianVarietyCohomologyOf hF hB hD hT).weight1 3)
    {η : HQ X 2} (hM : IsMemberOfM hF hB hD hT A η)
    (hGen : HodgeRingGeneratedByDivisorsAndWeil hF hB hD hT A hM.isWeilType)
    (hC9 : CycleClassMultiplicative (cup X)) (h11 : LefschetzOneOneHyp) :
    ∀ p : ℕ, Hdg^p(X; ℚ) ≤ algebraicCycleClassSpan X p :=
  hdg_le_span_of_weilClassesAlgebraic hF hB hD hT A hM.isWeilType
    (weilClassesAlgebraic_of_f1569Statement cup hF1569 hF hB hD hT A hM) hGen hC9 h11

end Statement

section Signature

/-- **Weil type is a balance between `H^{1,0}` and `H^{0,1}` inside `V_s`.** `A.IsWeilType`
(`2 · dim (V_s ∩ H^{1,0}) = dim V_s`) holds iff `dim (V_s ∩ H^{1,0}) = dim (V_s ∩ H^{0,1})`, since
`V_s = (V_s ∩ H^{1,0}) ⊕ (V_s ∩ H^{0,1})` (Blocks' `Vs_eq_sup`, `inf_H10_H01_Vs`). This is the
complex half of the signature dictionary (item 4).

`A` is a Weil action on `H¹(X(ℂ); ℚ)`: a rational endomorphism `J` of `H¹` that preserves the Hodge
pieces, which is `End⁰(X)` acting on `H¹` (Birkenhake–Lange, Ch. 1); that identification is not
formalized. -/
theorem isWeilType_iff_finrank_eq (hF : FiniteBetti X) (hB : BettiDeRhamIso X)
    (hD : HodgeDecomposition X) (hT : TorusCohomology μ) {d : ℚ}
    (A : letI := hT.finite
      HodgeBlocks.WeilAction (abelianVarietyCohomologyOf hF hB hD hT).weight1 d) :
    letI := hT.finite
    A.IsWeilType ↔
      finrank ℂ ↥(A.Vs ⊓ (abelianVarietyCohomologyOf hF hB hD hT).weight1.H (1, 0)) =
        finrank ℂ ↥(A.Vs ⊓ (abelianVarietyCohomologyOf hF hB hD hT).weight1.H (0, 1)) := by
  let := hT.finite
  have hdim := Submodule.finrank_sup_add_finrank_inf_eq
    (A.Vs ⊓ (abelianVarietyCohomologyOf hF hB hD hT).weight1.H (1, 0))
    (A.Vs ⊓ (abelianVarietyCohomologyOf hF hB hD hT).weight1.H (0, 1))
  rw [A.inf_H10_H01_Vs, ← A.Vs_eq_sup (h10_sup_h01_eq_top hF hB hD hT), finrank_bot,
    add_zero] at hdim
  unfold HodgeBlocks.WeilAction.IsWeilType
  omega

/-- Conjugation: `dim (V_{s̄} ∩ H^{0,1}) = dim (V_s ∩ H^{1,0})`. -/
theorem finrank_Vsbar_inf_H01 (hF : FiniteBetti X) (hB : BettiDeRhamIso X)
    (hD : HodgeDecomposition X) (hT : TorusCohomology μ) {d : ℚ}
    (A : letI := hT.finite
      HodgeBlocks.WeilAction (abelianVarietyCohomologyOf hF hB hD hT).weight1 d) :
    letI := hT.finite
    finrank ℂ ↥(A.Vsbar ⊓ (abelianVarietyCohomologyOf hF hB hD hT).weight1.H (0, 1)) =
      finrank ℂ ↥(A.Vs ⊓ (abelianVarietyCohomologyOf hF hB hD hT).weight1.H (1, 0)) := by
  let := hT.finite
  rw [← A.map_inf_Vs_H10_sigmaQ]
  exact HodgeBlocks.WeilAction.finrank_map_sigmaQ _

/-- **The signature dictionary for a complex structure `I` on `H¹_ℝ` (stated, not proved).**
For `I : ℝ ⊗ H¹ → ℝ ⊗ H¹`, the real dimensions of the two kernels of
`hermSignature_weilHermitian` are twice the complex dimensions of the eigenspace pieces in
`H^{0,1}`:
* `dim_ℝ ker (J - √d I) = 2 · dim_ℂ (V_s ∩ H^{0,1})`;
* `dim_ℝ ker (J + √d I) = 2 · dim_ℂ (V_{s̄} ∩ H^{0,1})`.

It holds for the complex structure `I` of `H¹_ℝ = ℝ ⊗ H¹(X; ℚ)` that acts by `i` on `H^{0,1}`
(and by `-i` on `H^{1,0}`): `x ↦ π^{0,1}(x)` is an `ℝ`-isomorphism `H¹_ℝ ≅ H^{0,1}` carrying `I`
to `i`, and it carries `ker (J ∓ √d I)` onto `V_{s} ∩ H^{0,1}`, resp. `V_{s̄} ∩ H^{0,1}`
(`J v = ±i√d v`). With that `I`, the Hodge–Riemann positivity of `PolarizationPositive`,
`i · E_ω(h, h̄) > 0` on `H^{1,0}`, is `E_ω (x, I x) > 0` on `H¹_ℝ`: for `x = h + h̄`,
`I x = -i h + i h̄`, so `E_ω (x, I x) = 2i E_ω(h, h̄) · (-1) · (-1) = 2 · i E_ω(h, h̄)` up to the
isotropy of `H^{1,0}`. **Neither the construction of `I` from the Hodge decomposition nor these
two identities is formalized**: this structure is the disclosed gap of item 4.

Source: van Geemen, *An introduction to the Hodge conjecture for abelian varieties*, LNM 1594
(1994), §5 (the signature of the Hermitian form of a Weil-type abelian variety, read off the
eigenspaces in `H^{1,0}`); Birkenhake–Lange, *Complex Abelian Varieties*, 2nd ed., Grundlehren 302,
Ch. 1 (`H¹_ℝ ≅ H^{0,1}` for a complex torus) and Ch. 4 (Riemann relations). -/
@[hodge_hypothesis]
structure SignatureDictionary (hF : FiniteBetti X) (hB : BettiDeRhamIso X)
    (hD : HodgeDecomposition X) (hT : TorusCohomology μ) {d : ℚ}
    (A : letI := hT.finite
      HodgeBlocks.WeilAction (abelianVarietyCohomologyOf hF hB hD hT).weight1 d)
    (I : ℝ ⊗[ℚ] HQ X 1 →ₗ[ℝ] ℝ ⊗[ℚ] HQ X 1) : Prop where
  ker_sub : letI := hT.finite
    finrank ℝ ↥(LinearMap.ker (A.J.baseChange ℝ - √(d : ℝ) • I)) =
      2 * finrank ℂ ↥(A.Vs ⊓ (abelianVarietyCohomologyOf hF hB hD hT).weight1.H (0, 1))
  ker_add : letI := hT.finite
    finrank ℝ ↥(LinearMap.ker (A.J.baseChange ℝ + √(d : ℝ) • I)) =
      2 * finrank ℂ ↥(A.Vsbar ⊓ (abelianVarietyCohomologyOf hF hB hD hT).weight1.H (0, 1))

/-- `J` is skew for `E_ω`, from the Rosati condition. -/
theorem polarizationForm_skew (hT : TorusCohomology μ) {η : HQ X 2}
    (hω : IsNondegenerate (polarizationVec hT η)) {J : HQ X 1 →ₗ[ℚ] HQ X 1}
    (hR : IsRosatiSkew (polarizationVec hT η) J) :
    ∀ x y, polarizationForm hT hω (J x) y = -polarizationForm hT hω x (J y) :=
  letI := hT.finite
  (isRosatiSkew_iff_dualForm hω J).1 hR

/-- **The signature of the polarized Weil-type package (item 4, conditional on the dictionary).**
For a complex structure `I` on `H¹_ℝ` commuting with `J`, with `E_ω (x, I x) > 0`
(`hpos`, the Hodge–Riemann positivity in real form) and satisfying the dictionary
`SignatureDictionary` (not proved), the Hermitian form `weilHermitian E_ω J` has signature
`(dim (V_s ∩ H^{0,1}), dim (V_s ∩ H^{1,0}))` = `(s, r)`. With `I` that is `i` on `H^{1,0}` and the
opposite positivity the order would be `(r, s)` (T4's docstring); whether `r = s` does not depend
on it.

`A` is a Weil action on `H¹(X(ℂ); ℚ)`: a rational endomorphism `J` of `H¹` that preserves the Hodge
pieces, which is `End⁰(X)` acting on `H¹` (Birkenhake–Lange, Ch. 1); that identification is not
formalized.

| hypothesis | role |
| --- | --- |
| `hF hB hD hT` | C1, C2, C4, C7; fix the package |
| `hd : 0 < d` | `K = ℚ(√−d)` imaginary quadratic |
| `hω`, `hR` | `ω` nondegenerate and Rosati-compatible with `J` |
| `I`, `hI`, `hIJ`, `hpos` | a complex structure on `H¹_ℝ` commuting with `J`, positive for `E_ω` |
| `hdict : SignatureDictionary A I` | the eigenspace dictionary: **not proved** (item 4's gap) |

Source: van Geemen, LNM 1594, §5, through `WeilHermitian.hermSignature_weilHermitian` (F-1712). -/
theorem hermSignature_polarizationForm (hF : FiniteBetti X) (hB : BettiDeRhamIso X)
    (hD : HodgeDecomposition X) (hT : TorusCohomology μ) {d : ℚ} (hd : 0 < d)
    [Fact (∀ r : ℚ, r ^ 2 ≠ -d + 0 * r)]
    (A : letI := hT.finite
      HodgeBlocks.WeilAction (abelianVarietyCohomologyOf hF hB hD hT).weight1 d)
    {η : HQ X 2} (hω : IsNondegenerate (polarizationVec hT η))
    (hR : letI := hT.finite; IsRosatiSkew (polarizationVec hT η) A.J)
    (I : ℝ ⊗[ℚ] HQ X 1 →ₗ[ℝ] ℝ ⊗[ℚ] HQ X 1) (hI : ∀ x, I (I x) = -x)
    (hIJ : letI := hT.finite; ∀ x, I (A.J.baseChange ℝ x) = A.J.baseChange ℝ (I x))
    (hpos : ∀ x, x ≠ 0 → 0 < (polarizationForm hT hω).baseChange ℝ x (I x))
    (hdict : SignatureDictionary hF hB hD hT A I) :
    letI := hT.finite
    hermSignature (weilHermitian (polarizationForm hT hω) ⟨A.J, A.J_sq⟩
        (polarizationForm_skew hT hω hR)) =
      (finrank ℂ ↥(A.Vs ⊓ (abelianVarietyCohomologyOf hF hB hD hT).weight1.H (0, 1)),
        finrank ℂ ↥(A.Vs ⊓ (abelianVarietyCohomologyOf hF hB hD hT).weight1.H (1, 0))) := by
  let := hT.finite
  rw [hermSignature_weilHermitian (J := ⟨A.J, A.J_sq⟩) hd _ I hI hIJ hpos, hdict.ker_sub,
    hdict.ker_add, finrank_Vsbar_inf_H01]
  simp

/-- **Weil type is signature `(3, 3)`, for a sixfold (item 4, conditional on the dictionary).**
For `dim X = 6`, `d > 0`, and `I` as in `hermSignature_polarizationForm`: `A.IsWeilType` iff
`hermSignature (weilHermitian E_ω J) = (3, 3)`. So, granted `SignatureDictionary` (not proved), the
condition `A.IsWeilType` in `IsMemberOfM` is F-1569's "signature `(3, 3)`".

`A` is a Weil action on `H¹(X(ℂ); ℚ)`: a rational endomorphism `J` of `H¹` that preserves the Hodge
pieces, which is `End⁰(X)` acting on `H¹` (Birkenhake–Lange, Ch. 1); that identification is not
formalized.

| hypothesis | role |
| --- | --- |
| `hF hB hD hT` | C1, C2, C4, C7 |
| `hd : 0 < d`, `hdim : dim X = 6` | imaginary quadratic `K`, a sixfold |
| `hω`, `hR`, `I`, `hI`, `hIJ`, `hpos` | as in `hermSignature_polarizationForm` |
| `hdict : SignatureDictionary A I` | the eigenspace dictionary: **not proved** (item 4's gap) |

Source: van Geemen, LNM 1594, §5 (Weil type is signature `(n/2, n/2)`); F-1569 (1) ("signature
`(3, 3)`"). -/
theorem isWeilType_iff_hermSignature_eq (hF : FiniteBetti X) (hB : BettiDeRhamIso X)
    (hD : HodgeDecomposition X) (hT : TorusCohomology μ) {d : ℚ} (hd : 0 < d)
    [Fact (∀ r : ℚ, r ^ 2 ≠ -d + 0 * r)] (hdim : dim X.left = 6)
    (A : letI := hT.finite
      HodgeBlocks.WeilAction (abelianVarietyCohomologyOf hF hB hD hT).weight1 d)
    {η : HQ X 2} (hω : IsNondegenerate (polarizationVec hT η))
    (hR : letI := hT.finite; IsRosatiSkew (polarizationVec hT η) A.J)
    (I : ℝ ⊗[ℚ] HQ X 1 →ₗ[ℝ] ℝ ⊗[ℚ] HQ X 1) (hI : ∀ x, I (I x) = -x)
    (hIJ : letI := hT.finite; ∀ x, I (A.J.baseChange ℝ x) = A.J.baseChange ℝ (I x))
    (hpos : ∀ x, x ≠ 0 → 0 < (polarizationForm hT hω).baseChange ℝ x (I x))
    (hdict : SignatureDictionary hF hB hD hT A I) :
    letI := hT.finite
    A.IsWeilType ↔
      hermSignature (weilHermitian (polarizationForm hT hω) ⟨A.J, A.J_sq⟩
        (polarizationForm_skew hT hω hR)) = (3, 3) := by
  let := hT.finite
  rw [hermSignature_polarizationForm hF hB hD hT hd A hω hR I hI hIJ hpos hdict,
    isWeilType_iff_finrank_eq]
  -- `dim V_s = dim X = 6`, as in `two_mul_finrank_vs_inf_h10_eq`
  have hsum := Submodule.finrank_sup_add_finrank_inf_eq A.Vs A.Vsbar
  have hc := HodgeBlocks.WeilAction.isCompl_Vs_Vsbar A hd
  rw [hc.sup_eq_top, hc.inf_eq_bot, finrank_top, finrank_bot, add_zero,
    Module.finrank_baseChange, hT.finrank_eq, A.finrank_Vsbar_eq_Vs, hdim] at hsum
  have hdim2 := Submodule.finrank_sup_add_finrank_inf_eq
    (A.Vs ⊓ (abelianVarietyCohomologyOf hF hB hD hT).weight1.H (1, 0))
    (A.Vs ⊓ (abelianVarietyCohomologyOf hF hB hD hT).weight1.H (0, 1))
  rw [A.inf_H10_H01_Vs, ← A.Vs_eq_sup (h10_sup_h01_eq_top hF hB hD hT), finrank_bot,
    add_zero] at hdim2
  constructor
  · intro h
    ext <;> simp <;> omega
  · intro h
    simp only [Prod.mk.injEq] at h
    omega

end Signature

end HodgeLean.RealDefs
