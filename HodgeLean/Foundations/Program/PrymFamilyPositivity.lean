import HodgeLean.Foundations.Program.PrymFamilyPositivityProofs

/-! # B6-3g, part 4: the `positive` field of the Prym family (FROZEN SPEC)

Each public theorem is the matching `_aux` theorem of `PrymFamilyPositivityProofs.lean`.

**Claimed.** For a complex abelian variety `X` with lattice `Λ_X = H₁(X(ℂ), ℤ)` and an integral
form `Q` on `Λ_X`, write `ω` for the 2-vector of the class `latticeClassHQ X Q` (the convention of
part 1's `b63g_modelClass`) and `E_ω = polarizationForm` for its inverse-contraction form on
`H¹(X(ℂ); ℚ)`. Then:

* on homology, `B_ω(a, b) = b (contract ω a)` restricted to the lattice is `Q` itself, with no
  sign and no factor: `contract ω (ev l) = P⁻¹ (Q (l, ·))` when `Q` is alternating;
* on cohomology, `E_ω (P⁻¹ Q(l, ·), P⁻¹ Q(m, ·)) = Q (l, m)`, also after complexification;
* the complexified row map carries homology conjugation to `sigmaQ`, and maps the period
  filtration `b2_abelianF X` onto the Hodge piece `H^{1,0}` of the package;
* so, when `Q` is a Riemann form for `b2_abelianF X` (`b2_IsRiemannForm`), `H^{1,0}` and `H^{0,1}`
  are isotropic for `E_ω ⊗ ℂ`, `Re (i · E_ω(x, σ x)) > 0` on nonzero `x ∈ H^{1,0}`, and
  `PolarizationPositive` holds for `latticeClassHQ X Q`, with the class not negated;
* the opposite sign fails: for `dim X > 0`, the class `-latticeClassHQ X Q` is not
  `PolarizationPositive`.

These are implications from a Riemann form on the period lattice. With part 1
(`b63g_modelForm_riemann`) they give the field `positive` of `g32h_PrymFamily` and of
`IsMemberOfM` for the part-1 sixfold of any B5 lattice data, and on the moving fibres of 3f (chain
examples at the end of the file). The sign is fixed on the standard elliptic data
`(ℤ², b2_stdF, b2_stdForm)`: there the form `-b2_stdForm` is not a Riemann form (proved below), the
class of part 1 is positive and its negative is not.

**Not claimed.** That the Prym centre operator satisfies the lattice hypotheses of part 1 on the
transported filtration (part 2); the Hodge numbers (part 3); the assembly of `g32h_PrymFamily`
over `V` with marked Nielsen tuples (part 5); the rational `d1_PolarizedVHS` (part 6); that
`latticeClassHQ X Q` is the class of an ample line bundle. Nothing here concerns a discriminant,
algebraicity of Weil classes or dominance. HC no distance; AV milestone no distance.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint HodgeLean.RealDefs
open HodgeLean.Adapters HodgeLean.Foundations HodgeLean.Foundations.Symplectic TopologicalSpace
open HodgeLean.Foundations.AppellHumbert HodgeLean.Papers
open scoped TensorProduct Manifold ContDiff

namespace HodgeLean.Foundations.Program
attribute [local instance] b4cov_sphChartedSpace b4cov_sph_isManifold

/-! ## The original form on homology and on cohomology -/

/-- **`B_ω` on the lattice is `Q`.** For an alternating integral form `Q` on `Λ_X` and
`ω = polarizationVec (latticeClassHQ X Q)`, the contraction of `ω` with the evaluation at `l` is
the class of the row `Q (l, ·)`. Hence `B_ω(ev l, ev m) = (ev m)(contract ω (ev l)) = Q (l, m)`:
the alternating form of `ω` on `H₁ ⊗ ℚ = (H¹)^∨` is the original `Q`, not `-Q` and not `Q / 2`.
Source: Birkenhake–Lange, *Complex Abelian Varieties*, 2nd ed., §1.3 and Lemma 1.3.1
(`H²(X, ℤ) = Alt²(Λ, ℤ)`); `latticeClass` (the factor `1/2` and the alternation cancel);
`Symplectic.contract_ιMulti`. -/
theorem b63g4_contract_eval (X : Over (Spec ↧ℂ)) [GrpObj X] [IsIntegral X.left]
    [Smooth X.hom] [IsProjective X.hom] (Q : LinearMap.BilinForm ℤ (b2_abelianLattice X))
    (halt : ∀ l, Q l l = 0) (l : b2_abelianLattice X) :
    contract (polarizationVec (torusCohomology_cupProductOf X)
        (latticeClassHQ X (b2_bilinToAddHom Q))) (b63g4_periodEval X l) =
      b63g4_column X Q l :=
  b63g4_contract_eval_aux X Q halt l

example (X : Over (Spec ↧ℂ)) [GrpObj X] [IsIntegral X.left]
    [Smooth X.hom] [IsProjective X.hom] (Q : LinearMap.BilinForm ℤ (b2_abelianLattice X))
    (halt : ∀ l, Q l l = 0) (l m : b2_abelianLattice X) :
    b63g4_periodEval X m (contract (polarizationVec (torusCohomology_cupProductOf X)
        (latticeClassHQ X (b2_bilinToAddHom Q))) (b63g4_periodEval X l)) = (Q l m : ℚ) := by
  rw [b63g4_contract_eval X Q halt l]
  simp [b63g4_periodEval, b63g4_column, b2_bilinToAddHom]

/-- **The inverse-contraction form on the row classes is `Q`.** For a Riemann form `Q`, the form
`E_ω = polarizationForm` of `RealDefs.F1569`, `E_ω (x, y) = (contract ω)⁻¹ y x`, takes the value
`Q (l, m)` on the row classes of `l` and `m`: dualizing twice returns the original form.
Source: Birkenhake–Lange, §4.1–§4.2 (the dual polarization); `polarizationForm`,
`Symplectic.dualForm`; `b2b_dualForm` (the same identity on `Hom(Λ, ℚ)`). -/
theorem b63g4_polarizationForm_column (X : Over (Spec ↧ℂ)) [GrpObj X] [IsIntegral X.left]
    [Smooth X.hom] [IsProjective X.hom] (Q : LinearMap.BilinForm ℤ (b2_abelianLattice X))
    (hQ : b2_IsRiemannForm (b2_abelianLattice X) (b2_abelianF X) Q)
    (l m : b2_abelianLattice X) :
    polarizationForm (torusCohomology_cupProductOf X) (b2_abelian_nondegenerate X Q hQ)
        (b63g4_column X Q l) (b63g4_column X Q m) = (Q l m : ℚ) :=
  b63g4_polarizationForm_column_aux X Q hQ l m

example (X : Over (Spec ↧ℂ)) [GrpObj X] [IsIntegral X.left]
    [Smooth X.hom] [IsProjective X.hom] (Q : LinearMap.BilinForm ℤ (b2_abelianLattice X))
    (hQ : b2_IsRiemannForm (b2_abelianLattice X) (b2_abelianF X) Q)
    (l m : b2_abelianLattice X) :
    polarizationForm (torusCohomology_cupProductOf X) (b2_abelian_nondegenerate X Q hQ)
        (b63g4_column X Q l) (b63g4_column X Q m) = (Q l m : ℚ) :=
  b63g4_polarizationForm_column X Q hQ l m

/-- **The complexified comparison.** `E_ω ⊗ ℂ` on the complexified row map is `Q ⊗ ℂ`.
Source: bilinearity of base change; `b63g4_polarizationForm_column`. -/
theorem b63g4_polarizationForm_cplx (X : Over (Spec ↧ℂ)) [GrpObj X] [IsIntegral X.left]
    [Smooth X.hom] [IsProjective X.hom] (Q : LinearMap.BilinForm ℤ (b2_abelianLattice X))
    (hQ : b2_IsRiemannForm (b2_abelianLattice X) (b2_abelianF X) Q)
    (u v : ℂ ⊗[ℤ] b2_abelianLattice X) :
    (polarizationForm (torusCohomology_cupProductOf X)
        (b2_abelian_nondegenerate X Q hQ)).baseChange ℂ
        (b63g4_cplxColumn X Q u) (b63g4_cplxColumn X Q v) =
      Q.baseChange ℂ u v :=
  b63g4_polarizationForm_cplx_aux X Q hQ u v

example (X : Over (Spec ↧ℂ)) [GrpObj X] [IsIntegral X.left]
    [Smooth X.hom] [IsProjective X.hom] (Q : LinearMap.BilinForm ℤ (b2_abelianLattice X))
    (hQ : b2_IsRiemannForm (b2_abelianLattice X) (b2_abelianF X) Q)
    (u v : ℂ ⊗[ℤ] b2_abelianLattice X) :
    (polarizationForm (torusCohomology_cupProductOf X)
        (b2_abelian_nondegenerate X Q hQ)).baseChange ℂ
        (b63g4_cplxColumn X Q u) (b63g4_cplxColumn X Q v) =
      Q.baseChange ℂ u v :=
  b63g4_polarizationForm_cplx X Q hQ u v

/-! ## Conjugation and the Hodge pieces -/

/-- **Conjugation.** The complexified row map carries the conjugation `b2_conj` of complex
homology to the conjugation `sigmaQ` of complex cohomology: the row map is defined over `ℤ`.
Source: Deligne, *Théorie de Hodge II*, Publ. Math. IHES 40, §1.2 (real structures);
`b2_conj`, `HodgeBlocks.sigmaQ`. -/
theorem b63g4_cplxColumn_conj (X : Over (Spec ↧ℂ)) [GrpObj X] [IsIntegral X.left]
    [Smooth X.hom] [IsProjective X.hom] (Q : LinearMap.BilinForm ℤ (b2_abelianLattice X))
    (u : ℂ ⊗[ℤ] b2_abelianLattice X) :
    b63g4_cplxColumn X Q (b2_conj _ u) =
      HodgeBlocks.sigmaQ (HQ X 1) (b63g4_cplxColumn X Q u) :=
  b63g4_cplxColumn_conj_aux X Q u

example (X : Over (Spec ↧ℂ)) [GrpObj X] [IsIntegral X.left]
    [Smooth X.hom] [IsProjective X.hom] (Q : LinearMap.BilinForm ℤ (b2_abelianLattice X))
    (u : ℂ ⊗[ℤ] b2_abelianLattice X) :
    b63g4_cplxColumn X Q (b2_conj _ u) =
      HodgeBlocks.sigmaQ (HQ X 1) (b63g4_cplxColumn X Q u) :=
  b63g4_cplxColumn_conj X Q u

/-- **The Hodge piece `H^{1,0}` is the image of the period filtration.** For a Riemann form `Q`,
the complexified row map sends `F = b2_abelianF X` onto the piece `(1, 0)` of the package's
weight-one structure. Under period duality `H^{1,0}` is the annihilator of `F`
(`b60b_h10_period`); isotropy of `F` puts the image of `F` inside it, and the image has the same
dimension `g` since `Q` is nondegenerate (`b2bpol_hodgeOne_eq_map`).
Source: Birkenhake–Lange, §1.4 and §4.2; `b60b_h10_period`, `b2bpol_hodgeOne_eq_map`. -/
theorem b63g4_h10_eq_map (X : Over (Spec ↧ℂ)) [GrpObj X] [IsIntegral X.left]
    [Smooth X.hom] [IsProjective X.hom] (Q : LinearMap.BilinForm ℤ (b2_abelianLattice X))
    (hQ : b2_IsRiemannForm (b2_abelianLattice X) (b2_abelianF X) Q) :
    letI := (torusCohomology_cupProductOf X).finite
    (abelianVarietyCohomologyOf (finiteBetti_abelian X) (spec_bettiDeRhamIso_abelian X)
        (hodgeDecomposition_of_abelian X) (torusCohomology_cupProductOf X)).weight1.H (1, 0) =
      (b2_abelianF X).map (b63g4_cplxColumn X Q) :=
  b63g4_h10_eq_map_aux X Q hQ

example (X : Over (Spec ↧ℂ)) [GrpObj X] [IsIntegral X.left]
    [Smooth X.hom] [IsProjective X.hom] (Q : LinearMap.BilinForm ℤ (b2_abelianLattice X))
    (hQ : b2_IsRiemannForm (b2_abelianLattice X) (b2_abelianF X) Q)
    (u : ℂ ⊗[ℤ] b2_abelianLattice X) (hu : u ∈ b2_abelianF X) :
    letI := (torusCohomology_cupProductOf X).finite
    b63g4_cplxColumn X Q u ∈
      (abelianVarietyCohomologyOf (finiteBetti_abelian X) (spec_bettiDeRhamIso_abelian X)
        (hodgeDecomposition_of_abelian X) (torusCohomology_cupProductOf X)).weight1.H (1, 0) := by
  rw [b63g4_h10_eq_map X Q hQ]
  exact Submodule.mem_map_of_mem hu

/-! ## The two Riemann relations and positivity -/

/-- **First Riemann relation.** For a Riemann form `Q`, the pieces `H^{1,0}` and `H^{0,1}` are
isotropic for `E_ω ⊗ ℂ`: isotropy of `F` for `Q ⊗ ℂ` (`b2_IsRiemannForm.isotropic`) is carried by
the row map, and `H^{0,1}` is the conjugate of `H^{1,0}`.
Source: Birkenhake–Lange, §4.2 (first Riemann relation); Griffiths, *Periods of integrals on
algebraic manifolds I*, Amer. J. Math. 90 (1968), §2. -/
theorem b63g4_isotropic (X : Over (Spec ↧ℂ)) [GrpObj X] [IsIntegral X.left]
    [Smooth X.hom] [IsProjective X.hom] (Q : LinearMap.BilinForm ℤ (b2_abelianLattice X))
    (hQ : b2_IsRiemannForm (b2_abelianLattice X) (b2_abelianF X) Q) :
    letI := (torusCohomology_cupProductOf X).finite
    (∀ x ∈ (abelianVarietyCohomologyOf (finiteBetti_abelian X) (spec_bettiDeRhamIso_abelian X)
        (hodgeDecomposition_of_abelian X) (torusCohomology_cupProductOf X)).weight1.H (1, 0),
      ∀ y ∈ (abelianVarietyCohomologyOf (finiteBetti_abelian X) (spec_bettiDeRhamIso_abelian X)
        (hodgeDecomposition_of_abelian X) (torusCohomology_cupProductOf X)).weight1.H (1, 0),
      (polarizationForm (torusCohomology_cupProductOf X)
        (b2_abelian_nondegenerate X Q hQ)).baseChange ℂ x y = 0) ∧
    (∀ x ∈ (abelianVarietyCohomologyOf (finiteBetti_abelian X) (spec_bettiDeRhamIso_abelian X)
        (hodgeDecomposition_of_abelian X) (torusCohomology_cupProductOf X)).weight1.H (0, 1),
      ∀ y ∈ (abelianVarietyCohomologyOf (finiteBetti_abelian X) (spec_bettiDeRhamIso_abelian X)
        (hodgeDecomposition_of_abelian X) (torusCohomology_cupProductOf X)).weight1.H (0, 1),
      (polarizationForm (torusCohomology_cupProductOf X)
        (b2_abelian_nondegenerate X Q hQ)).baseChange ℂ x y = 0) :=
  b63g4_isotropic_aux X Q hQ

example (X : Over (Spec ↧ℂ)) [GrpObj X] [IsIntegral X.left]
    [Smooth X.hom] [IsProjective X.hom] (Q : LinearMap.BilinForm ℤ (b2_abelianLattice X))
    (hQ : b2_IsRiemannForm (b2_abelianLattice X) (b2_abelianF X) Q) :
    letI := (torusCohomology_cupProductOf X).finite
    ∀ x ∈ (abelianVarietyCohomologyOf (finiteBetti_abelian X) (spec_bettiDeRhamIso_abelian X)
        (hodgeDecomposition_of_abelian X) (torusCohomology_cupProductOf X)).weight1.H (1, 0),
      ∀ y ∈ (abelianVarietyCohomologyOf (finiteBetti_abelian X) (spec_bettiDeRhamIso_abelian X)
        (hodgeDecomposition_of_abelian X) (torusCohomology_cupProductOf X)).weight1.H (1, 0),
      (polarizationForm (torusCohomology_cupProductOf X)
        (b2_abelian_nondegenerate X Q hQ)).baseChange ℂ x y = 0 :=
  (b63g4_isotropic X Q hQ).1

/-- **Second Riemann relation, in the exact convention of `HodgeBlocks.Polarisation`.** For a
Riemann form `Q` and `0 ≠ x ∈ H^{1,0}`, `Re (i · E_ω(x, σ x)) > 0`. Writing `x` as the image of
`0 ≠ u ∈ F`, the row map turns this into `Re (i · Q_ℂ(u, ū)) > 0`, which is
`b2_IsRiemannForm.positive`, with the same factor `i` and the same order of arguments.
Source: Birkenhake–Lange, §4.2 (second Riemann relation); Cattani–El Zein–Griffiths–Lê,
*Hodge Theory*, Definition 3.1.8 (`i^{p-q}` with `(p, q) = (1, 0)`);
`b2_IsRiemannForm.positive`. -/
theorem b63g4_h10_positive (X : Over (Spec ↧ℂ)) [GrpObj X] [IsIntegral X.left]
    [Smooth X.hom] [IsProjective X.hom] (Q : LinearMap.BilinForm ℤ (b2_abelianLattice X))
    (hQ : b2_IsRiemannForm (b2_abelianLattice X) (b2_abelianF X) Q) :
    letI := (torusCohomology_cupProductOf X).finite
    ∀ x ∈ (abelianVarietyCohomologyOf (finiteBetti_abelian X) (spec_bettiDeRhamIso_abelian X)
        (hodgeDecomposition_of_abelian X) (torusCohomology_cupProductOf X)).weight1.H (1, 0),
      x ≠ 0 →
      0 < (Complex.I * (polarizationForm (torusCohomology_cupProductOf X)
        (b2_abelian_nondegenerate X Q hQ)).baseChange ℂ x
          (HodgeBlocks.sigmaQ (HQ X 1) x)).re :=
  b63g4_h10_positive_aux X Q hQ

example (X : Over (Spec ↧ℂ)) [GrpObj X] [IsIntegral X.left]
    [Smooth X.hom] [IsProjective X.hom] (Q : LinearMap.BilinForm ℤ (b2_abelianLattice X))
    (hQ : b2_IsRiemannForm (b2_abelianLattice X) (b2_abelianF X) Q) :
    letI := (torusCohomology_cupProductOf X).finite
    ∀ x ∈ (abelianVarietyCohomologyOf (finiteBetti_abelian X) (spec_bettiDeRhamIso_abelian X)
        (hodgeDecomposition_of_abelian X) (torusCohomology_cupProductOf X)).weight1.H (1, 0),
      x ≠ 0 →
      0 < (Complex.I * (polarizationForm (torusCohomology_cupProductOf X)
        (b2_abelian_nondegenerate X Q hQ)).baseChange ℂ x
          (HodgeBlocks.sigmaQ (HQ X 1) x)).re :=
  b63g4_h10_positive X Q hQ

/-- **Positivity of the class of a Riemann form.** For a Riemann form `Q` on the period lattice
of `X`, the class `latticeClassHQ X Q`, not negated, satisfies `PolarizationPositive`: its form
`E_ω` is a `HodgeBlocks.Polarisation` of the weight-one structure. The two Riemann relations
above and the vanishing of the pieces other than `(1, 0)` and `(0, 1)` are the conditions of
`pol1_polarisation_iff_h10_positive`.
Source: Birkenhake–Lange, §4.1–§4.2 (Riemann relations); Cattani–El Zein–Griffiths–Lê,
Definition 3.1.8; `pol1_polarisation_iff_h10_positive`, `b2bpol_dualForm_isPolarized`. -/
theorem b63g4_abelian_positive (X : Over (Spec ↧ℂ)) [GrpObj X] [IsIntegral X.left]
    [Smooth X.hom] [IsProjective X.hom] (Q : LinearMap.BilinForm ℤ (b2_abelianLattice X))
    (hQ : b2_IsRiemannForm (b2_abelianLattice X) (b2_abelianF X) Q) :
    PolarizationPositive (finiteBetti_abelian X) (spec_bettiDeRhamIso_abelian X)
      (hodgeDecomposition_of_abelian X) (torusCohomology_cupProductOf X)
      (b2_abelian_nondegenerate X Q hQ) :=
  b63g4_abelian_positive_aux X Q hQ

example (X : Over (Spec ↧ℂ)) [GrpObj X] [IsIntegral X.left]
    [Smooth X.hom] [IsProjective X.hom] (Q : LinearMap.BilinForm ℤ (b2_abelianLattice X))
    (hQ : b2_IsRiemannForm (b2_abelianLattice X) (b2_abelianF X) Q) :
    PolarizationPositive (finiteBetti_abelian X) (spec_bettiDeRhamIso_abelian X)
      (hodgeDecomposition_of_abelian X) (torusCohomology_cupProductOf X)
      (b2_abelian_nondegenerate X Q hQ) :=
  b63g4_abelian_positive X Q hQ

/-- **The opposite sign fails.** For `dim X > 0` and a Riemann form `Q`, the class
`-latticeClassHQ X Q` is not `PolarizationPositive`: its form is `-E_ω`, and
`Re (i · (-E_ω)(x, σ x)) < 0` on the nonzero piece `H^{1,0}` (of dimension `dim X`).
Source: Birkenhake–Lange, §4.2 (a Riemann form and its negative are not both positive);
`Symplectic.dualForm`. -/
theorem b63g4_neg_not_positive (X : Over (Spec ↧ℂ)) [GrpObj X] [IsIntegral X.left]
    [Smooth X.hom] [IsProjective X.hom] (hdim : 0 < dim X.left)
    (Q : LinearMap.BilinForm ℤ (b2_abelianLattice X))
    (hQ : b2_IsRiemannForm (b2_abelianLattice X) (b2_abelianF X) Q) :
    ¬ PolarizationPositive (finiteBetti_abelian X) (spec_bettiDeRhamIso_abelian X)
      (hodgeDecomposition_of_abelian X) (torusCohomology_cupProductOf X)
      (b63g4_neg_nondegenerate X (b2_abelian_nondegenerate X Q hQ)) :=
  b63g4_neg_not_positive_aux X hdim Q hQ

example (X : Over (Spec ↧ℂ)) [GrpObj X] [IsIntegral X.left]
    [Smooth X.hom] [IsProjective X.hom] (hdim : 0 < dim X.left)
    (Q : LinearMap.BilinForm ℤ (b2_abelianLattice X))
    (hQ : b2_IsRiemannForm (b2_abelianLattice X) (b2_abelianF X) Q) :
    ¬ PolarizationPositive (finiteBetti_abelian X) (spec_bettiDeRhamIso_abelian X)
      (hodgeDecomposition_of_abelian X) (torusCohomology_cupProductOf X)
      (b63g4_neg_nondegenerate X (b2_abelian_nondegenerate X Q hQ)) :=
  b63g4_neg_not_positive X hdim Q hQ

/-! ## The sign on the standard elliptic data

On `(ℤ², b2_stdF, b2_stdForm)`, with `F = ℂ (e₀ + i e₁)` and `Q (e₀, e₁) = 1`, the vector
`v = e₀ + i e₁` has `Q_ℂ(v, v̄) = -2i`, so `Re (i · Q_ℂ(v, v̄)) = 2 > 0`, and `-b2_stdForm` gives
`-2`. The homology check below has a body that uses no statement of this file. The model check
then reads the sign on `H²` of the elliptic model `b5_elliptic`: the class of part 1 is positive,
its negative is not, so the class is nonzero; the model has dimension one, so neither the zero
lattice nor the zero class is the instance. -/

/-- **Homology check of the sign.** `-b2_stdForm` is not a Riemann form for `b2_stdF`: its
positivity fails at `v = e₀ + i e₁` (`b2a_stdVec`), where the value is `-2`
(`b63g4_std_value`). -/
example : ¬ b2_IsRiemannForm (Fin 2 → ℤ) b2_stdF (-b2_stdForm) := by
  intro h
  have hv0 : b2a_stdVec ≠ 0 := by
    intro h0
    have := congrArg (LinearMap.liftBaseChange ℂ
      ((Algebra.linearMap ℤ ℂ) ∘ₗ LinearMap.proj (R := ℤ) (φ := fun _ : Fin 2 ↦ ℤ) 0)) h0
    simp [b2a_stdVec] at this
  have hp := h.positive _ (Submodule.mem_span_singleton_self _) hv0
  have hneg : (-b2_stdForm).baseChange ℂ = -(b2_stdForm.baseChange ℂ) := by
    ext x y
    simp [LinearMap.BilinForm.baseChange_tmul]
  rw [hneg, LinearMap.neg_apply, LinearMap.neg_apply, mul_neg, Complex.neg_re,
    b63g4_std_value] at hp
  norm_num at hp

/-- The standard data give a Riemann form with the original sign (a theorem with a body). -/
example : b2_IsRiemannForm (Fin 2 → ℤ) b2_stdF b2_stdForm := b2_std_isRiemannForm

/-- **Model check of the sign.** On the elliptic model `b5_elliptic` of the standard data, the
class `b63g_modelClass` of part 1 is `PolarizationPositive`, its negative is not, the class is
nonzero, and the model has dimension one. -/
example :
    letI := b5_groupObj _ _ b2_std_isWeightOne _ b2_std_isRiemannForm
    letI : IsIntegral b5_elliptic.left := b5_integral_aux _ _ b2_std_isWeightOne _
      b2_std_isRiemannForm
    letI := b5_smooth_aux _ _ b2_std_isWeightOne _ b2_std_isRiemannForm
    letI := b5_projective_aux _ _ b2_std_isWeightOne _ b2_std_isRiemannForm
    PolarizationPositive (η := b63g_modelClass _ _ b2_std_isWeightOne _ b2_std_isRiemannForm)
        (finiteBetti_abelian b5_elliptic) (spec_bettiDeRhamIso_abelian b5_elliptic)
        (hodgeDecomposition_of_abelian b5_elliptic) (torusCohomology_cupProductOf b5_elliptic)
        (b2_abelian_nondegenerate _ _
          (b63g_modelForm_riemann _ _ b2_std_isWeightOne _ b2_std_isRiemannForm)) ∧
      ¬ PolarizationPositive
        (η := -b63g_modelClass _ _ b2_std_isWeightOne _ b2_std_isRiemannForm)
        (finiteBetti_abelian b5_elliptic) (spec_bettiDeRhamIso_abelian b5_elliptic)
        (hodgeDecomposition_of_abelian b5_elliptic) (torusCohomology_cupProductOf b5_elliptic)
        (b63g4_neg_nondegenerate _ (b2_abelian_nondegenerate _ _
          (b63g_modelForm_riemann _ _ b2_std_isWeightOne _ b2_std_isRiemannForm))) ∧
      b63g_modelClass _ _ b2_std_isWeightOne _ b2_std_isRiemannForm ≠ 0 ∧
      dim b5_elliptic.left = 1 := by
  let := b5_groupObj _ _ b2_std_isWeightOne _ b2_std_isRiemannForm
  let : IsIntegral b5_elliptic.left := b5_integral_aux _ _ b2_std_isWeightOne _
    b2_std_isRiemannForm
  let := b5_smooth_aux _ _ b2_std_isWeightOne _ b2_std_isRiemannForm
  let := b5_projective_aux _ _ b2_std_isWeightOne _ b2_std_isRiemannForm
  have hdim : dim b5_elliptic.left = 1 := by
    have h := b63g_model_finrank _ _ b2_std_isWeightOne _ b2_std_isRiemannForm
    rw [Module.finrank_fin_fun] at h
    change 2 = 2 * dim b5_elliptic.left at h
    omega
  have hR := b63g_modelForm_riemann _ _ b2_std_isWeightOne _ b2_std_isRiemannForm
  have hpos := b63g4_abelian_positive _ _ hR
  have hneg := b63g4_neg_not_positive _ (by change 0 < dim b5_elliptic.left; omega) _ hR
  refine ⟨hpos, hneg, fun h0 ↦ hneg ?_, hdim⟩
  refine b63g4_positive_congr _ ?_ _ _ hpos
  change b63g_modelClass _ _ b2_std_isWeightOne _ b2_std_isRiemannForm =
    -b63g_modelClass _ _ b2_std_isWeightOne _ b2_std_isRiemannForm
  rw [h0, neg_zero]

/-! ## Chain checks toward the field `positive` -/

/-- **The field `positive` on a bundled sixfold.** For B5 lattice data with an operator as in
part 1, the `g32t_Sixfold` of part 1 (the B5 model, the Weil action of the model operator and
`b63g_modelClass`) satisfies `PolarizationPositive` for every nondegeneracy witness: the type of
the field `positive` of `g32h_PrymFamily` at a fibre, and of the field `positive` of
`IsMemberOfM`. -/
example (Λ : Type) [AddCommGroup Λ] [Module.Finite ℤ Λ]
    [Module.Free ℤ Λ] (F : Submodule ℂ (ℂ ⊗[ℤ] Λ)) (hF : b2_IsWeightOne Λ F)
    (Q : LinearMap.BilinForm ℤ Λ) (hQ : b2_IsRiemannForm Λ F Q) (φ : Λ →+ Λ)
    (hsq : ∀ l, φ (φ l) = (-3 : ℤ) • l) (hφ : F ≤ F.comap (b2_cplxMap φ)) :
    letI := b5_groupObj Λ F hF Q hQ
    letI : IsIntegral (b5_model Λ F hF Q).left := b5_integral_aux Λ F hF Q hQ
    letI := b5_smooth_aux Λ F hF Q hQ
    letI := b5_projective_aux Λ F hF Q hQ
    letI : IsCommMonObj (b5_model Λ F hF Q) := b5_commutative_aux Λ F hF Q hQ
    letI := (torusCohomology_cupProductOf (b5_model Λ F hF Q)).finite
    let P : g32t_Sixfold :=
      { X := b5_model Λ F hF Q
        W := ⟨b63g_modelOperator Λ F hF Q hQ φ,
          (b63g_dualOperator_sq _ 3 _ (b63g_modelMap_sq Λ F hF Q hQ 3 φ hsq)).trans
            (by norm_num),
          b63g_dualOperator_hodge _ _ (b63g_modelMap_filtration Λ F hF Q hQ φ hφ)⟩
        pol := b63g_modelClass Λ F hF Q hQ }
    ∀ hnd : IsNondegenerate (polarizationVec (torusCohomology_cupProductOf P.X) P.pol),
      PolarizationPositive (finiteBetti_abelian P.X) (spec_bettiDeRhamIso_abelian P.X)
        (hodgeDecomposition_of_abelian P.X) (torusCohomology_cupProductOf P.X) hnd := by
  intro P hnd
  let := b5_groupObj Λ F hF Q hQ
  let : IsIntegral (b5_model Λ F hF Q).left := b5_integral_aux Λ F hF Q hQ
  let := b5_smooth_aux Λ F hF Q hQ
  let := b5_projective_aux Λ F hF Q hQ
  exact b63g4_abelian_positive _ _ (b63g_modelForm_riemann Λ F hF Q hQ)

/-- **The two Riemann relations give the field.** `b63g4_isotropic` and `b63g4_h10_positive`,
with the vanishing of the other pieces, are the hypotheses of
`pol1_polarisation_iff_h10_positive`; their conclusion is `PolarizationPositive`, the statement
`b63g4_abelian_positive`. -/
example (X : Over (Spec ↧ℂ)) [GrpObj X] [IsIntegral X.left]
    [Smooth X.hom] [IsProjective X.hom] (Q : LinearMap.BilinForm ℤ (b2_abelianLattice X))
    (hQ : b2_IsRiemannForm (b2_abelianLattice X) (b2_abelianF X) Q) :
    PolarizationPositive (finiteBetti_abelian X) (spec_bettiDeRhamIso_abelian X)
      (hodgeDecomposition_of_abelian X) (torusCohomology_cupProductOf X)
      (b2_abelian_nondegenerate X Q hQ) := by
  let := (torusCohomology_cupProductOf X).finite
  exact (pol1_polarisation_iff_h10_positive _ _ (isAlt_polarizationForm _ _)
    (nondegenerate_polarizationForm _ _)
    (fun pq h10 h01 ↦ cohomologyHodgePiece_one_eq_bot X pq h10 h01)
    (b63g4_isotropic X Q hQ).1 (b63g4_isotropic X Q hQ).2).2 (b63g4_h10_positive X Q hQ)

/-- **The actual moving fibres.** For the saturated lattice at `s` with a basis of rank twelve
(as `b63d_lattice_rank` supplies), the filtration transported from `t` and the original form,
the certificates of `b63e_weight_one_riemann` give the B5 model of part 1; its class
`b63g_modelClass` is `PolarizationPositive`, the field `positive` at this fibre. -/
example (b : Fin 10 → ℂ) (C : Type) [TopologicalSpace C]
    [MulAction b4b_Group C]
    (hC : ∀ g : b4b_Group, Continuous (fun x : C ↦ g • x))
    (V : Set (Fin 10 → ℂ)) (hV : V ⊆ b6t_polydisc b)
    [∀ t : V, ChartedSpace ℂ (b63l_parameterFibre b C V hV t)]
    [∀ t : V, IsManifold 𝓘(ℂ, ℂ) ω (b63l_parameterFibre b C V hV t)]
    [∀ t : V, T2Space (b63l_parameterFibre b C V hV t)]
    [∀ t : V, CompactSpace (b63l_parameterFibre b C V hV t)]
    [∀ t : V, ConnectedSpace (b63l_parameterFibre b C V hV t)]
    (hG : ∀ (t : V) (g : b4b_Group), ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω
      (fun x : b63l_parameterFibre b C V hV t ↦ g • x))
    (hb : b ∈ b6_chart) [ChartedSpace ℂ C] [IsManifold 𝓘(ℂ, ℂ) ω C]
    [T2Space C] [CompactSpace C] [ConnectedSpace C]
    (f : C → OnePoint ℂ) (hf : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω f) (hs : Function.Surjective f)
    (hk : ∀ t : V, ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω (b63d_projection b C f V hV t))
    (Q₀ : LinearMap.BilinForm ℤ (b3_periodLattice ℂ C)) (hQ₀ : b3_IsIntersectionForm ℂ Q₀)
    (Q : (t : V) → LinearMap.BilinForm ℤ (b3_periodLattice ℂ (b63l_parameterFibre b C V hV t)))
    (hQ : ∀ t : V, b3_IsIntersectionForm ℂ (Q t))
    (P : (t : V) → b6m_H1 (b63l_parameterFibre b C V hV t) →ₗ[ℤ]
      b3_periodLattice ℂ (b63l_parameterFibre b C V hV t))
    (hP : ∀ (t : V) (γ : b3_SmoothLoop ℂ (b63l_parameterFibre b C V hV t)),
      P t (b6m_loopClass _ γ) = b3_latticePeriod ℂ _ γ)
    (s t : V) (B : Module.Basis (Fin 12) ℤ (b63l_parameterLattice b C hC V hV s)) :
    letI : Module.Free ℤ (b63l_parameterLattice b C hC V hV s) := Module.Free.of_basis B
    letI : Module.Finite ℤ (b63l_parameterLattice b C hC V hV s) := Module.Finite.of_basis B
    letI := b5_groupObj _ _ (b63e_weight_one_riemann b C hC V hV hG hb f hf hs hk Q₀ hQ₀ Q hQ
      P hP s t).1 _ (b63e_weight_one_riemann b C hC V hV hG hb f hf hs hk Q₀ hQ₀ Q hQ P hP s t).2
    letI : IsIntegral (b5_model _ _ (b63e_weight_one_riemann b C hC V hV hG hb f hf hs hk Q₀
        hQ₀ Q hQ P hP s t).1 (b63e_singularQ b C hC V hV s (P s) (Q s))).left :=
      b5_integral_aux _ _ _ _ (b63e_weight_one_riemann b C hC V hV hG hb f hf hs hk Q₀ hQ₀ Q
        hQ P hP s t).2
    letI := b5_smooth_aux _ _ _ _ (b63e_weight_one_riemann b C hC V hV hG hb f hf hs hk Q₀ hQ₀
      Q hQ P hP s t).2
    letI := b5_projective_aux _ _ _ _ (b63e_weight_one_riemann b C hC V hV hG hb f hf hs hk Q₀
      hQ₀ Q hQ P hP s t).2
    PolarizationPositive
      (η := b63g_modelClass _ _ _ _ (b63e_weight_one_riemann b C hC V hV hG hb f hf hs hk Q₀ hQ₀
        Q hQ P hP s t).2)
      (finiteBetti_abelian _) (spec_bettiDeRhamIso_abelian _) (hodgeDecomposition_of_abelian _)
      (torusCohomology_cupProductOf _)
      (b2_abelian_nondegenerate _ _ (b63g_modelForm_riemann _ _ _ _
        (b63e_weight_one_riemann b C hC V hV hG hb f hf hs hk Q₀ hQ₀ Q hQ P hP s t).2)) :=
  letI : Module.Free ℤ (b63l_parameterLattice b C hC V hV s) := Module.Free.of_basis B
  letI : Module.Finite ℤ (b63l_parameterLattice b C hC V hV s) := Module.Finite.of_basis B
  have W := b63e_weight_one_riemann b C hC V hV hG hb f hf hs hk Q₀ hQ₀ Q hQ P hP s t
  letI := b5_groupObj _ _ W.1 _ W.2
  letI : IsIntegral (b5_model _ _ W.1 (b63e_singularQ b C hC V hV s (P s) (Q s))).left :=
    b5_integral_aux _ _ _ _ W.2
  letI := b5_smooth_aux _ _ _ _ W.2
  letI := b5_projective_aux _ _ _ _ W.2
  b63g4_abelian_positive _ _ (b63g_modelForm_riemann _ _ W.1 _ W.2)

end HodgeLean.Foundations.Program
