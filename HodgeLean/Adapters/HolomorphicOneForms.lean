import HodgeLean.Adapters.HolomorphicOneFormsProofs

/-! # Global holomorphic `1`-forms and `F^1 H_dR^1`: frozen specification

Inputs stage 4c, toward `F^1_B ≤ complexHolomorphicH1 X`. Stage 4b (`HodgeFilterLattice`) reduces
the degree-one Hodge decomposition of an abelian `X` to that inclusion, where
`F^1_B = (F^1 H_dR^1).comap (bettiDeRhamHQ X 1)`. This stage takes the first step of its route:
it identifies `F^1 H_dR^1(X)` with the de Rham classes of closed global holomorphic `1`-forms.

Global holomorphic `p`-forms are global sections of upstream's sheafified `holomorphicDeRhamSheaf`
(`GlobalHolomorphicForm`). A degree-one cycle of `Γ(X(ℂ), F^1 Ω•)` is a closed global holomorphic
`1`-form, and `cycleDeRhamClass` sends it to `H_dR^1(X)` through the edge map
`globalSectionsToHypercohomology` and upstream's `filteredToDeRhamCohomology`.

Claimed:
* for integral `X` proper over `ℂ`: the structure map `ℂ → Γ(X, 𝒪_X)` is bijective;
* for every smooth integral `X`: a degree-one cycle of `Γ(X(ℂ), F^1 Ω•)` is determined by its
  global holomorphic `1`-form, and these forms are exactly the closed ones; each degree-one cycle
  is its own homology class (there are no boundaries);
* for every complex `S` of sheaves on `X(ℂ)` that is strictly `≥ 1`: the edge map
  `H^1(Γ(X(ℂ), S)) → ℍ^1(X(ℂ); S)` is bijective;
* for every smooth integral `X`: `F^1 H_dR^1(X)` is the set of de Rham classes of closed global
  holomorphic `1`-forms;
* for every smooth integral `X`: the implication from "every global holomorphic function on
  `X(ℂ)` is locally constant" to the injectivity of the class map on closed `1`-forms;
* for abelian `X`: `F^1_B ≤ complexHolomorphicH1 X` is equivalent to the period condition that the
  Betti class of every closed global holomorphic `1`-form lies in the holomorphic summand;
* falsification, for abelian `X` with `g ≥ 1`: under that inclusion the classes of closed
  holomorphic `1`-forms are not all of `H_dR^1(X)` (dimension `g`, not `2g`), and under the
  identification `F^1_B = complexHolomorphicH1 X` some such class is not antiholomorphic.

Not claimed: the inclusion `F^1_B ≤ complexHolomorphicH1 X` or the period condition itself, the
constancy of global holomorphic functions on `X(ℂ)`, the invariant forms `dzᵢ`, the dimension of
the space of global holomorphic `1`-forms, or any integration of forms along loops. These need the
pullback of forms along `exp : ℂ^g → X(ℂ)` and a de Rham theorem with singular periods, which exist
nowhere (`docs/specs/HolomorphicOneForms.md`). Upstream's presheaf value `HolomorphicForm X d ⊤ p`
is not the space of global forms; only the sheafified sections are used.
HC no distance; AV milestone no distance.
-/

noncomputable section
open CategoryTheory AlgebraicGeometry ComplexPoint TopologicalSpace
open HodgeLean.RealDefs HodgeLean.Foundations
open scoped TensorProduct

namespace HodgeLean.Adapters

/-- For an integral scheme `X` proper over `ℂ`, the structure map `ℂ → Γ(X, 𝒪_X)` is bijective:
global regular functions are constant.

Source: Mathlib's `AlgebraicGeometry.finite_appTop_of_universallyClosed`
(`Mathlib/AlgebraicGeometry/Morphisms/Proper.lean`: `Γ(X, 𝒪_X)` is a finite field extension of the
base field), with `ℂ` algebraically closed. -/
theorem spec_structureSheaf_globalSections_bijective (X : Over (Spec ↧ℂ))
    [IsIntegral X.left] [IsProper X.hom] :
    Function.Bijective ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv ≫ X.hom.appTop).hom :=
  spec_structureSheaf_globalSections_bijective_aux X

example (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [IsProper X.hom] (f : Γ(X.left, ⊤)) :
    ∃ c : ℂ, ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv ≫ X.hom.appTop).hom c = f :=
  (spec_structureSheaf_globalSections_bijective X).2 f

/-- A degree-one cycle of `Γ(X(ℂ), F^1 Ω•)` is determined by its global holomorphic `1`-form.

Source: Mathlib's `HomologicalComplex.iCycles` is a monomorphism, and `filteredDeRhamXOneIso` is an
isomorphism (Voisin, *Hodge Theory and Complex Algebraic Geometry I*, §8.1.3). -/
theorem spec_cycleOneForm_injective (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] :
    Function.Injective (cycleOneForm X) :=
  spec_cycleOneForm_injective_aux X

example (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom]
    (z : (filteredGlobalSections X).cycles ((1 : ℕ) : ℤ)) (hz : cycleOneForm X z = 0) : z = 0 :=
  spec_cycleOneForm_injective X (hz.trans (map_zero _).symm)

/-- The global holomorphic `1`-forms of degree-one cycles of `Γ(X(ℂ), F^1 Ω•)` are exactly the
closed ones: under `filteredDeRhamXOneIso` the differential of `F^1 Ω•` in degree one is
`d : Ω^1 → Ω^2`.

Source: Voisin, *Hodge Theory and Complex Algebraic Geometry I*, §8.1.3; Mathlib's
`HomologicalComplex.stupidTrunc` and `HomologicalComplex.extend_d_eq`, with upstream's
`holomorphicDeRhamComplex_d`. -/
theorem spec_range_cycleOneForm (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] :
    (cycleOneForm X).range = closedGlobalHolomorphicOneForms X :=
  spec_range_cycleOneForm_aux X

example (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom]
    (θ : GlobalHolomorphicForm X 1) (hθ : globalHolomorphicDifferential X 1 θ = 0) :
    ∃ z, cycleOneForm X z = θ := by
  have h : θ ∈ (cycleOneForm X).range := by
    rw [spec_range_cycleOneForm X]
    exact hθ
  exact h

/-- Every degree-one cycle of `Γ(X(ℂ), F^1 Ω•)` is its own homology class: the complex vanishes in
degree `0`, so there are no boundaries in degree one.

Source: Mathlib's `HomologicalComplex.homologyπ`, with `HomologicalComplex.isZero_stupidTrunc_X`
(`F^1 Ω•` is zero in degree `0`). -/
theorem spec_filteredGlobalSections_homologyπ_one_bijective (X : Over (Spec ↧ℂ))
    [IsIntegral X.left] [Smooth X.hom] :
    Function.Bijective ((filteredGlobalSections X).homologyπ ((1 : ℕ) : ℤ)).hom :=
  spec_filteredGlobalSections_homologyπ_one_bijective_aux X

example (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom]
    (z : (filteredGlobalSections X).cycles ((1 : ℕ) : ℤ))
    (hz : ((filteredGlobalSections X).homologyπ ((1 : ℕ) : ℤ)).hom z = 0) : z = 0 :=
  (spec_filteredGlobalSections_homologyπ_one_bijective X).1 (hz.trans (map_zero _).symm)

/-- For a complex `S` of sheaves of abelian groups on `X(ℂ)` that is strictly `≥ 1`, the edge map
`H^1(Γ(X(ℂ), S)) → ℍ^1(X(ℂ); S)` is bijective: both sides are the global sections of
`ker(S^1 → S^2)`.

Source: Gelfand–Manin, *Methods of Homological Algebra*, 2nd ed., IV.4 (the standard
t-structure: `Hom_D(A, L) = Hom(H^0 A, H^0 L)` for `A ∈ D^{≤0}`, `L ∈ D^{≥0}`), with
`Hom(ℤ_X, F) = Γ(X, F)`; Bredon, *Sheaf Theory*, 2nd ed., GTM 170, II.4. -/
theorem spec_globalSectionsToHypercohomology_one_bijective (X : Over (Spec ↧ℂ))
    (S : CochainComplex (AnalyticAdditiveSheaf X) ℤ) [S.IsStrictlyGE 1] :
    Function.Bijective (globalSectionsToHypercohomology X S ((1 : ℕ) : ℤ)) :=
  spec_globalSectionsToHypercohomology_one_bijective_aux X S

example (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] :
    Function.Bijective (globalSectionsToHypercohomology X (F^1 Ω•(X)) ((1 : ℕ) : ℤ)) :=
  spec_globalSectionsToHypercohomology_one_bijective X (F^1 Ω•(X))

/-- `F^1 H_dR^1(X)` consists exactly of the de Rham classes of closed global holomorphic
`1`-forms: `ℍ^1(X(ℂ); F^1 Ω•)` is the group of closed global holomorphic `1`-forms.

Source: Voisin, *Hodge Theory and Complex Algebraic Geometry I*, §8.1.3 (the edge map
`H^0(X, Ω^1) → F^1 H^1(X, ℂ)`), through `spec_globalSectionsToHypercohomology_one_bijective` and
`spec_filteredGlobalSections_homologyπ_one_bijective`. -/
theorem spec_hodgeFiltration_one_eq_range_cycleDeRhamClass (X : Over (Spec ↧ℂ))
    [IsIntegral X.left] [Smooth X.hom] :
    (F^1 H_dR^((1 : ℕ) : ℤ)(X)).toAddSubgroup = (cycleDeRhamClass X).range :=
  spec_hodgeFiltration_one_eq_range_cycleDeRhamClass_aux X

example (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom]
    (α : H_dR^((1 : ℕ) : ℤ)(X)) (hα : α ∈ F^1 H_dR^((1 : ℕ) : ℤ)(X)) :
    ∃ z, cycleDeRhamClass X z = α := by
  have h : α ∈ (cycleDeRhamClass X).range := by
    rw [← spec_hodgeFiltration_one_eq_range_cycleDeRhamClass X]
    exact hα
  exact h

/-- The implication from "every global holomorphic function on `X(ℂ)` is locally constant" to the
injectivity of the de Rham class map on closed global holomorphic `1`-forms. The kernel of
`ℍ^1(F^1 Ω•) → ℍ^1(Ω•)` is the image of `d` on global holomorphic functions.

Source: Voisin, *Hodge Theory and Complex Algebraic Geometry I*, §8.1.3 (the long exact sequence
of `0 → F^1 Ω• → Ω• → 𝒪 → 0`); Griffiths–Harris, *Principles of Algebraic Geometry*, Ch. 0 §1
(global holomorphic functions on a compact connected complex manifold are constant, which makes the
premise true for proper `X`). -/
theorem spec_cycleDeRhamClass_injective_of_constant (X : Over (Spec ↧ℂ))
    [IsIntegral X.left] [Smooth X.hom]
    (hconst : ∀ f : GlobalHolomorphicForm X 0, f ∈ Set.range
      ((TopCat.Sheaf.IsFlasque.BoundedBelowComplex.globalSectionsFunctor
        (TopCat.of (ComplexPoint X))).map
          (constantsToHolomorphicDeRhamZeroSheaf X (dim X.left))).hom) :
    Function.Injective (cycleDeRhamClass X) :=
  spec_cycleDeRhamClass_injective_of_constant_aux X hconst

example (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom]
    (hconst : ∀ f : GlobalHolomorphicForm X 0, f ∈ Set.range
      ((TopCat.Sheaf.IsFlasque.BoundedBelowComplex.globalSectionsFunctor
        (TopCat.of (ComplexPoint X))).map
          (constantsToHolomorphicDeRhamZeroSheaf X (dim X.left))).hom)
    (z : (filteredGlobalSections X).cycles ((1 : ℕ) : ℤ)) (hz : cycleDeRhamClass X z = 0) :
    cycleOneForm X z = 0 := by
  rw [spec_cycleDeRhamClass_injective_of_constant X hconst (hz.trans (map_zero _).symm),
    map_zero]

/-- For abelian `X`: `F^1_B ≤ complexHolomorphicH1 X` is equivalent to the period condition for
closed global holomorphic `1`-forms: the Betti class of each lies in the holomorphic summand, i.e.
its periods along the lattice are those of a complex-linear functional on `ℂ^g`.

Source: Birkenhake–Lange, *Complex Abelian Varieties*, 2nd ed., Grundlehren 302, §1.4 and
Theorem 1.4.1, through `spec_hodgeFiltration_one_eq_range_cycleDeRhamClass`. -/
theorem spec_comap_hodgeFiltration_one_le_iff (X : Over (Spec ↧ℂ)) [GrpObj X]
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] :
    (F^1 H_dR^((1 : ℕ) : ℤ)(X)).comap (bettiDeRhamHQ X 1) ≤ complexHolomorphicH1 X ↔
      ∀ (z : (filteredGlobalSections X).cycles ((1 : ℕ) : ℤ)) (ω : ℂ ⊗[ℚ] HQ X 1),
        bettiDeRhamHQ X 1 ω = cycleDeRhamClass X z → ω ∈ complexHolomorphicH1 X :=
  spec_comap_hodgeFiltration_one_le_iff_aux X

example (X : Over (Spec ↧ℂ)) [GrpObj X] [IsIntegral X.left] [Smooth X.hom]
    [IsProjective X.hom]
    (hper : ∀ (z : (filteredGlobalSections X).cycles ((1 : ℕ) : ℤ)) (ω : ℂ ⊗[ℚ] HQ X 1),
      bettiDeRhamHQ X 1 ω = cycleDeRhamClass X z → ω ∈ complexHolomorphicH1 X) :
    Disjoint (F^1 H_dR^((1 : ℕ) : ℤ)(X))
      (conjHodgeFiltrationComplexSubmodule X 1 ((1 : ℕ) : ℤ)) :=
  spec_disjoint_hodgeFiltration_one_of_le X ((spec_comap_hodgeFiltration_one_le_iff X).2 hper)

/-- Falsification check, for abelian `X` with `g ≥ 1`: under `F^1_B ≤ complexHolomorphicH1 X`, the
de Rham classes of closed global holomorphic `1`-forms are not all of `H_dR^1(X)`; they span a
space of dimension at most `g`, while `H_dR^1(X)` has dimension `2g`.

Source: Birkenhake–Lange, *Complex Abelian Varieties*, 2nd ed., Grundlehren 302, Lemma 1.3.1 and
Theorem 1.4.1, through `spec_hodgeFiltration_one_eq_range_cycleDeRhamClass`,
`spec_finrank_hodgeFiltration_one_le_of_le`, `spec_complexH1_dimension` and
`spec_bettiDeRhamIso_abelian`. -/
theorem spec_cycleDeRhamClass_not_surjective_of_le (X : Over (Spec ↧ℂ)) [GrpObj X]
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] (hg : 1 ≤ dim X.left)
    (hle : (F^1 H_dR^((1 : ℕ) : ℤ)(X)).comap (bettiDeRhamHQ X 1) ≤ complexHolomorphicH1 X) :
    ¬ Function.Surjective (cycleDeRhamClass X) :=
  spec_cycleDeRhamClass_not_surjective_of_le_aux X hg hle

example (X : Over (Spec ↧ℂ)) [GrpObj X] [IsIntegral X.left] [Smooth X.hom]
    [IsProjective X.hom] (hg : 1 ≤ dim X.left)
    (hle : (F^1 H_dR^((1 : ℕ) : ℤ)(X)).comap (bettiDeRhamHQ X 1) ≤ complexHolomorphicH1 X) :
    ∃ α : H_dR^((1 : ℕ) : ℤ)(X), ∀ z, cycleDeRhamClass X z ≠ α := by
  obtain ⟨α, hα⟩ := not_forall.mp (spec_cycleDeRhamClass_not_surjective_of_le X hg hle)
  exact ⟨α, fun z hz => hα ⟨z, hz⟩⟩

/-- Falsification check, for abelian `X` with `g ≥ 1`: under `F^1_B = complexHolomorphicH1 X`,
some closed global holomorphic `1`-form has a Betti class outside the antiholomorphic summand
(a form `dz̄` would have conjugate-linear periods, which a holomorphic form does not).

Source: Birkenhake–Lange, *Complex Abelian Varieties*, 2nd ed., Grundlehren 302, Theorem 1.4.1,
through `spec_hodgeFiltration_one_eq_range_cycleDeRhamClass`, `spec_complexH1_split` and
`spec_complexH1_dimension`. -/
theorem spec_exists_cycle_not_antiholomorphic_of_eq (X : Over (Spec ↧ℂ)) [GrpObj X]
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] (hg : 1 ≤ dim X.left)
    (heq : (F^1 H_dR^((1 : ℕ) : ℤ)(X)).comap (bettiDeRhamHQ X 1) = complexHolomorphicH1 X) :
    ∃ (z : (filteredGlobalSections X).cycles ((1 : ℕ) : ℤ)) (ω : ℂ ⊗[ℚ] HQ X 1),
      bettiDeRhamHQ X 1 ω = cycleDeRhamClass X z ∧ ω ∉ complexAntiholomorphicH1 X :=
  spec_exists_cycle_not_antiholomorphic_of_eq_aux X hg heq

example (X : Over (Spec ↧ℂ)) [GrpObj X] [IsIntegral X.left] [Smooth X.hom]
    [IsProjective X.hom] (hg : 1 ≤ dim X.left)
    (heq : (F^1 H_dR^((1 : ℕ) : ℤ)(X)).comap (bettiDeRhamHQ X 1) = complexHolomorphicH1 X) :
    ¬ ∀ (z : (filteredGlobalSections X).cycles ((1 : ℕ) : ℤ)) (ω : ℂ ⊗[ℚ] HQ X 1),
      bettiDeRhamHQ X 1 ω = cycleDeRhamClass X z → ω ∈ complexAntiholomorphicH1 X := by
  intro h
  obtain ⟨z, ω, hω, hA⟩ := spec_exists_cycle_not_antiholomorphic_of_eq X hg heq
  exact hA (h z ω hω)

end HodgeLean.Adapters
