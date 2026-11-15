import HodgeLean.Adapters.CupFilteredDeRhamProofs

/-! # Toward `CupFiltered` for abelian `X`: frozen specification

Stage `CupFilteredDeRham`, the first stage of the `CupFiltered` track
(`docs/specs/CupFilteredDeRham.md`). Stage 4m reduced `HodgeDecomposition X` for abelian `X` to
two open inputs: the ledger hypothesis `CupFiltered X (cupProductOf X)` (O5) and the opposedness
`F^p ∩ conj F^{n+1-p} = 0` in degrees `2 ≤ n ≤ 2g`. This stage reduces the first input to a
special case of it, and freezes the first de Rham statements toward it.

Amendment after the statement review. The parallel stage `HodgeOpposedAbelian` (opp1) derives the
opposedness from `CupFiltered` by Poincaré duality. Its argument runs with `hL` in place of
`CupFiltered`: reorder the type-`(1, 0)` factors of a cup-wedge generator next to `x`, using
`CupProduct.graded_comm`, and apply `hL` repeatedly. The product lands in `F^{g+1}`, which is zero in
every degree. So for abelian `X` with the torus theorem, the opposedness follows from `hL`, and
`hL` alone implies `CupFiltered X μ` and `HodgeDecomposition X`. Statements 13 and 14 below keep the
opposedness as a hypothesis. The reduction to `hL` alone is a later stage, after this stage and
opp1 are proved.

The smaller input, written `hL` below, is the special case of `CupFiltered` with a degree-one left
factor of filtration level one: if `β_1 x ∈ F^1 H^1` and `β_k y ∈ F^q H^k`, then
`β_{1+k} (x ∪ y) ∈ F^{q+1} H^{1+k}`. It says that cup product with a class of a holomorphic
`1`-form raises the Hodge filtration by one.

Claimed:
* the instantiated product `cupProductOf X` is a nonzero rational multiple of the product
  transported along the unnormalized comparison U1, so the normalization scalar of
  `normalizedEquiv` does not affect any filtration statement;
* for every complex `S` of sheaves strictly `≥ n`, the edge map from `H^n(Γ(X(ℂ), S))` to
  `ℍ^n(X(ℂ); S)` is bijective;
* for smooth integral `X` and every `p`: a degree-`p` cycle of `Γ(X(ℂ), F^p Ω•)` is determined by
  its global holomorphic `p`-form, those forms are exactly the closed ones, and `F^p H_dR^p(X)` is
  the set of classes of closed global holomorphic `p`-forms;
* for smooth `X`: the wedge of `p` global holomorphic `1`-forms exists as a global holomorphic
  `p`-form (its value at each point is the wedge of the covectors), it is closed when the factors
  are closed, and for smooth integral `X` it is the form of a degree-`p` cycle of
  `Γ(X(ℂ), F^p Ω•)`, so its class lies in `F^p H_dR^p(X)`;
* for abelian `X` and a cup product `μ` with the torus theorem: `cupMultiC` is alternating; the
  implication from `hL` to the multiplicativity of `F^•` on cups of degree-one classes, and to
  `cupWedgePiece ≤ deRhamHodgePiece`; the implication from `hL` and the opposedness in degree `n`
  to `F^p H_dR^n(X) = ⨆_{p' ≥ p} cupWedgePiece X μ n (p', n - p')`; and the implication from `hL`
  and the opposedness in degrees `2 ≤ n ≤ 2g` to `CupFiltered X μ` and to `HodgeDecomposition X`.

Not claimed: `hL` for any `μ`, `CupFiltered X μ` for any `μ`, the opposedness in any degree
`n ≥ 2`, `HodgeDecomposition X`, any comparison between the class of a wedge of forms and a cup
product of classes, or anything for non-abelian `X` beyond the de Rham statements.
HC no distance; AV milestone no distance.
-/

noncomputable section
open CategoryTheory AlgebraicGeometry ComplexPoint TopologicalSpace Opposite
open HodgeLean.Foundations HodgeLean.RealDefs
open scoped TensorProduct

namespace HodgeLean.Adapters

/-- **The normalization scalar is one nonzero rational.** The instantiated cup product
`cupProductOf X` is `c` times the product transported along the unnormalized comparison
`HQ X n ≃ H^n(X; ℚ) ≃ H^n_sing(X(ℂ); ℚ)` (U1), for one `c ≠ 0` independent of the degrees.
`cupComparison X n` is `s⁻¹` times that comparison in every degree (`normalizedEquiv`), so the
transported product picks up `s · s⁻¹ · s⁻¹ = s⁻¹`. Membership in the `ℂ`-subspaces `F^p` is
insensitive to a nonzero scalar, so this removes `normalizedEquiv` from the comparison of the cup
product with any de Rham product.
Source: Hatcher, *Algebraic Topology*, §3.2 (the cup product), transported by linear
equivalences; `Foundations.Singular.normalizedEquiv` and `cupComparison`. -/
theorem spec_cupProductOf_cup_eq_smul_transportedCup (X : Over (Spec ↧ℂ))
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] :
    ∃ c : ℚ, c ≠ 0 ∧ ∀ {i j k : ℕ} (h : i + j = k) (a : HQ X i) (b : HQ X j),
      (cupProductOf X).cup h a b =
        c • Foundations.Singular.transportedCup (TopCat.of (ComplexPoint X))
          (fun n => (HQ.linearEquiv X n).trans (rationalCohomologyLinearEquivSingular X n))
          h a b :=
  spec_cupProductOf_cup_eq_smul_transportedCup_aux X

/-- The two products have the same zero products. -/
example (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    {i j k : ℕ} (h : i + j = k) (a : HQ X i) (b : HQ X j) :
    (cupProductOf X).cup h a b = 0 ↔
      Foundations.Singular.transportedCup (TopCat.of (ComplexPoint X))
        (fun n => (HQ.linearEquiv X n).trans (rationalCohomologyLinearEquivSingular X n))
        h a b = 0 := by
  obtain ⟨c, hc, hcup⟩ := spec_cupProductOf_cup_eq_smul_transportedCup X
  rw [hcup h a b, smul_eq_zero, or_iff_right hc]

/-- **The edge map is bijective in the lowest degree.** For a complex `S` of sheaves on `X(ℂ)`
that is zero below degree `n`, the map `H^n(Γ(X(ℂ), S)) → ℍ^n(X(ℂ); S)` is bijective: both sides
are the global sections of the kernel of `S^n → S^{n+1}`. This is stage 4c's
`spec_globalSectionsToHypercohomology_one_bijective` in every degree.
Source: Voisin, *Hodge Theory and Complex Algebraic Geometry I*, Cambridge Stud. Adv. Math. 76,
§8.1 (hypercohomology through acyclic resolutions); Bredon, *Sheaf Theory*, 2nd ed., GTM 170,
II.4; `globalSectionsToHypercohomology`. -/
theorem spec_globalSectionsToHypercohomology_bijective_of_isStrictlyGE (X : Over (Spec ↧ℂ))
    (S : CochainComplex (AnalyticAdditiveSheaf X) ℤ) (n : ℤ) [S.IsStrictlyGE n] :
    Function.Bijective (globalSectionsToHypercohomology X S n) :=
  spec_globalSectionsToHypercohomology_bijective_of_isStrictlyGE_aux X S n

/-- The case `S = F^p Ω•(X)` in degree `p`. -/
example (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] (p : ℕ) :
    Function.Bijective (globalSectionsToHypercohomology X (F^(p : ℤ) Ω•(X)) (p : ℤ)) :=
  spec_globalSectionsToHypercohomology_bijective_of_isStrictlyGE X _ _

/-- **A degree-`p` cycle is determined by its form.** `iCycles` is a monomorphism of abelian
groups, and global sections of an isomorphism are bijective.
Source: Mathlib's `HomologicalComplex.iCycles` (a monomorphism); stage 4c's
`spec_cycleOneForm_injective` in every degree. -/
theorem spec_cycleForm_injective (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom]
    (p : ℕ) : Function.Injective (cycleForm X p) :=
  spec_cycleForm_injective_aux X p

example (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] (p : ℕ)
    (z : (filteredGlobalSectionsOf X p).cycles (p : ℤ)) (hz : cycleForm X p z = 0) : z = 0 :=
  spec_cycleForm_injective X p (hz.trans (map_zero _).symm)

/-- **The forms of degree-`p` cycles are the closed forms.** The cycles of `Γ(X(ℂ), F^p Ω•)` in
degree `p` are the kernel of `Γ` of its differential `(F^p Ω•)^p → (F^p Ω•)^{p+1}`, which is the
exterior derivative `Ω^p → Ω^{p+1}` under `filteredDeRhamXIso` (Mathlib's `stupidTrunc` keeps the
differentials in degrees `≥ p`).
Source: Voisin, *Hodge Theory and Complex Algebraic Geometry I*, §8.1.3; Mathlib's
`HomologicalComplex.stupidTrunc`; stage 4c's `spec_range_cycleOneForm` in every degree. -/
theorem spec_range_cycleForm (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] (p : ℕ) :
    (cycleForm X p).range = closedGlobalHolomorphicForms X p :=
  spec_range_cycleForm_aux X p

example (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] (p : ℕ)
    (θ : GlobalHolomorphicForm X p) (hθ : globalHolomorphicDifferential X p θ = 0) :
    ∃ z, cycleForm X p z = θ := by
  have : θ ∈ (cycleForm X p).range := by
    rw [spec_range_cycleForm]
    exact hθ
  exact this

/-- **`F^p H_dR^p(X)` is the set of classes of closed global holomorphic `p`-forms.** The complex
`Γ(X(ℂ), F^p Ω•)` is zero in degree `p - 1`, so `homologyπ` is surjective in degree `p`, and the
edge map is bijective (`spec_globalSectionsToHypercohomology_bijective_of_isStrictlyGE`).
Source: Voisin, *Hodge Theory and Complex Algebraic Geometry I*, §8.1.3 (`F^n H^n = H^0(Ω^n)`
for the closed forms, here with no degeneration input); stage 4c's
`spec_hodgeFiltration_one_eq_range_cycleDeRhamClass` in every degree. -/
theorem spec_hodgeFiltration_eq_range_cycleFormDeRhamClass (X : Over (Spec ↧ℂ))
    [IsIntegral X.left] [Smooth X.hom] (p : ℕ) :
    (F^(p : ℤ) H_dR^(p : ℤ)(X)).toAddSubgroup = (cycleFormDeRhamClass X p).range :=
  spec_hodgeFiltration_eq_range_cycleFormDeRhamClass_aux X p

example (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] (p : ℕ)
    (α : H_dR^(p : ℤ)(X)) (hα : α ∈ F^(p : ℤ) H_dR^(p : ℤ)(X)) :
    ∃ z, cycleFormDeRhamClass X p z = α := by
  have : α ∈ (cycleFormDeRhamClass X p).range := by
    rw [← spec_hodgeFiltration_eq_range_cycleFormDeRhamClass]
    exact hα
  exact this

/-- **The wedge of global holomorphic `1`-forms.** For global holomorphic `1`-forms
`θ_1, …, θ_p` on `X(ℂ)` there is a global holomorphic `p`-form whose value at every `x` is the
wedge `θ_1(x) ∧ ⋯ ∧ θ_p(x)` of their covectors. Near each point the `θ_i` come from Kähler
`1`-forms on one open (`spec_exists_local_representative`); their product in the exterior algebra
evaluates to the wedge of the evaluations (upstream's `chartEvaluation` is built from
`wedgeCovectors`); the local products agree on overlaps because values determine forms
(`spec_eq_zero_of_globalFormValue_eq_zero`), so they glue in the sheaf `Ω^p`.
Source: Griffiths–Harris, *Principles of Algebraic Geometry*, Ch. 0 §2 (the exterior algebra of
holomorphic forms); upstream `ContinuousAlternatingMap.wedgeCovectors`, `chartWedge`. -/
theorem spec_exists_globalFormValue_eq_wedgeCovectors (X : Over (Spec ↧ℂ)) (d : ℕ)
    [SmoothOfRelativeDimension d X.hom] (p : ℕ)
    (θ : Fin p → (holomorphicDeRhamSheaf X d 1).presheaf.obj (op ⊤)) :
    ∃ ζ : (holomorphicDeRhamSheaf X d p).presheaf.obj (op ⊤), ∀ x : ComplexPoint X,
      globalFormValue X d p x ζ =
        ContinuousAlternatingMap.wedgeCovectors ℂ (Fin d → ℂ)
          (fun i => globalOneFormCovector X d (θ i) x) :=
  spec_exists_globalFormValue_eq_wedgeCovectors_aux X d p θ

/-- The wedge is unique, because values determine global forms. -/
example (X : Over (Spec ↧ℂ)) (d : ℕ) [SmoothOfRelativeDimension d X.hom] (p : ℕ)
    (θ : Fin p → (holomorphicDeRhamSheaf X d 1).presheaf.obj (op ⊤))
    (ζ ζ' : (holomorphicDeRhamSheaf X d p).presheaf.obj (op ⊤))
    (hζ : ∀ x, globalFormValue X d p x ζ =
      ContinuousAlternatingMap.wedgeCovectors ℂ (Fin d → ℂ)
        (fun i => globalOneFormCovector X d (θ i) x))
    (hζ' : ∀ x, globalFormValue X d p x ζ' =
      ContinuousAlternatingMap.wedgeCovectors ℂ (Fin d → ℂ)
        (fun i => globalOneFormCovector X d (θ i) x)) :
    ζ = ζ' :=
  sub_eq_zero.mp (spec_eq_zero_of_globalFormValue_eq_zero X d p _ fun x => by
    rw [map_sub, hζ, hζ', sub_self])

/-- **A wedge of closed `1`-forms is closed.** If every `θ_i` is closed, the global form with
values `θ_1(x) ∧ ⋯ ∧ θ_p(x)` is closed: locally it is the product of Kähler representatives, and
the Leibniz rule `d(ω ∧ η) = dω ∧ η + (-1)^{|ω|} ω ∧ dη` (upstream `Algebra.DeRham.extDeriv_mul`)
writes its derivative as a sum of products with a factor `dθ_i`, whose values vanish.
Source: Griffiths–Harris, *Principles of Algebraic Geometry*, Ch. 0 §2 (the Leibniz rule);
upstream `Algebra.DeRham.extDeriv_mul`. -/
theorem spec_differential_eq_zero_of_globalFormValue_eq_wedgeCovectors (X : Over (Spec ↧ℂ))
    (d : ℕ) [SmoothOfRelativeDimension d X.hom] (p : ℕ)
    (θ : Fin p → (holomorphicDeRhamSheaf X d 1).presheaf.obj (op ⊤))
    (hθ : ∀ i, (holomorphicDeRhamSheafDifferential X d 1).hom.app (op ⊤) (θ i) = 0)
    (ζ : (holomorphicDeRhamSheaf X d p).presheaf.obj (op ⊤))
    (hζ : ∀ x : ComplexPoint X, globalFormValue X d p x ζ =
      ContinuousAlternatingMap.wedgeCovectors ℂ (Fin d → ℂ)
        (fun i => globalOneFormCovector X d (θ i) x)) :
    (holomorphicDeRhamSheafDifferential X d p).hom.app (op ⊤) ζ = 0 :=
  spec_differential_eq_zero_of_globalFormValue_eq_wedgeCovectors_aux X d p θ hθ ζ hζ

/-- With the previous statement: the wedge of closed `1`-forms exists and is closed. -/
example (X : Over (Spec ↧ℂ)) (d : ℕ) [SmoothOfRelativeDimension d X.hom] (p : ℕ)
    (θ : Fin p → (holomorphicDeRhamSheaf X d 1).presheaf.obj (op ⊤))
    (hθ : ∀ i, (holomorphicDeRhamSheafDifferential X d 1).hom.app (op ⊤) (θ i) = 0) :
    ∃ ζ : (holomorphicDeRhamSheaf X d p).presheaf.obj (op ⊤),
      (∀ x : ComplexPoint X, globalFormValue X d p x ζ =
        ContinuousAlternatingMap.wedgeCovectors ℂ (Fin d → ℂ)
          (fun i => globalOneFormCovector X d (θ i) x)) ∧
      (holomorphicDeRhamSheafDifferential X d p).hom.app (op ⊤) ζ = 0 := by
  obtain ⟨ζ, hζ⟩ := spec_exists_globalFormValue_eq_wedgeCovectors X d p θ
  exact ⟨ζ, hζ, spec_differential_eq_zero_of_globalFormValue_eq_wedgeCovectors X d p θ hθ ζ hζ⟩

/-- **A wedge of `p` closed holomorphic `1`-forms gives a class in `F^p H_dR^p(X)`.** For smooth
integral `X` and closed global holomorphic `1`-forms `θ_1, …, θ_p`, some degree-`p` cycle of
`Γ(X(ℂ), F^p Ω•)` has the form `θ_1 ∧ ⋯ ∧ θ_p`: the wedge exists and is closed
(`spec_exists_globalFormValue_eq_wedgeCovectors`,
`spec_differential_eq_zero_of_globalFormValue_eq_wedgeCovectors`), and closed forms are forms of
cycles (`spec_range_cycleForm`). Its class `cycleFormDeRhamClass X p z` lies in `F^p` by
construction.
Source: Voisin, *Hodge Theory and Complex Algebraic Geometry I*, §8.1.3; the three statements
named. -/
theorem spec_exists_cycleForm_eq_wedge (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom]
    (p : ℕ) (θ : Fin p → GlobalHolomorphicForm X 1)
    (hθ : ∀ i, θ i ∈ closedGlobalHolomorphicOneForms X) :
    ∃ z : (filteredGlobalSectionsOf X p).cycles (p : ℤ), ∀ x : ComplexPoint X,
      globalFormValue X (dim X.left) p x (cycleForm X p z) =
        ContinuousAlternatingMap.wedgeCovectors ℂ (Fin (dim X.left) → ℂ)
          (fun i => globalOneFormCovector X (dim X.left) (θ i) x) :=
  spec_exists_cycleForm_eq_wedge_aux X p θ hθ

/-- The class of the wedge cycle lies in `F^p H_dR^p(X)`. -/
example (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] (p : ℕ)
    (θ : Fin p → GlobalHolomorphicForm X 1) (hθ : ∀ i, θ i ∈ closedGlobalHolomorphicOneForms X) :
    ∃ z : (filteredGlobalSectionsOf X p).cycles (p : ℤ),
      (∀ x, globalFormValue X (dim X.left) p x (cycleForm X p z) =
        ContinuousAlternatingMap.wedgeCovectors ℂ (Fin (dim X.left) → ℂ)
          (fun i => globalOneFormCovector X (dim X.left) (θ i) x)) ∧
      cycleFormDeRhamClass X p z ∈ F^(p : ℤ) H_dR^(p : ℤ)(X) := by
  obtain ⟨z, hz⟩ := spec_exists_cycleForm_eq_wedge X p θ hθ
  exact ⟨z, hz, _, rfl⟩

/-- **The cup of degree-one classes is alternating.** For abelian `X` and a cup product `μ` with the
torus theorem, permuting the factors of `cupMultiC` multiplies it by the sign: `cupMultiC n v` is
the image of `v 0 ∧ ⋯ ∧ v (n-1)` under the complexified torus isomorphism
(`TorusCohomology.complexificationCongr_symm_ιMulti`), and `ιMulti` is alternating.
Source: Birkenhake–Lange, *Complex Abelian Varieties*, 2nd ed., Grundlehren 302, Lemma 1.3.1;
`TorusCohomology.complexificationCongr_symm_ιMulti` and Mathlib's `AlternatingMap.map_perm`. -/
theorem spec_cupMultiC_comp_perm (X : Over (Spec ↧ℂ)) [GrpObj X] [IsIntegral X.left]
    [Smooth X.hom] [IsProjective X.hom] {μ : CupProduct X} (hT : TorusCohomology μ) (n : ℕ)
    (v : Fin n → ℂ ⊗[ℚ] HQ X 1) (σ : Equiv.Perm (Fin n)) :
    μ.cupMultiC n (v ∘ σ) = Equiv.Perm.sign σ • μ.cupMultiC n v :=
  spec_cupMultiC_comp_perm_aux X hT n v σ

/-- Swapping two degree-one factors changes the sign. -/
example (X : Over (Spec ↧ℂ)) [GrpObj X] [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    {μ : CupProduct X} (hT : TorusCohomology μ) (v : Fin 2 → ℂ ⊗[ℚ] HQ X 1) :
    μ.cupMultiC 2 (v ∘ Equiv.swap 0 1) = -μ.cupMultiC 2 v := by
  rw [spec_cupMultiC_comp_perm X hT, Equiv.Perm.sign_swap (by decide), Units.neg_smul, one_smul]

/-- **Cups of degree-one classes are filtered, from `hL`.** For abelian `X` and a cup product `μ`
with the torus theorem: the implication from `hL` (cup with a class in `F^1 H^1` raises the
filtration by one) to `β_1 (v i) ∈ F^{p_i}` for all `i` ⇒ `β_n (cupMultiC n v) ∈ F^{∑ p_i}`. Factors
with `p_i ≥ 2` vanish (`F^2 H^1 = 0`), factors with `p_i ≤ 0` impose nothing. Reorder the factors
with `p_i = 1` to the front (`spec_cupMultiC_comp_perm`) and apply `hL` once for each of them,
starting from the cup of the others, which lies in `F^0 = H_dR`.
Source: Voisin, *Hodge Theory and Complex Algebraic Geometry I*, §7.1 (through `hL`);
`spec_cupMultiC_comp_perm` and `CupProduct.cupMultiC_succ`. -/
theorem spec_bettiDeRhamHQ_cupMultiC_mem_of_cupLeft (X : Over (Spec ↧ℂ)) [GrpObj X]
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] {μ : CupProduct X}
    (hT : TorusCohomology μ)
    (hL : ∀ {k m : ℕ} (h : 1 + k = m) (q : ℤ) (x : ℂ ⊗[ℚ] HQ X 1) (y : ℂ ⊗[ℚ] HQ X k),
      bettiDeRhamHQ X 1 x ∈ F^1 H_dR^((1 : ℕ) : ℤ)(X) →
      bettiDeRhamHQ X k y ∈ F^q H_dR^(k : ℤ)(X) →
      bettiDeRhamHQ X m (μ.cupC h x y) ∈ F^(1 + q) H_dR^(m : ℤ)(X))
    (n : ℕ) (v : Fin n → ℂ ⊗[ℚ] HQ X 1) (p : Fin n → ℤ)
    (hv : ∀ i, bettiDeRhamHQ X 1 (v i) ∈ F^(p i) H_dR^((1 : ℕ) : ℤ)(X)) :
    bettiDeRhamHQ X n (μ.cupMultiC n v) ∈ F^(∑ i, p i) H_dR^(n : ℤ)(X) :=
  spec_bettiDeRhamHQ_cupMultiC_mem_of_cupLeft_aux X hT hL n v p hv

/-- `n` classes of holomorphic `1`-forms cup into `F^n H_dR^n(X)`. -/
example (X : Over (Spec ↧ℂ)) [GrpObj X] [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    {μ : CupProduct X} (hT : TorusCohomology μ)
    (hL : ∀ {k m : ℕ} (h : 1 + k = m) (q : ℤ) (x : ℂ ⊗[ℚ] HQ X 1) (y : ℂ ⊗[ℚ] HQ X k),
      bettiDeRhamHQ X 1 x ∈ F^1 H_dR^((1 : ℕ) : ℤ)(X) →
      bettiDeRhamHQ X k y ∈ F^q H_dR^(k : ℤ)(X) →
      bettiDeRhamHQ X m (μ.cupC h x y) ∈ F^(1 + q) H_dR^(m : ℤ)(X))
    (n : ℕ) (v : Fin n → ℂ ⊗[ℚ] HQ X 1)
    (hv : ∀ i, bettiDeRhamHQ X 1 (v i) ∈ F^1 H_dR^((1 : ℕ) : ℤ)(X)) :
    bettiDeRhamHQ X n (μ.cupMultiC n v) ∈ F^(n : ℤ) H_dR^(n : ℤ)(X) := by
  have := spec_bettiDeRhamHQ_cupMultiC_mem_of_cupLeft X hT hL n v (fun _ => 1) hv
  simpa using this

/-- **The cup-wedge pieces lie in the Hodge pieces, from `hL`.** For abelian `X` and a cup product
`μ` with the torus theorem: the implication from `hL` to
`cupWedgePiece X μ n pq ≤ deRhamHodgePiece X n pq`. This is stage 4m's
`spec_cupWedgePiece_le_deRhamHodgePiece` with `hL` in place of `CupFiltered X μ`. On a generator,
`F` is `spec_bettiDeRhamHQ_cupMultiC_mem_of_cupLeft`, and `conj F` is the same statement for
`sigmaQ` of the factors (`CupProduct.sigmaQ_cupC`, `bettiDeRhamHQ_sigmaQ`), since `hL` and
`sigmaQ`-conjugation give `hL` for `conj F`.
Source: Voisin, *Hodge Theory and Complex Algebraic Geometry I*, §7.1 (through `hL`);
`spec_bettiDeRhamHQ_cupMultiC_mem_of_cupLeft` and stage 4m's `spec_cupWedgePiece_eq_bot`. -/
theorem spec_cupWedgePiece_le_deRhamHodgePiece_of_cupLeft (X : Over (Spec ↧ℂ)) [GrpObj X]
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] {μ : CupProduct X}
    (hT : TorusCohomology μ)
    (hL : ∀ {k m : ℕ} (h : 1 + k = m) (q : ℤ) (x : ℂ ⊗[ℚ] HQ X 1) (y : ℂ ⊗[ℚ] HQ X k),
      bettiDeRhamHQ X 1 x ∈ F^1 H_dR^((1 : ℕ) : ℤ)(X) →
      bettiDeRhamHQ X k y ∈ F^q H_dR^(k : ℤ)(X) →
      bettiDeRhamHQ X m (μ.cupC h x y) ∈ F^(1 + q) H_dR^(m : ℤ)(X))
    (n : ℕ) (pq : ℤ × ℤ) :
    cupWedgePiece X μ n pq ≤ deRhamHodgePiece X n pq :=
  spec_cupWedgePiece_le_deRhamHodgePiece_of_cupLeft_aux X hT hL n pq

example (X : Over (Spec ↧ℂ)) [GrpObj X] [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    {μ : CupProduct X} (hT : TorusCohomology μ)
    (hL : ∀ {k m : ℕ} (h : 1 + k = m) (q : ℤ) (x : ℂ ⊗[ℚ] HQ X 1) (y : ℂ ⊗[ℚ] HQ X k),
      bettiDeRhamHQ X 1 x ∈ F^1 H_dR^((1 : ℕ) : ℤ)(X) →
      bettiDeRhamHQ X k y ∈ F^q H_dR^(k : ℤ)(X) →
      bettiDeRhamHQ X m (μ.cupC h x y) ∈ F^(1 + q) H_dR^(m : ℤ)(X))
    (n : ℕ) (d : Fin n → ℤ × ℤ) (v : Fin n → ℂ ⊗[ℚ] HQ X 1)
    (hv : ∀ i, v i ∈ cohomologyHodgePiece X 1 (d i)) :
    bettiDeRhamHQ X n (μ.cupMultiC n v) ∈ deRhamHodgePiece X n (HodgeBlocks.totalBidegree n d) :=
  spec_cupWedgePiece_le_deRhamHodgePiece_of_cupLeft X hT hL n _
    (Submodule.subset_span ⟨d, v, rfl, hv, rfl⟩)

/-- **The Hodge filtration from `hL` and opposedness in degree `n`.** For abelian `X` and a cup
product `μ` with the torus theorem: the implication from `hL` and `F^p ∩ conj F^{n+1-p} = 0` in
`H_dR^n(X)` for `1 ≤ p ≤ n` to `F^p H_dR^n(X) = ⨆_{p' ≥ p} cupWedgePiece X μ n (p', n - p')`. `≥`:
each piece lies in `F^{p'} ≤ F^p` (`spec_cupWedgePiece_le_deRhamHodgePiece_of_cupLeft`). `≤`:
write `x ∈ F^p` as a sum of pieces (`spec_cupWedgePiece_isInternal`); the part with `p' < p` lies
in `F^p` and in `conj F^{n+1-p}`, so it is `0` (for `p ≤ 0` and `p > n` without the binder).
Source: Deligne, *Théorie de Hodge II*, Publ. Math. IHÉS 40 (1971), §1.2; stage 4m's
`spec_cupWedgePiece_isInternal` and `spec_cupWedgePiece_eq_bot`. -/
theorem spec_hodgeFiltration_eq_iSup_cupWedgePiece_of_cupLeft (X : Over (Spec ↧ℂ)) [GrpObj X]
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] {μ : CupProduct X}
    (hT : TorusCohomology μ)
    (hL : ∀ {k m : ℕ} (h : 1 + k = m) (q : ℤ) (x : ℂ ⊗[ℚ] HQ X 1) (y : ℂ ⊗[ℚ] HQ X k),
      bettiDeRhamHQ X 1 x ∈ F^1 H_dR^((1 : ℕ) : ℤ)(X) →
      bettiDeRhamHQ X k y ∈ F^q H_dR^(k : ℤ)(X) →
      bettiDeRhamHQ X m (μ.cupC h x y) ∈ F^(1 + q) H_dR^(m : ℤ)(X))
    (n : ℕ) (hopp : ∀ p : ℤ, 1 ≤ p → p ≤ n → hodgePiece X p ((n : ℤ) + 1 - p) n = ⊥)
    (p : ℤ) :
    F^p H_dR^(n : ℤ)(X) = ⨆ (p' : ℤ) (_ : p ≤ p'), cupWedgePiece X μ n (p', (n : ℤ) - p') :=
  spec_hodgeFiltration_eq_iSup_cupWedgePiece_of_cupLeft_aux X hT hL n hopp p

/-- Each piece of type `(p', n - p')` with `p ≤ p'` lies in `F^p`. -/
example (X : Over (Spec ↧ℂ)) [GrpObj X] [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    {μ : CupProduct X} (hT : TorusCohomology μ)
    (hL : ∀ {k m : ℕ} (h : 1 + k = m) (q : ℤ) (x : ℂ ⊗[ℚ] HQ X 1) (y : ℂ ⊗[ℚ] HQ X k),
      bettiDeRhamHQ X 1 x ∈ F^1 H_dR^((1 : ℕ) : ℤ)(X) →
      bettiDeRhamHQ X k y ∈ F^q H_dR^(k : ℤ)(X) →
      bettiDeRhamHQ X m (μ.cupC h x y) ∈ F^(1 + q) H_dR^(m : ℤ)(X))
    (n : ℕ) (hopp : ∀ p : ℤ, 1 ≤ p → p ≤ n → hodgePiece X p ((n : ℤ) + 1 - p) n = ⊥)
    (p : ℤ) :
    cupWedgePiece X μ n (p, (n : ℤ) - p) ≤ F^p H_dR^(n : ℤ)(X) := by
  rw [spec_hodgeFiltration_eq_iSup_cupWedgePiece_of_cupLeft X hT hL n hopp p]
  exact le_iSup₂_of_le (f := fun (p' : ℤ) (_ : p ≤ p') => cupWedgePiece X μ n (p', (n : ℤ) - p'))
    p le_rfl le_rfl

/-- **`CupFiltered` from `hL` and opposedness.** (With opp1's argument run from `hL`, see the
module docstring, the opposedness hypothesis is redundant for abelian `X`. That reduction is a
later stage.)
For abelian `X` and a cup product `μ` with the torus theorem: the implication from `hL` and
`F^p ∩ conj F^{n+1-p} = 0` in `H_dR^n(X)` for `2 ≤ n ≤ 2 · dim X` and `1 ≤ p ≤ n` to
`CupFiltered X μ`. By `spec_hodgeFiltration_eq_iSup_cupWedgePiece_of_cupLeft` (degrees `0` and `1` are
stage 4l and stage 4b, degrees above `2g` are zero), `β^{-1} F^p H^i` is spanned by cups of typed
degree-one classes with at least `p` factors of type `(1, 0)`. The cup of two such cups is a cup of
the concatenated factors (associativity and the unit law of `μ`), with at least `p + q` factors of
type `(1, 0)`, so it lies in `F^{p+q}` (`spec_bettiDeRhamHQ_cupMultiC_mem_of_cupLeft`).
`CupFiltered X μ` implies `hL` (the `example`), so `hL` is the smaller input.
Source: Deligne, *Théorie de Hodge II*, Publ. Math. IHÉS 40 (1971), §1.2; Birkenhake–Lange,
*Complex Abelian Varieties*, 2nd ed., Grundlehren 302, Lemma 1.3.1;
`spec_hodgeFiltration_eq_iSup_cupWedgePiece_of_cupLeft` and `spec_bettiDeRhamHQ_cupMultiC_mem_of_cupLeft`. -/
theorem spec_cupFiltered_of_cupLeft (X : Over (Spec ↧ℂ)) [GrpObj X] [IsIntegral X.left]
    [Smooth X.hom] [IsProjective X.hom] {μ : CupProduct X} (hT : TorusCohomology μ)
    (hL : ∀ {k m : ℕ} (h : 1 + k = m) (q : ℤ) (x : ℂ ⊗[ℚ] HQ X 1) (y : ℂ ⊗[ℚ] HQ X k),
      bettiDeRhamHQ X 1 x ∈ F^1 H_dR^((1 : ℕ) : ℤ)(X) →
      bettiDeRhamHQ X k y ∈ F^q H_dR^(k : ℤ)(X) →
      bettiDeRhamHQ X m (μ.cupC h x y) ∈ F^(1 + q) H_dR^(m : ℤ)(X))
    (hopp : ∀ n : ℕ, 2 ≤ n → n ≤ 2 * dim X.left → ∀ p : ℤ, 1 ≤ p → p ≤ n →
      hodgePiece X p ((n : ℤ) + 1 - p) n = ⊥) :
    CupFiltered X μ :=
  spec_cupFiltered_of_cupLeft_aux X hT hL hopp

/-- `hL` is the case `i = 1`, `p = 1` of `CupFiltered X μ`. -/
example (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    {μ : CupProduct X} (hC : CupFiltered X μ) :
    ∀ {k m : ℕ} (h : 1 + k = m) (q : ℤ) (x : ℂ ⊗[ℚ] HQ X 1) (y : ℂ ⊗[ℚ] HQ X k),
      bettiDeRhamHQ X 1 x ∈ F^1 H_dR^((1 : ℕ) : ℤ)(X) →
      bettiDeRhamHQ X k y ∈ F^q H_dR^(k : ℤ)(X) →
      bettiDeRhamHQ X m (μ.cupC h x y) ∈ F^(1 + q) H_dR^(m : ℤ)(X) :=
  fun h q x y hx hy => hC.mem h 1 q x y hx hy

/-- With the instantiated cup product, whose torus theorem is proved. -/
example (X : Over (Spec ↧ℂ)) [GrpObj X] [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    (hL : ∀ {k m : ℕ} (h : 1 + k = m) (q : ℤ) (x : ℂ ⊗[ℚ] HQ X 1) (y : ℂ ⊗[ℚ] HQ X k),
      bettiDeRhamHQ X 1 x ∈ F^1 H_dR^((1 : ℕ) : ℤ)(X) →
      bettiDeRhamHQ X k y ∈ F^q H_dR^(k : ℤ)(X) →
      bettiDeRhamHQ X m ((cupProductOf X).cupC h x y) ∈ F^(1 + q) H_dR^(m : ℤ)(X))
    (hopp : ∀ n : ℕ, 2 ≤ n → n ≤ 2 * dim X.left → ∀ p : ℤ, 1 ≤ p → p ≤ n →
      hodgePiece X p ((n : ℤ) + 1 - p) n = ⊥) :
    CupFiltered X (cupProductOf X) :=
  spec_cupFiltered_of_cupLeft X (torusCohomology_cupProductOf X) hL hopp

/-- **`HodgeDecomposition X` from `hL` and opposedness.** For abelian `X` and a cup product `μ`
with the torus theorem: the implication from `hL` and `F^p ∩ conj F^{n+1-p} = 0` in `H_dR^n(X)`
for `2 ≤ n ≤ 2 · dim X` and `1 ≤ p ≤ n` to `HodgeDecomposition X`. This is stage 4m's
`spec_hodgeDecomposition_of_opposed` with `hL` in place of `CupFiltered X μ`.
Source: Birkenhake–Lange, *Complex Abelian Varieties*, 2nd ed., Grundlehren 302, Lemma 1.3.1 and
Theorem 1.4.1; Deligne, *Théorie de Hodge II*, Publ. Math. IHÉS 40 (1971), §1.2;
`spec_cupFiltered_of_cupLeft` and stage 4m's `spec_hodgeDecomposition_of_opposed`. -/
theorem spec_hodgeDecomposition_of_cupLeft (X : Over (Spec ↧ℂ)) [GrpObj X]
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] {μ : CupProduct X}
    (hT : TorusCohomology μ)
    (hL : ∀ {k m : ℕ} (h : 1 + k = m) (q : ℤ) (x : ℂ ⊗[ℚ] HQ X 1) (y : ℂ ⊗[ℚ] HQ X k),
      bettiDeRhamHQ X 1 x ∈ F^1 H_dR^((1 : ℕ) : ℤ)(X) →
      bettiDeRhamHQ X k y ∈ F^q H_dR^(k : ℤ)(X) →
      bettiDeRhamHQ X m (μ.cupC h x y) ∈ F^(1 + q) H_dR^(m : ℤ)(X))
    (hopp : ∀ n : ℕ, 2 ≤ n → n ≤ 2 * dim X.left → ∀ p : ℤ, 1 ≤ p → p ≤ n →
      hodgePiece X p ((n : ℤ) + 1 - p) n = ⊥) :
    HodgeDecomposition X :=
  spec_hodgeDecomposition_of_cupLeft_aux X hT hL hopp

/-- With the instantiated cup product, the open inputs are `hL` and the opposedness. -/
example (X : Over (Spec ↧ℂ)) [GrpObj X] [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    (hL : ∀ {k m : ℕ} (h : 1 + k = m) (q : ℤ) (x : ℂ ⊗[ℚ] HQ X 1) (y : ℂ ⊗[ℚ] HQ X k),
      bettiDeRhamHQ X 1 x ∈ F^1 H_dR^((1 : ℕ) : ℤ)(X) →
      bettiDeRhamHQ X k y ∈ F^q H_dR^(k : ℤ)(X) →
      bettiDeRhamHQ X m ((cupProductOf X).cupC h x y) ∈ F^(1 + q) H_dR^(m : ℤ)(X))
    (hopp : ∀ n : ℕ, 2 ≤ n → n ≤ 2 * dim X.left → ∀ p : ℤ, 1 ≤ p → p ≤ n →
      hodgePiece X p ((n : ℤ) + 1 - p) n = ⊥) :
    HodgeDecomposition X :=
  spec_hodgeDecomposition_of_cupLeft X (torusCohomology_cupProductOf X) hL hopp

end HodgeLean.Adapters
