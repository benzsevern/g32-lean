import HodgeLean.Adapters.CurveStructureSheafVanishingProofs

/-! # `H^2(X, 𝒪_X) = 0` for curves, and `CycleClassIsHodge` for curves (FROZEN SPEC)

Scope. The cch spec (`CycleClassHodgeCurve.lean`) proves `CycleClassIsHodge X` for an integral
smooth projective curve as an implication from `Subsingleton ℍ^2(X; holomorphicFormsShifted X 0)`,
that is `H^2(X(ℂ), 𝒪) = 0`. Nothing here or upstream proves that vanishing: there is no sheaf of
smooth `(0, 1)`-forms on `X(ℂ)`, no fine or soft sheaf acyclicity, and no dimension vanishing for
sheaf cohomology. This spec freezes two routes.

* **Resolution route.** A long exact sequence step (statement 1) turns a short exact sequence of
  sheaves `0 → 𝒪 → A → B → 0` with `ℍ^2(A[0]) = 0` and `ℍ^1(B[0]) = 0` into `H^2(X(ℂ), 𝒪) = 0`
  (statement 2), hence into `CycleClassIsHodge X` for curves (statement 3). On a Riemann surface the
  Dolbeault sequence `0 → 𝒪 → 𝒜^{0,0} → 𝒜^{0,1} → 0` has this shape, with `A`, `B` fine.
* **Hodge decomposition route.** `F^p H_dR^n(X) = ⊥` for `p > dim X` (statement 4), so under the
  existing named input `HodgeDecomposition X` only the `(d, d)` piece of `H^{2d}` survives and
  `F^d H_dR^{2d}(X) = ⊤` (statement 5). For a curve this is `F^1 H_dR^2 = ⊤`, and
  `CycleClassIsHodge X` follows (statement 6) without `H^2(X(ℂ), 𝒪) = 0`.

Claimed: statements 1, 2, 4 for every `X` in their stated generality; `CycleClassIsHodge X` for
every integral smooth projective curve `X` over `ℂ` as an implication from the explicit binders of
statement 3 (a short exact sequence `0 → 𝒪 → A → B → 0` with the two vanishings), and separately
as an implication from `HodgeDecomposition X` (statement 6). Falsification checks: statement 7
(the vanishing fails whenever `H^{0,n} ≠ 0`, for instance `n = 2` on an abelian surface) and
statement 8 (the bound `p > dim X` of statement 4 is sharp on curves).

Not claimed: `CycleClassIsHodge X` for curves unconditionally; the vanishing
`H^2(X(ℂ), 𝒪) = 0` itself; the Dolbeault resolution, its sheaves, or their acyclicity; dimension
vanishing of sheaf cohomology above the real dimension `2`; `HodgeDecomposition X` itself. No new
`@[hodge_hypothesis]`.
HC no distance; AV milestone no distance.
-/

noncomputable section
open CategoryTheory TopologicalSpace AlgebraicGeometry ComplexPoint
open HodgeLean.RealDefs

namespace HodgeLean.Adapters

/-- **One step of the long exact sequence.** For a short exact sequence `0 → K₁ → K₂ → K₃ → 0` of
complexes of sheaves on `X(ℂ)`, if `ℍ^n(X; K₂) = 0` and `ℍ^{n-1}(X; K₃) = 0`, then
`ℍ^n(X; K₁) = 0`: the sequence `ℍ^{n-1}(K₃) → ℍ^n(K₁) → ℍ^n(K₂)` is exact.
Source: Voisin, *Hodge Theory and Complex Algebraic Geometry I*, Cambridge Stud. Adv. Math. 76,
§8.1.2 (the long exact sequence of hypercohomology of a short exact sequence of complexes);
Mathlib's `DerivedCategory.triangleOfSES_distinguished` and
`Pretriangulated.Triangle.coyoneda_exact₁`. -/
theorem spec_hypercohomology_subsingleton_of_shortExact (X : Over (Spec ↧ℂ))
    {S : ShortComplex (CochainComplex (AnalyticAdditiveSheaf X) ℤ)} (hS : S.ShortExact) (n : ℤ)
    (h₂ : Subsingleton ℍ^n(X; S.X₂)) (h₃ : Subsingleton ℍ^(n - 1)(X; S.X₃)) :
    Subsingleton ℍ^n(X; S.X₁) :=
  spec_hypercohomology_subsingleton_of_shortExact_aux X hS n h₂ h₃

/-- Degree two, the case used in statement 2. -/
example (X : Over (Spec ↧ℂ)) {S : ShortComplex (CochainComplex (AnalyticAdditiveSheaf X) ℤ)}
    (hS : S.ShortExact) (h₂ : Subsingleton ℍ^2(X; S.X₂))
    (h₃ : Subsingleton ℍ^(2 - 1)(X; S.X₃)) :
    Subsingleton ℍ^2(X; S.X₁) :=
  spec_hypercohomology_subsingleton_of_shortExact X hS 2 h₂ h₃

/-- **`H^2(X(ℂ), 𝒪) = 0` from a two-term acyclic-enough resolution.** If
`0 → 𝒪 → A → B → 0` is a short exact sequence of sheaves on `X(ℂ)` with `H^2(X(ℂ), A) = 0` and
`H^1(X(ℂ), B) = 0` (as hypercohomology of the complexes `A[0]`, `B[0]`), then
`ℍ^2(X; holomorphicFormsShifted X 0) = H^2(X(ℂ), 𝒪)` vanishes. Here `𝒪` is `Ω•(X).X 0`, the
degree-zero term of upstream's holomorphic de Rham complex. On a compact Riemann surface the
Dolbeault sequence `0 → 𝒪 → 𝒜^{0,0} → 𝒜^{0,1} → 0` (exact by the `∂̄`-Poincaré lemma in one
variable) has fine, hence acyclic, middle and right terms.
Source: Griffiths–Harris, *Principles of Algebraic Geometry*, Ch. 0 §2 (the `∂̄`-Poincaré lemma in
one variable) and §3 (fine resolutions; Dolbeault's theorem); Voisin, *Hodge Theory and Complex
Algebraic Geometry I*, §8.1.2; here statement 1 applied to the image of the sequence under
`HomologicalComplex.single _ _ 0`. -/
theorem spec_subsingleton_hypercohomology_two_of_shortExact (X : Over (Spec ↧ℂ))
    [IsIntegral X.left] [Smooth X.hom] {A B : AnalyticAdditiveSheaf X} (f : Ω•(X).X 0 ⟶ A)
    (g : A ⟶ B) (w : f ≫ g = 0) (hS : (ShortComplex.mk f g w).ShortExact)
    (hA : Subsingleton
      ℍ^2(X; (HomologicalComplex.single (AnalyticAdditiveSheaf X) (ComplexShape.up ℤ) 0).obj A))
    (hB : Subsingleton
      ℍ^1(X; (HomologicalComplex.single (AnalyticAdditiveSheaf X) (ComplexShape.up ℤ) 0).obj B)) :
    Subsingleton ℍ^2(X; holomorphicFormsShifted X 0) :=
  spec_subsingleton_hypercohomology_two_of_shortExact_aux X f g w hS hA hB

/-- With the cch spec, the same binders give `F^1 H_dR^2(X) = F^0 H_dR^2(X)`. -/
example (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] {A B : AnalyticAdditiveSheaf X}
    (f : Ω•(X).X 0 ⟶ A) (g : A ⟶ B) (w : f ≫ g = 0) (hS : (ShortComplex.mk f g w).ShortExact)
    (hA : Subsingleton
      ℍ^2(X; (HomologicalComplex.single (AnalyticAdditiveSheaf X) (ComplexShape.up ℤ) 0).obj A))
    (hB : Subsingleton
      ℍ^1(X; (HomologicalComplex.single (AnalyticAdditiveSheaf X) (ComplexShape.up ℤ) 0).obj B)) :
    F^(0 + 1) H_dR^2(X) = F^0 H_dR^2(X) :=
  spec_hodgeFiltration_succ_eq_of_subsingleton X 0 2
    (spec_subsingleton_hypercohomology_two_of_shortExact X f g w hS hA hB)

/-- **Assembly, resolution route: `CycleClassIsHodge` for curves**, as an implication from a short
exact sequence `0 → 𝒪 → A → B → 0` of sheaves on `X(ℂ)` with `H^2(X(ℂ), A) = 0` and
`H^1(X(ℂ), B) = 0`. For an integral smooth projective curve `X` over `ℂ` these are the Dolbeault
data; the conclusion is statement 2 followed by `spec_cycleClassIsHodge_of_curve` (cch spec).
Source: Griffiths–Harris, *Principles of Algebraic Geometry*, Ch. 0 §2–3; Voisin, *Hodge Theory and
Complex Algebraic Geometry I*, §§11.1.2–11.1.3 (cycle classes are of type `(p, p)`). -/
theorem spec_cycleClassIsHodge_of_curve_of_shortExact (X : Over (Spec ↧ℂ))
    [IsIntegral X.left] [Smooth X.hom] [SmoothOfRelativeDimension 1 X.hom] [IsProjective X.hom]
    {A B : AnalyticAdditiveSheaf X} (f : Ω•(X).X 0 ⟶ A)
    (g : A ⟶ B) (w : f ≫ g = 0) (hS : (ShortComplex.mk f g w).ShortExact)
    (hA : Subsingleton
      ℍ^2(X; (HomologicalComplex.single (AnalyticAdditiveSheaf X) (ComplexShape.up ℤ) 0).obj A))
    (hB : Subsingleton
      ℍ^1(X; (HomologicalComplex.single (AnalyticAdditiveSheaf X) (ComplexShape.up ℤ) 0).obj B)) :
    CycleClassIsHodge X :=
  spec_cycleClassIsHodge_of_curve_of_shortExact_aux X f g w hS hA hB

/-- The codimension-one part, with the same binders. -/
example (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom]
    [SmoothOfRelativeDimension 1 X.hom] [IsProjective X.hom] {A B : AnalyticAdditiveSheaf X}
    (f : Ω•(X).X 0 ⟶ A) (g : A ⟶ B) (w : f ≫ g = 0) (hS : (ShortComplex.mk f g w).ShortExact)
    (hA : Subsingleton
      ℍ^2(X; (HomologicalComplex.single (AnalyticAdditiveSheaf X) (ComplexShape.up ℤ) 0).obj A))
    (hB : Subsingleton
      ℍ^1(X; (HomologicalComplex.single (AnalyticAdditiveSheaf X) (ComplexShape.up ℤ) 0).obj B)) :
    algebraicCycleClassSpan X 1 ≤ Hdg^1(X; ℚ) :=
  (spec_cycleClassIsHodge_of_curve_of_shortExact X f g w hS hA hB).le 1

/-- **`F^p` vanishes above the dimension.** For `p > dim X`, `F^p H_dR^n(X) = ⊥` in every degree
`n`: every term of `σ_{≥p} Ω•(X)` is zero, since `Ω^q = 0` for `q > dim X`
(`holomorphicDeRhamSheaf_isZero_of_lt`) and the truncation is zero below `p`, so its
hypercohomology is zero. Unconditional.
Source: Voisin, *Hodge Theory and Complex Algebraic Geometry I*, §8.3.1 (the Hodge filtration as
the image of the hypercohomology of `σ_{≥p} Ω•`); upstream `holomorphicDeRhamSheaf_isZero_of_lt`. -/
theorem spec_hodgeFiltration_eq_bot_of_dim_lt (X : Over (Spec ↧ℂ)) [IsIntegral X.left]
    [Smooth X.hom] {p : ℤ} (hp : (dim X.left : ℤ) < p) (n : ℤ) :
    F^p H_dR^n(X) = ⊥ :=
  spec_hodgeFiltration_eq_bot_of_dim_lt_aux X hp n

/-- On a curve, `F^2 H_dR^2(X) = ⊥` (while `hodgeFiltration_eq_bot_of_lt` only reaches `p > 2`). -/
example (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom]
    [SmoothOfRelativeDimension 1 X.hom] :
    F^2 H_dR^2(X) = ⊥ :=
  spec_hodgeFiltration_eq_bot_of_dim_lt X
    (by rw [SmoothOfRelativeDimension.dim_eq X.hom 1]; norm_num) 2

/-- **Top-degree classes lie in `F^d`, from the Hodge decomposition.** For `d = dim X`, under
`HodgeDecomposition X`, `F^d H_dR^{2d}(X) = ⊤`: on the line `p + q = 2d` every piece with `p > d`
or `q > d` is zero by statement 4 (directly, or through conjugation), so `H^{2d}` is the single
piece `hodgePiece X d d (2d) ≤ F^d`.
Source: Voisin, *Hodge Theory and Complex Algebraic Geometry I*, Ch. 6 §6.1 (the Hodge
decomposition; `H^{p,q} = 0` unless `0 ≤ p, q ≤ dim X`); here statement 4 and
`HodgeDecomposition` (`RealDefs/HodgeStructure.lean`). -/
theorem spec_hodgeFiltration_dim_eq_top_of_hodgeDecomposition (X : Over (Spec ↧ℂ))
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] (hD : HodgeDecomposition X) :
    F^((dim X.left : ℕ) : ℤ) H_dR^((2 * dim X.left : ℕ) : ℤ)(X) = ⊤ :=
  spec_hodgeFiltration_dim_eq_top_of_hodgeDecomposition_aux X hD

/-- Every top-degree class is a Hodge class, under `HodgeDecomposition X` (with the cch spec). -/
example (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    (hD : HodgeDecomposition X) :
    Hdg^(dim X.left)(X; ℚ) = ⊤ :=
  spec_hodgeClasses_eq_top_of_hodgeFiltration X (dim X.left)
    (spec_hodgeFiltration_dim_eq_top_of_hodgeDecomposition X hD)

/-- **Assembly, Hodge decomposition route: `CycleClassIsHodge` for curves**, as an implication from
`HodgeDecomposition X`, with no vanishing of `H^2(X(ℂ), 𝒪)`. Codimension `0` by
`spec_hodgeClasses_zero_eq_top`, codimension `1` by statement 5 (`d = 1`) and
`spec_hodgeClasses_eq_top_of_hodgeFiltration`, codimension `p ≥ 2` by
`spec_algebraicCycleClassSpan_le_hodgeClasses_of_subsingleton` and `j5d_subsingleton_HQ_of_lt`.
Source: Voisin, *Hodge Theory and Complex Algebraic Geometry I*, Ch. 6 §6.1 and §§11.1.2–11.1.3;
the cch spec (`CycleClassHodgeCurve.lean`). -/
theorem spec_cycleClassIsHodge_of_curve_of_hodgeDecomposition (X : Over (Spec ↧ℂ))
    [IsIntegral X.left] [Smooth X.hom] [SmoothOfRelativeDimension 1 X.hom] [IsProjective X.hom]
    (hD : HodgeDecomposition X) :
    CycleClassIsHodge X :=
  spec_cycleClassIsHodge_of_curve_of_hodgeDecomposition_aux X hD

/-- With `j5d_algebraicCycleClassSpan_one_eq_top`: on a curve, under `HodgeDecomposition X`, the
codimension-one cycle classes are exactly the rational Hodge classes of degree two. -/
example (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom]
    [SmoothOfRelativeDimension 1 X.hom] [IsProjective X.hom] (hD : HodgeDecomposition X) :
    algebraicCycleClassSpan X 1 = Hdg^1(X; ℚ) :=
  le_antisymm ((spec_cycleClassIsHodge_of_curve_of_hodgeDecomposition X hD).le 1)
    ((j5d_algebraicCycleClassSpan_one_eq_top HodgeLean.Adapters.complexPointsPreconnected X).symm
      ▸ le_top)

/-- **Falsification check: the vanishing fails when `H^{0,n} ≠ 0`.** Under `HodgeDecomposition X`,
if `hodgePiece X 0 n n ≠ ⊥`, then `ℍ^n(X; 𝒪[0]) = H^n(X(ℂ), 𝒪)` is not zero. Otherwise
`F^1 H_dR^n = F^0 H_dR^n = ⊤` (cch statement 1), so `hodgePiece X 0 n n = conj F^n` lies in
`F^1 ∩ conj F^{n-1} = hodgePiece X 1 (n-1) n`, and independence of the decomposition forces it to
be zero. On an abelian surface `n = 2` and `H^{0,2} ≅ ℂ`, so `H^2(X(ℂ), 𝒪) ≠ 0`: the curve
vanishing does not extend to dimension two.
Source: Voisin, *Hodge Theory and Complex Algebraic Geometry I*, Ch. 6 §6.1 and §8.3.1; Birkenhake–
Lange, *Complex Abelian Varieties*, 2nd ed., Grundlehren 302, §1.4 (`H^q(X, 𝒪_X) ≅ ⋀^q \bar{V}^*`);
here `spec_hodgeFiltration_succ_eq_of_subsingleton` (cch spec). -/
theorem spec_not_subsingleton_hypercohomology_of_hodgePiece_ne_bot (X : Over (Spec ↧ℂ))
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] (hD : HodgeDecomposition X) (n : ℕ)
    (h : hodgePiece X 0 (n : ℤ) (n : ℤ) ≠ ⊥) :
    ¬ Subsingleton ℍ^(n : ℤ)(X; holomorphicFormsShifted X 0) :=
  spec_not_subsingleton_hypercohomology_of_hodgePiece_ne_bot_aux X hD n h

/-- The surface case: `H^{0,2} ≠ 0` rules out `H^2(X(ℂ), 𝒪) = 0`. -/
example (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    (hD : HodgeDecomposition X) (h : hodgePiece X 0 ((2 : ℕ) : ℤ) ((2 : ℕ) : ℤ) ≠ ⊥) :
    Nontrivial ℍ^((2 : ℕ) : ℤ)(X; holomorphicFormsShifted X 0) :=
  not_subsingleton_iff_nontrivial.mp
    (spec_not_subsingleton_hypercohomology_of_hodgePiece_ne_bot X hD 2 h)

/-- **Falsification check: statement 4 is sharp.** On an integral smooth projective curve, under
`BettiDeRhamIso X` and `HodgeDecomposition X`, `F^1 H_dR^2(X) ≠ ⊥`: it is `⊤` by statement 5, and
`H_dR^2(X) ≅ ℂ ⊗ H^2(X(ℂ); ℚ)` is a line (`j5d_finrank_HQ_two`). So `p > dim X` in statement 4
cannot be weakened to `p ≥ dim X`.
Source: Voisin, *Hodge Theory and Complex Algebraic Geometry I*, Ch. 6 §6.1; Hatcher, *Algebraic
Topology*, Theorem 3.26(a); here statement 5 and `j5d_finrank_HQ_two`
(`RealDefs/TopDegreeRank.lean`). -/
theorem spec_hodgeFiltration_one_two_ne_bot_of_curve (X : Over (Spec ↧ℂ))
    [IsIntegral X.left] [Smooth X.hom] [SmoothOfRelativeDimension 1 X.hom] [IsProjective X.hom]
    (hB : BettiDeRhamIso X) (hD : HodgeDecomposition X) :
    F^1 H_dR^2(X) ≠ ⊥ :=
  spec_hodgeFiltration_one_two_ne_bot_of_curve_aux X hB hD

/-- So `F^1 H_dR^2(X) ≠ F^2 H_dR^2(X)` on a curve, under the same inputs. -/
example (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom]
    [SmoothOfRelativeDimension 1 X.hom] [IsProjective X.hom]
    (hB : BettiDeRhamIso X) (hD : HodgeDecomposition X) :
    F^1 H_dR^2(X) ≠ F^2 H_dR^2(X) := fun h =>
  spec_hodgeFiltration_one_two_ne_bot_of_curve X hB hD (h.trans
    (spec_hodgeFiltration_eq_bot_of_dim_lt X
      (by rw [SmoothOfRelativeDimension.dim_eq X.hom 1]; norm_num) 2))

end HodgeLean.Adapters
