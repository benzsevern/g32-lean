import HodgeLean.Adapters.CycleClassHodgeCurveProofs

/-! # `CycleClassIsHodge` for curves (FROZEN SPEC)

Scope. Upstream's `F^p H_dR^n(X)` is the image of `ℍ^n(X; σ_{≥p} Ω•) → ℍ^n(X; Ω•)`. The graded piece
`σ_{≥q} Ω• / σ_{≥q+1} Ω•` is `Ω^q[-q]` (`holomorphicFormsShifted X q`), so `F^{q+1} H^n = F^q H^n`
whenever `ℍ^n(X; Ω^q[-q]) = H^{n-q}(X(ℂ), Ω^q)` vanishes. For a curve, `H^2(X(ℂ), 𝒪) = 0` then gives
`F^1 H_dR^2 = ⊤`, so every class of `H^2(X(ℂ); ℚ)` is a Hodge class, and with `Hdg^0 = ⊤` and the
vanishing of `HQ X m` above degree `2`, `CycleClassIsHodge X` follows.

Claimed: `CycleClassIsHodge X` for every integral smooth projective curve `X` over `ℂ`, as an
implication from the vanishing `H^2(X(ℂ), 𝒪) = 0`, stated precisely as
`Subsingleton ℍ^2(X; holomorphicFormsShifted X 0)` and passed as an explicit binder. The general
step (statement 1) and its iteration (statement 2) hold for every integral smooth `X`.
Unconditional: `Hdg^0(X; ℚ) = ⊤` for every integral smooth `X`.

Not claimed: the vanishing `H^2(X(ℂ), 𝒪) = 0` itself (no Dolbeault resolution or dimension
vanishing for coherent analytic sheaves is available here or upstream); anything in dimension
above one; any property of the cycle classes themselves (the argument makes every class of
`H^2(X(ℂ); ℚ)` Hodge, so it uses only that the point classes live there). No new
`@[hodge_hypothesis]`.
HC no distance; AV milestone no distance.
-/

noncomputable section
open CategoryTheory AlgebraicGeometry ComplexPoint
open scoped TensorProduct
open HodgeLean.RealDefs

namespace HodgeLean.Adapters

/-- **One step of the Hodge filtration.** If `ℍ^n(X; Ω^q[-q]) = H^{n-q}(X(ℂ), Ω^q)` vanishes, then
`F^{q+1} H_dR^n(X) = F^q H_dR^n(X)`. The degreewise split short exact sequence
`0 → σ_{≥q+1} Ω• → σ_{≥q} Ω• → Ω^q[-q] → 0` gives a distinguished triangle, hence the exact sequence
`ℍ^n(σ_{≥q+1}) → ℍ^n(σ_{≥q}) → ℍ^n(Ω^q[-q])`; its first map is onto, and both filtration steps are
images in `ℍ^n(Ω•)` of maps compatible with it.
Source: Voisin, *Hodge Theory and Complex Algebraic Geometry I*, Cambridge Stud. Adv. Math. 76,
§8.3.1 (the Hodge filtration on hypercohomology and its graded pieces `Ω^q[-q]`) and §8.1.2 (the
long exact sequence of hypercohomology of a short exact sequence of complexes); Mathlib's
`HomologicalComplex.ShortExact` and `Pretriangulated.Triangle.coyoneda_exact₂`. -/
theorem spec_hodgeFiltration_succ_eq_of_subsingleton (X : Over (Spec ↧ℂ)) [IsIntegral X.left]
    [Smooth X.hom] (q n : ℤ) (h : Subsingleton ℍ^n(X; holomorphicFormsShifted X q)) :
    F^(q + 1) H_dR^n(X) = F^q H_dR^n(X) :=
  spec_hodgeFiltration_succ_eq_of_subsingleton_aux X q n h

example (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom]
    (h : Subsingleton ℍ^2(X; holomorphicFormsShifted X 0)) :
    F^(0 + 1) H_dR^2(X) = F^0 H_dR^2(X) :=
  spec_hodgeFiltration_succ_eq_of_subsingleton X 0 2 h

/-- **`F^p H_dR^n = ⊤` from vanishing below `p`.** If `H^{n-q}(X(ℂ), Ω^q) = 0` for every
`0 ≤ q < p`, then `F^p H_dR^n(X) = ⊤`. On an `X` of dimension `d` the hypothesis is expected for
`n ≥ d + p` (then `n - q > d`), which is the range "`n - p ≥ d`"; that dimension vanishing is not
available here. At `p = 0` there is no hypothesis and this is `hodgeFiltration_eq_top_of_nonpos`.
Source: Voisin, *Hodge Theory and Complex Algebraic Geometry I*, §8.3.1; induction on
`spec_hodgeFiltration_succ_eq_of_subsingleton` from `F^0 = ⊤`. -/
theorem spec_hodgeFiltration_eq_top_of_subsingleton (X : Over (Spec ↧ℂ)) [IsIntegral X.left]
    [Smooth X.hom] (p : ℕ) (n : ℤ)
    (h : ∀ q : ℕ, q < p → Subsingleton ℍ^n(X; holomorphicFormsShifted X q)) :
    F^(p : ℤ) H_dR^n(X) = ⊤ :=
  spec_hodgeFiltration_eq_top_of_subsingleton_aux X p n h

/-- For a curve, `F^1 H_dR^2(X) = ⊤` from `H^2(X(ℂ), 𝒪) = 0`. -/
example (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom]
    (h𝒪 : Subsingleton ℍ^2(X; holomorphicFormsShifted X 0)) :
    F^((1 : ℕ) : ℤ) H_dR^2(X) = ⊤ :=
  spec_hodgeFiltration_eq_top_of_subsingleton X 1 2 fun q hq => by
    obtain rfl : q = 0 := by omega
    exact h𝒪

/-- **Every class is Hodge when `F^p` is everything.** If `F^p H_dR^{2p}(X) = ⊤`, then the
conjugate filtration is `⊤` too (it is a preimage of `F^p` under conjugation), so
`hodgePiece X p p (2p) = ⊤` and `Hdg^p(X; ℚ) = ⊤`.
Source: Voisin, *Hodge Theory and Complex Algebraic Geometry I*, §7.1.1 (Hodge classes as rational
classes in `F^p ∩ conj F^p`); upstream `hodgeClasses`. -/
theorem spec_hodgeClasses_eq_top_of_hodgeFiltration (X : Over (Spec ↧ℂ)) [IsIntegral X.left]
    [Smooth X.hom] (p : ℕ) (h : F^(p : ℤ) H_dR^((2 * p : ℕ) : ℤ)(X) = ⊤) :
    Hdg^p(X; ℚ) = ⊤ :=
  spec_hodgeClasses_eq_top_of_hodgeFiltration_aux X p h

example (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom]
    (h : F^((1 : ℕ) : ℤ) H_dR^((2 * 1 : ℕ) : ℤ)(X) = ⊤) :
    Hdg^1(X; ℚ) = ⊤ :=
  spec_hodgeClasses_eq_top_of_hodgeFiltration X 1 h

/-- **Every degree-zero class is Hodge**, unconditionally: `F^0 = ⊤`.
Source: Voisin, *Hodge Theory and Complex Algebraic Geometry I*, §7.1.1; here
`hodgeFiltration_eq_top_of_nonpos` (`RealDefs/Filtration.lean`) and
`spec_hodgeClasses_eq_top_of_hodgeFiltration`. -/
theorem spec_hodgeClasses_zero_eq_top (X : Over (Spec ↧ℂ)) [IsIntegral X.left]
    [Smooth X.hom] :
    Hdg^0(X; ℚ) = ⊤ :=
  spec_hodgeClasses_zero_eq_top_aux X

/-- The degree-zero part of `CycleClassIsHodge`, for every integral smooth projective `X`. -/
example (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] :
    algebraicCycleClassSpan X 0 ≤ Hdg^0(X; ℚ) := by
  rw [spec_hodgeClasses_zero_eq_top X]
  exact le_top

/-- **Cycle classes in a vanishing degree are Hodge.** If `HQ X (2p)` is a subsingleton, the span
of codimension-`p` cycle classes lies in `Hdg^p(X; ℚ)` (both are `⊥` or `⊤` of the zero space).
Source: elementary; with `j5d_subsingleton_HQ_of_lt` (`RealDefs/TopDegreeRank.lean`) it covers
`2p > 2 dim X`. -/
theorem spec_algebraicCycleClassSpan_le_hodgeClasses_of_subsingleton (X : Over (Spec ↧ℂ))
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] (p : ℕ)
    (h : Subsingleton (HQ X (2 * p))) :
    algebraicCycleClassSpan X p ≤ Hdg^p(X; ℚ) :=
  spec_algebraicCycleClassSpan_le_hodgeClasses_of_subsingleton_aux X p h

example (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom]
    [SmoothOfRelativeDimension 1 X.hom] [IsProjective X.hom] :
    algebraicCycleClassSpan X 2 ≤ Hdg^2(X; ℚ) :=
  spec_algebraicCycleClassSpan_le_hodgeClasses_of_subsingleton X 2
    (j5d_subsingleton_HQ_of_lt X 1 (by norm_num))

/-- **The class of a point of a curve is of type `(1, 1)`**, as an implication from
`H^2(X(ℂ), 𝒪) = 0`: for `x` of coheight one, `1 ⊗ [x]` lies in `cohomologyHodgePiece X 2 (1, 1)`.
The vanishing is the curve input; the statement is written for any integral smooth projective `X`,
where it is the same implication.
Source: Voisin, *Hodge Theory and Complex Algebraic Geometry I*, §11.1.2–11.1.3 (cycle classes are
of type `(p, p)`); Griffiths–Harris, *Principles of Algebraic Geometry*, Ch. 0 §2–3 (Dolbeault:
`H^2(X, 𝒪) ≅ H^{0,2}_{∂̄}(X) = 0` on a Riemann surface); here statements 2–3 and
`mem_hodgeClasses_iff_tmul_mem` (`RealDefs/CupFiltered.lean`). -/
theorem spec_pointClass_mem_cohomologyHodgePiece (X : Over (Spec ↧ℂ)) [IsIntegral X.left]
    [Smooth X.hom] [IsProjective X.hom]
    (h𝒪 : Subsingleton ℍ^2(X; holomorphicFormsShifted X 0))
    (x : X.left) (hx : Order.coheight x = 1) :
    (1 : ℂ) ⊗ₜ[ℚ] (cycleComponentSheafClass X x hx : HQ X 2) ∈
      cohomologyHodgePiece X 2 ((1 : ℤ), (1 : ℤ)) :=
  spec_pointClass_mem_cohomologyHodgePiece_aux X h𝒪 x hx

/-- **`CycleClassIsHodge` for curves**, as an implication from `H^2(X(ℂ), 𝒪) = 0`. For an integral
smooth projective curve `X` over `ℂ`: codimension `0` by `spec_hodgeClasses_zero_eq_top`,
codimension `1` by `F^1 H_dR^2 = ⊤`, codimension `p ≥ 2` because `HQ X (2p) = 0`
(`j5d_subsingleton_HQ_of_lt`).
Source: Voisin, *Hodge Theory and Complex Algebraic Geometry I*, §§11.1.2–11.1.3; Griffiths–Harris,
*Principles of Algebraic Geometry*, Ch. 0 §2–3. -/
theorem spec_cycleClassIsHodge_of_curve (X : Over (Spec ↧ℂ)) [IsIntegral X.left]
    [Smooth X.hom] [SmoothOfRelativeDimension 1 X.hom] [IsProjective X.hom]
    (h𝒪 : Subsingleton ℍ^2(X; holomorphicFormsShifted X 0)) :
    CycleClassIsHodge X :=
  spec_cycleClassIsHodge_of_curve_aux X h𝒪

/-- On a curve, with the vanishing, every degree-two class is Hodge and the codimension-one cycle
classes span them (`j5d_algebraicCycleClassSpan_one_eq_top`). -/
example (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom]
    [SmoothOfRelativeDimension 1 X.hom] [IsProjective X.hom]
    (h𝒪 : Subsingleton ℍ^2(X; holomorphicFormsShifted X 0)) :
    algebraicCycleClassSpan X 1 = Hdg^1(X; ℚ) :=
  le_antisymm ((spec_cycleClassIsHodge_of_curve X h𝒪).le 1)
    ((j5d_algebraicCycleClassSpan_one_eq_top HodgeLean.Adapters.complexPointsPreconnected X).symm
      ▸ le_top)

/-- **Falsification check: `F^1 = ⊤` is not automatic.** Under the Betti–de Rham comparison,
`H_dR^0(X) ≠ 0` (it contains the image of `1 ⊗ 1`), while `F^1 H_dR^0(X) = 0`
(`hodgeFiltration_eq_bot_of_lt`). So `F^1 H_dR^0(X) ≠ ⊤`.
Source: Voisin, *Hodge Theory and Complex Algebraic Geometry I*, §7.1.1 (`F^1 H^0 = H^{1,-1} ⊕ ⋯ = 0`);
`unitClass_ne_zero'` (`RealDefs/FundamentalClassUnit.lean`). -/
theorem spec_hodgeFiltration_one_zero_ne_top (X : Over (Spec ↧ℂ)) [IsIntegral X.left]
    [Smooth X.hom] [IsProjective X.hom] (hB : BettiDeRhamIso X) :
    F^1 H_dR^((0 : ℕ) : ℤ)(X) ≠ ⊤ :=
  spec_hodgeFiltration_one_zero_ne_top_aux X hB

/-- **Falsification check: the vanishing hypothesis is a real condition.** Under the Betti–de Rham
comparison, `ℍ^0(X; 𝒪[0]) = H^0(X(ℂ), 𝒪) ≠ 0` (it contains the constants), so the hypothesis of
statement 2 fails in degree `0`, as it must by the previous statement.
Source: Griffiths–Harris, *Principles of Algebraic Geometry*, Ch. 0 §2 (constant functions are
holomorphic); here `spec_hodgeFiltration_eq_top_of_subsingleton` and
`spec_hodgeFiltration_one_zero_ne_top`. -/
theorem spec_not_subsingleton_hypercohomology_zero (X : Over (Spec ↧ℂ)) [IsIntegral X.left]
    [Smooth X.hom] [IsProjective X.hom] (hB : BettiDeRhamIso X) :
    ¬ Subsingleton ℍ^((0 : ℕ) : ℤ)(X; holomorphicFormsShifted X 0) :=
  spec_not_subsingleton_hypercohomology_zero_aux X hB

example (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    (hB : BettiDeRhamIso X) :
    Nontrivial ℍ^((0 : ℕ) : ℤ)(X; holomorphicFormsShifted X 0) :=
  not_subsingleton_iff_nontrivial.mp (spec_not_subsingleton_hypercohomology_zero X hB)

end HodgeLean.Adapters
