import HodgeLean.Adapters.HolomorphicPeriodsProofs

/-! # Periods of holomorphic `1`-forms as curve integrals: frozen specification

Inputs stage 4g, the first stages of step 4 of the route to `F^1_B ≤ complexHolomorphicH1 X`
(`docs/specs/HolomorphicPeriods.md`). Stage 4f proves that a global holomorphic `1`-form `θ` on an
abelian `X` pulls back along `exp : ℂ^g → X(ℂ)` to a constant covector `a = exp^*θ(0)`. Step 4 is
a degree-one de Rham comparison: the Betti period of `β⁻¹([θ])` along the S12 loop of `λ ∈ Λ` is
(up to a universal constant) the curve integral of `exp^*θ` along the segment `[0, λ]`. This stage
freezes the pieces of that comparison on the `ℂ^g` side, and step 5 as an implication from it.

Claimed:
* for abelian `X`: the S12 loop `abelianLatticeLoop X λ` is `exp` of Mathlib's segment path
  `Path.segment 0 λ`, on `[0, 1]`;
* for holomorphic `f` on a complex normed space: the curve integral of the exact form `df` along a
  segment `[a, b]` is `f b - f a` (so exact forms have zero periods along closed segments, and
  adding `df` with `f b = f a` does not change the integral along `[a, b]`);
* for abelian `X`: the curve integral of `exp^*θ` along `[a, b]` is `exp^*θ(0)(b - a)`, so along
  `[0, λ]` it is `∑ aᵢ λᵢ`;
* falsification: the real `1`-form `x dy` on `ℂ` is not closed, and its integrals along two
  homotopic paths with the same endpoints differ, so closedness is needed for the periods of a form
  to depend only on the homotopy class of the loop;
* for abelian `X`: the implication from the step-4 period formula (an explicit binder, with a
  universal constant `c`) to `F^1_B ≤ complexHolomorphicH1 X`. This is step 5.

Not claimed: the step-4 period formula itself, any comparison between upstream's hypercohomology
class of a form and a singular cocycle, integration of forms along paths in `X(ℂ)`, or homotopy
invariance of curve integrals beyond what Mathlib proves on normed spaces.
HC no distance; AV milestone no distance.
-/

noncomputable section
open CategoryTheory AlgebraicGeometry ComplexPoint TopologicalSpace Opposite
open HodgeLean.RealDefs HodgeLean.Foundations
open scoped TensorProduct

namespace HodgeLean.Adapters

/-- For abelian `X`, the S12 loop through a period `λ` is `exp` of the segment `[0, λ]`:
`abelianLatticeLoop X λ t = exp (t • λ)` for `t ∈ [0, 1]`.
Source: Birkenhake–Lange, *Complex Abelian Varieties*, 2nd ed., §1.1 (`H₁(ℂ^g/Λ, ℤ) = Λ` through
the images of the segments `[0, λ]`); S11 `oneParameterSubgroup_smul`. -/
theorem spec_abelianLatticeLoop_eq_complexExponential_segment (X : Over (Spec ↧ℂ)) [GrpObj X]
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] (l : abelianPeriodLattice X)
    (t : unitInterval) :
    abelianLatticeLoop X l ((t : ℝ) : UnitAddCircle) =
      (complexExponential X (dim X.left)
        (Path.segment (0 : Fin (dim X.left) → ℂ) (l : Fin (dim X.left) → ℂ) t)).toMul :=
  spec_abelianLatticeLoop_eq_complexExponential_segment_aux X l t

example (X : Over (Spec ↧ℂ)) [GrpObj X] [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    (l : abelianPeriodLattice X) :
    abelianLatticeLoop X l ((1 : ℝ) : UnitAddCircle) =
      (complexExponential X (dim X.left) (l : Fin (dim X.left) → ℂ)).toMul := by
  have h := spec_abelianLatticeLoop_eq_complexExponential_segment X l 1
  rwa [Path.target] at h

/-- The fundamental theorem of calculus for curve integrals along segments: the integral of the
exact form `df` of a `C¹` holomorphic `f` along `[a, b]` is `f b - f a`.
Source: Rudin, *Real and Complex Analysis*, 3rd ed., Theorem 10.12 (the integral of a derivative
along a path), applied to `t ↦ f (a + t • (b - a))`; Mathlib's `curveIntegral_segment` and
`intervalIntegral.integral_eq_sub_of_hasDerivAt`. -/
theorem spec_curveIntegral_segment_fderiv {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F] (f : E → F)
    (hf : ContDiff ℂ 1 f) (a b : E) :
    ∫ᶜ x in Path.segment a b, fderiv ℂ f x = f b - f a :=
  spec_curveIntegral_segment_fderiv_aux f hf a b

example {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup F]
    [NormedSpace ℂ F] [CompleteSpace F] (f : E → F) (hf : ContDiff ℂ 1 f) (a : E) :
    ∫ᶜ x in Path.segment a a, fderiv ℂ f x = 0 := by
  rw [spec_curveIntegral_segment_fderiv f hf a a, sub_self]

/-- Adding an exact form `df` with `f b = f a` does not change the curve integral of a continuous
form along `[a, b]`. For `b = a + λ` and a `Λ`-periodic `f` this says that forms on `ℂ^g` which
differ by `d` of a periodic function have the same lattice periods.
Source: Rudin, *Real and Complex Analysis*, 3rd ed., Theorem 10.12; Mathlib's
`curveIntegral_fun_add`, through `spec_curveIntegral_segment_fderiv`. -/
theorem spec_curveIntegral_segment_add_fderiv_of_eq {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
    (ω : E → E →L[ℂ] F) (hω : Continuous ω) (f : E → F) (hf : ContDiff ℂ 1 f) (a b : E)
    (hab : f b = f a) :
    ∫ᶜ x in Path.segment a b, (ω x + fderiv ℂ f x) = ∫ᶜ x in Path.segment a b, ω x :=
  spec_curveIntegral_segment_add_fderiv_of_eq_aux ω hω f hf a b hab

example {g : ℕ} (ω : (Fin g → ℂ) → (Fin g → ℂ) →L[ℂ] ℂ) (hω : Continuous ω)
    (f : (Fin g → ℂ) → ℂ) (hf : ContDiff ℂ 1 f) (l : Fin g → ℂ) (hfl : ∀ v, f (v + l) = f v) :
    ∫ᶜ x in Path.segment 0 l, (ω x + fderiv ℂ f x) = ∫ᶜ x in Path.segment 0 l, ω x :=
  spec_curveIntegral_segment_add_fderiv_of_eq ω hω f hf 0 l (by simpa using hfl 0)

/-- For abelian `X` and a global holomorphic `1`-form `θ`, the curve integral of `exp^*θ` along a
segment `[a, b]` of `ℂ^d` is `exp^*θ(0)(b - a)`: along `[0, λ]` it is `∑ aᵢ λᵢ` with
`a = exp^*θ(0)`.
Source: Birkenhake–Lange, *Complex Abelian Varieties*, 2nd ed., §1.1 and Lemma 1.3.1; stage 4f
`spec_expPullback_eq_expPullback_zero` and Mathlib's `curveIntegral_segment_const`. -/
theorem spec_curveIntegral_segment_expPullback (X : Over (Spec ↧ℂ)) (d : ℕ) [GrpObj X]
    [IsCommMonObj X] [SmoothOfRelativeDimension d X.hom] [IsIntegral X.left]
    [IsProjective X.hom] (θ : (holomorphicDeRhamSheaf X d 1).presheaf.obj (op ⊤))
    (a b : Fin d → ℂ) :
    ∫ᶜ x in Path.segment a b, expPullback X d θ x = expPullback X d θ 0 (b - a) :=
  spec_curveIntegral_segment_expPullback_aux X d θ a b

example (X : Over (Spec ↧ℂ)) (d : ℕ) [GrpObj X] [IsCommMonObj X]
    [SmoothOfRelativeDimension d X.hom] [IsIntegral X.left] [IsProjective X.hom]
    (θ : (holomorphicDeRhamSheaf X d 1).presheaf.obj (op ⊤)) (l : Fin d → ℂ) :
    ∫ᶜ x in Path.segment 0 l, expPullback X d θ x = ∑ i, expPullback X d θ 0 (Pi.single i 1) * l i := by
  rw [spec_curveIntegral_segment_expPullback X d θ 0 l, sub_zero]
  conv_lhs => rw [show l = ∑ i, l i • Pi.single i (1 : ℂ) by
    ext j; simp [Finset.sum_apply, Pi.single_apply]]
  simp [map_sum, mul_comm]

/-- Falsification check, part one: the real `1`-form `x dy` on `ℂ` is not closed; its derivative
at `0` is not symmetric (`d(x dy) = dx ∧ dy`).
Source: Spivak, *Calculus on Manifolds*, Ch. 4; Mathlib's convention that `ω` is closed iff
`fderiv ω x u v = fderiv ω x v u` (`Mathlib/MeasureTheory/Integral/CurveIntegral/Poincare.lean`). -/
theorem spec_fderiv_reDImForm_not_symmetric :
    fderiv ℝ reDImForm 0 1 Complex.I ≠ fderiv ℝ reDImForm 0 Complex.I 1 :=
  spec_fderiv_reDImForm_not_symmetric_aux

example : ¬ ∀ u v : ℂ, fderiv ℝ reDImForm 0 u v = fderiv ℝ reDImForm 0 v u :=
  fun h => spec_fderiv_reDImForm_not_symmetric (h 1 Complex.I)

/-- Falsification check, part two: the two staircase paths from `0` to `1 + i` are homotopic, but
the integrals of the non-closed form `x dy` along them are `1` and `0`. So curve integrals of a
form that is not closed are not homotopy invariant, and the closedness hypothesis of Mathlib's
`curveIntegral_add_curveIntegral_eq_of_hasFDerivWithinAt` cannot be dropped.
Source: Spivak, *Calculus on Manifolds*, Ch. 4 (Green's theorem: the difference is the area
`∫∫ dx ∧ dy = 1` of the unit square); Mathlib's `SimplyConnectedSpace.paths_homotopic`,
`curveIntegral_trans` and `curveIntegral_segment`. -/
theorem spec_curveIntegral_reDImForm_staircases :
    rightUpPath.Homotopic upRightPath ∧
      ∫ᶜ x in rightUpPath, reDImForm x = 1 ∧ ∫ᶜ x in upRightPath, reDImForm x = 0 :=
  spec_curveIntegral_reDImForm_staircases_aux

example : ∃ γ₁ γ₂ : Path (0 : ℂ) (1 + Complex.I),
    γ₁.Homotopic γ₂ ∧ ∫ᶜ x in γ₁, reDImForm x ≠ ∫ᶜ x in γ₂, reDImForm x := by
  obtain ⟨h, h₁, h₂⟩ := spec_curveIntegral_reDImForm_staircases
  exact ⟨_, _, h, by rw [h₁, h₂]; exact one_ne_zero⟩

/-- **Step 5, as an implication from step 4.** For abelian `X`, if for some universal constant `c`
the Betti period of every rational-coefficient class `ω` whose de Rham image is the class of a
closed global holomorphic `1`-form `θ` is `c` times the curve integral of `exp^*θ` along `[0, λ]`,
then `F^1_B ≤ complexHolomorphicH1 X`. The constant absorbs the orientation and normalization
conventions of the comparison (circle orientation, the rescaling in `cupComparison`, signs of
the hypercohomology identifications); any value works, because only complex linearity in `λ` is
used.
Source: Birkenhake–Lange, *Complex Abelian Varieties*, 2nd ed., §1.4 and Theorem 1.4.1; stage 4c
`spec_comap_hodgeFiltration_one_le_iff` and `spec_hodgeFiltration_one_eq_range_cycleDeRhamClass`,
with `spec_curveIntegral_segment_expPullback`. -/
theorem spec_comap_hodgeFiltration_one_le_of_periods (X : Over (Spec ↧ℂ)) [GrpObj X]
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] (c : ℂ)
    (hper : ∀ (z : (filteredGlobalSections X).cycles ((1 : ℕ) : ℤ)) (ω : ℂ ⊗[ℚ] HQ X 1),
      bettiDeRhamHQ X 1 ω = cycleDeRhamClass X z → ∀ l : abelianPeriodLattice X,
        complexAbelianPeriod X ω l = c * ∫ᶜ x in Path.segment 0 (l : Fin (dim X.left) → ℂ),
          expPullback X (dim X.left) (cycleOneForm X z) x) :
    (F^1 H_dR^((1 : ℕ) : ℤ)(X)).comap (bettiDeRhamHQ X 1) ≤ complexHolomorphicH1 X :=
  spec_comap_hodgeFiltration_one_le_of_periods_aux X c hper

example (X : Over (Spec ↧ℂ)) [GrpObj X] [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    (c : ℂ)
    (hper : ∀ (z : (filteredGlobalSections X).cycles ((1 : ℕ) : ℤ)) (ω : ℂ ⊗[ℚ] HQ X 1),
      bettiDeRhamHQ X 1 ω = cycleDeRhamClass X z → ∀ l : abelianPeriodLattice X,
        complexAbelianPeriod X ω l = c * ∫ᶜ x in Path.segment 0 (l : Fin (dim X.left) → ℂ),
          expPullback X (dim X.left) (cycleOneForm X z) x) :
    Disjoint (F^1 H_dR^((1 : ℕ) : ℤ)(X))
      (conjHodgeFiltrationComplexSubmodule X 1 ((1 : ℕ) : ℤ)) :=
  spec_disjoint_hodgeFiltration_one_of_le X
    (spec_comap_hodgeFiltration_one_le_of_periods X c hper)

end HodgeLean.Adapters
