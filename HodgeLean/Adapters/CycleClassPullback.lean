import HodgeLean.Adapters.CycleClassPullbackDefs
import HodgeLean.Adapters.CycleClassPullbackProofs

/-! # Algebraic pullback along powers sum maps (FROZEN)

This stage proves the zero-coefficient half of the powers pullback premise and records the exact
nonzero-coefficient reduction. The remaining geometric comparison is documented in
`docs/specs/CycleClassPullback.md`.
HC no distance; AV milestone no distance.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open scoped CategoryTheory.MonObj
open HodgeLean.RealDefs

namespace HodgeLean.Adapters

variable {A Y : Over (Spec ↧ℂ)} [GrpObj A] [IsCommMonObj A]
  [IsIntegral A.left] [Smooth A.hom] [IsProjective A.hom]
  [GrpObj Y] [IsCommMonObj Y] [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]
  {L : Type*} [Field L] [Algebra ℚ L] {r : ℕ}

/-- A finite component cycle realizes an algebraic cohomology class.
Source: `cycleComponentSheafClass_mem_algebraicCycleClassSpan` and linear closure. -/
theorem ccm2_ComponentCycle_class_mem {X : Over (Spec ↧ℂ)} [IsIntegral X.left]
    [Smooth X.hom] [IsProjective X.hom] {q : ℕ} (c : ccm2_ComponentCycle X q) :
    c.class ∈ algebraicCycleClassSpan X q :=
  ccm2_ComponentCycle_class_mem_aux c

/-- Component-cycle realization preserves addition.
Source: linear extension of the rational cycle-class map. -/
theorem ccm2_ComponentCycle_class_add {X : Over (Spec ↧ℂ)} [IsIntegral X.left]
    [Smooth X.hom] [IsProjective X.hom] {q : ℕ} (c d : ccm2_ComponentCycle X q) :
    (c + d).class = c.class + d.class :=
  ccm2_ComponentCycle_class_add_aux c d

/-- Component-cycle realization preserves rational scaling.
Source: linear extension of the rational cycle-class map. -/
theorem ccm2_ComponentCycle_class_smul {X : Over (Spec ↧ℂ)} [IsIntegral X.left]
    [Smooth X.hom] [IsProjective X.hom] {q : ℕ} (m : ℚ) (c : ccm2_ComponentCycle X q) :
    (m • c).class = m • c.class :=
  ccm2_ComponentCycle_class_smul_aux m c

/-- A nonzero tuple has a nonzero coordinate.
Source: extensionality for finite tuples. -/
theorem ccm2_exists_ne_zero_coordinate (θ : L →ₐ[ℚ] AbelianEnd0 A)
    (a : Fin r → pwOrder A θ) (ha : a ≠ 0) :
  ∃ i, a i ≠ 0 :=
  ccm2_exists_ne_zero_coordinate_aux θ a ha

/-- A nonzero coefficient has invertible image in the rational endomorphism algebra.
Source: a field homomorphism is injective and preserves inverses. -/
theorem ccm2_theta_isUnit_of_ne_zero (θ : L →ₐ[ℚ] AbelianEnd0 A) (b : pwOrder A θ)
    (hb : b ≠ 0) : IsUnit (θ (b : L)) :=
  ccm2_theta_isUnit_of_ne_zero_aux θ b hb

/-- The integral representative of a nonzero coefficient is an isogeny on complex points.
Source: Mumford, *Abelian Varieties*, §19, nonzero endomorphisms in a CM field. -/
theorem ccm2_pwOrderEnd_isogeny_of_ne_zero (θ : L →ₐ[ℚ] AbelianEnd0 A)
    (b : pwOrder A θ) (hb : b ≠ 0) :
    ccm2_IsogenyOnPoints (pwOrderEnd A θ b).hom :=
  ccm2_pwOrderEnd_isogeny_of_ne_zero_aux θ b hb

/-- The powers sum map restricted to one coordinate is its coefficient endomorphism.
Source: the biproduct identities in `AbelianPowerData`. -/
theorem ccm2_incl_pwSumMap (P : AbelianPowerData A Y r)
    (θ : L →ₐ[ℚ] AbelianEnd0 A) (a : Fin r → pwOrder A θ) (i : Fin r) :
    P.incl i ≫ P.pwSumMap θ a = (pwOrderEnd A θ (a i)).hom :=
  ccm2_incl_pwSumMap_aux P θ a i

/-- A powers sum map with a nonzero coefficient tuple is surjective on complex points.
Source: restriction to a nonzero coordinate and surjectivity of its isogeny. -/
theorem ccm2_pwSumMap_surjective_of_ne_zero (P : AbelianPowerData A Y r)
    (θ : L →ₐ[ℚ] AbelianEnd0 A) (a : Fin r → pwOrder A θ) (ha : a ≠ 0) :
    Function.Surjective (Point.map (P.pwSumMap θ a)) :=
  ccm2_pwSumMap_surjective_of_ne_zero_aux P θ a ha

/-- A nonzero coefficient tuple does not give the constant identity map when the target has a
complex point distinct from its identity.
Source: surjectivity of the nonzero powers sum map and the image of a constant group map. -/
theorem ccm2_pwSumMap_ne_one_of_ne_zero (P : AbelianPowerData A Y r)
    (θ : L →ₐ[ℚ] AbelianEnd0 A) (a : Fin r → pwOrder A θ) (ha : a ≠ 0)
    (hA : ∃ x : ComplexPoint A, x ≠ 1) :
    P.pwSumMap θ a ≠ 1 :=
  ccm2_pwSumMap_ne_one_of_ne_zero_aux P θ a ha hA

/-- A powers sum map with a nonzero coefficient tuple is smooth.
Source: a surjective homomorphism of complex abelian varieties is smooth. -/
theorem ccm2_pwSumMap_smooth_of_ne_zero (P : AbelianPowerData A Y r)
    (θ : L →ₐ[ℚ] AbelianEnd0 A) (a : Fin r → pwOrder A θ) (ha : a ≠ 0) :
    Smooth (P.pwSumMap θ a).left :=
  ccm2_pwSumMap_smooth_of_ne_zero_aux P θ a ha

/-- Generatorwise component-cycle pullback implies preservation of the full algebraic span.
Source: linear extension from the component generators of `algebraicCycleClassSpan`. -/
theorem ccm2_homPullback_span_of_component_cycles (f : Y ⟶ A) (q : ℕ)
    (hcomponent : ∀ (x : A.left) (hx : Order.coheight x = q),
      ∃ c : ccm2_ComponentCycle Y q,
        homPullback f (2 * q) (cycleComponentSheafClass A x hx) = c.class) :
    (algebraicCycleClassSpan A q).map (homPullback f (2 * q)) ≤
      algebraicCycleClassSpan Y q :=
  ccm2_homPullback_span_of_component_cycles_aux f q hcomponent

/-- The powers sum map for the zero coefficient tuple is the constant map to the identity.
Source: PW v0.3, proof of Theorem 4.2, definition of `f_a`; `AbelianPowerData.pwSumMap`. -/
theorem ccm2_pwSumMap_zero (P : AbelianPowerData A Y r)
    (θ : L →ₐ[ℚ] AbelianEnd0 A) : P.pwSumMap θ 0 = 1 :=
  ccm2_pwSumMap_zero_aux P θ

/-- Pullback along the constant map preserves the algebraic cycle-class span in every
codimension. In codimension zero the target span is all of cohomology; in positive codimension
the pullback vanishes.
Source: Hatcher, *Algebraic Topology*, §3.1–3.2; functoriality and the positive-degree pullback
of a constant map. -/
theorem ccm2_homPullback_one_span (q : ℕ) :
    (algebraicCycleClassSpan A q).map (homPullback (1 : Y ⟶ A) (2 * q)) ≤
      algebraicCycleClassSpan Y q :=
  ccm2_homPullback_one_span_aux q

/-- The powers pullback premise holds for the zero coefficient tuple, for every power datum and
every codimension.
Source: PW v0.3, proof of Theorem 4.2; the zero sum map factors through the identity point. -/
theorem ccm2_pwSumMap_zero_span (P : AbelianPowerData A Y r)
    (θ : L →ₐ[ℚ] AbelianEnd0 A) (q : ℕ) :
    (algebraicCycleClassSpan A q).map (homPullback (P.pwSumMap θ 0) (2 * q)) ≤
      algebraicCycleClassSpan Y q :=
  ccm2_pwSumMap_zero_span_aux P θ q

/-- In codimension zero, every powers sum map preserves the algebraic cycle-class span.
Source: the degree-zero cycle-class span is all of rational cohomology. -/
theorem ccm2_pwSumMap_codimension_zero (P : AbelianPowerData A Y r)
    (θ : L →ₐ[ℚ] AbelianEnd0 A) (a : Fin r → pwOrder A θ) :
    (algebraicCycleClassSpan A 0).map (homPullback (P.pwSumMap θ a) 0) ≤
      algebraicCycleClassSpan Y 0 :=
  ccm2_pwSumMap_codimension_zero_aux P θ a

/-- Splitting coefficient tuples into zero and nonzero reduces the full powers pullback premise
to its nonzero-coefficient part.
Source: the exhaustive cases `a = 0` and `a ≠ 0`; `ccm2_pwSumMap_zero_span`. -/
theorem ccm2_hPull_of_zero_or_nonzero (P : AbelianPowerData A Y r)
    (θ : L →ₐ[ℚ] AbelianEnd0 A)
    (hnz : ∀ (a : Fin r → pwOrder A θ), a ≠ 0 → ∀ q : ℕ,
      (algebraicCycleClassSpan A q).map (homPullback (P.pwSumMap θ a) (2 * q)) ≤
        algebraicCycleClassSpan Y q) :
    ∀ (a : Fin r → pwOrder A θ) (q : ℕ),
      (algebraicCycleClassSpan A q).map (homPullback (P.pwSumMap θ a) (2 * q)) ≤
        algebraicCycleClassSpan Y q :=
  ccm2_hPull_of_zero_or_nonzero_aux P θ hnz

/-! Degenerate and satisfiability checks. -/

example (P : AbelianPowerData A Y 0) (θ : L →ₐ[ℚ] AbelianEnd0 A)
    (a : Fin 0 → pwOrder A θ) (q : ℕ) :
    (algebraicCycleClassSpan A q).map (homPullback (P.pwSumMap θ a) (2 * q)) ≤
      algebraicCycleClassSpan Y q := by
  have ha : a = 0 := Subsingleton.elim _ _
  subst a
  exact ccm2_pwSumMap_zero_span P θ q

example (P : AbelianPowerData A Y 1) (θ : L →ₐ[ℚ] AbelianEnd0 A) :
    (algebraicCycleClassSpan A 0).map (homPullback (P.pwSumMap θ 0) 0) ≤
      algebraicCycleClassSpan Y 0 := by
  simpa using ccm2_pwSumMap_zero_span P θ 0

example (P : AbelianPowerData A Y r) (θ : L →ₐ[ℚ] AbelianEnd0 A)
    (a : Fin r → pwOrder A θ) (ha : a ≠ 0) (hA : ∃ x : ComplexPoint A, x ≠ 1) :
    P.pwSumMap θ 0 = 1 ∧ P.pwSumMap θ a ≠ 1 :=
  ⟨ccm2_pwSumMap_zero P θ, ccm2_pwSumMap_ne_one_of_ne_zero P θ a ha hA⟩

example (d q : ℕ) [SmoothOfRelativeDimension d A.hom] (hq : d < q)
    (a : HQ A (2 * q)) (ha : a ∈ algebraicCycleClassSpan A q) : a = 0 :=
  ccm1_algebraic_class_eq_zero_of_lt d q hq a ha

example (q : ℕ) (x : A.left) (hx : Order.coheight x = q) :
    ccm2_CodimensionPoint A q := ⟨x, hx⟩

example (q : ℕ) : ccm2_ComponentCycle A q := 0

example (q : ℕ) (c : ccm2_ComponentCycle A q) :
    c.class ∈ algebraicCycleClassSpan A q := ccm2_ComponentCycle_class_mem c

example (q : ℕ) (c d : ccm2_ComponentCycle A q) :
    (c + d).class = c.class + d.class := ccm2_ComponentCycle_class_add c d

example (q : ℕ) (m : ℚ) (c : ccm2_ComponentCycle A q) :
    (m • c).class = m • c.class := ccm2_ComponentCycle_class_smul m c

example (f : Y ⟶ A) (h : ccm2_IsogenyOnPoints f) :
    Function.Surjective (Point.map f) := h.2

example (θ : L →ₐ[ℚ] AbelianEnd0 A) (a : Fin r → pwOrder A θ) (ha : a ≠ 0) :
    ∃ i, a i ≠ 0 := ccm2_exists_ne_zero_coordinate θ a ha

example (θ : L →ₐ[ℚ] AbelianEnd0 A) (b : pwOrder A θ) (hb : b ≠ 0) :
    IsUnit (θ (b : L)) := ccm2_theta_isUnit_of_ne_zero θ b hb

example (θ : L →ₐ[ℚ] AbelianEnd0 A) (b : pwOrder A θ) (hb : b ≠ 0) :
    ccm2_IsogenyOnPoints (pwOrderEnd A θ b).hom :=
  ccm2_pwOrderEnd_isogeny_of_ne_zero θ b hb

example (P : AbelianPowerData A Y r) (θ : L →ₐ[ℚ] AbelianEnd0 A)
    (a : Fin r → pwOrder A θ) (i : Fin r) :
    P.incl i ≫ P.pwSumMap θ a = (pwOrderEnd A θ (a i)).hom :=
  ccm2_incl_pwSumMap P θ a i

example (P : AbelianPowerData A Y r) (θ : L →ₐ[ℚ] AbelianEnd0 A)
    (a : Fin r → pwOrder A θ) (ha : a ≠ 0) :
    Function.Surjective (Point.map (P.pwSumMap θ a)) :=
  ccm2_pwSumMap_surjective_of_ne_zero P θ a ha

example (P : AbelianPowerData A Y r) (θ : L →ₐ[ℚ] AbelianEnd0 A)
    (a : Fin r → pwOrder A θ) (ha : a ≠ 0) (hA : ∃ x : ComplexPoint A, x ≠ 1) :
    P.pwSumMap θ a ≠ 1 :=
  ccm2_pwSumMap_ne_one_of_ne_zero P θ a ha hA

example (P : AbelianPowerData A Y r) (θ : L →ₐ[ℚ] AbelianEnd0 A)
    (a : Fin r → pwOrder A θ) (ha : a ≠ 0) : Smooth (P.pwSumMap θ a).left :=
  ccm2_pwSumMap_smooth_of_ne_zero P θ a ha

example (f : Y ⟶ A) (q : ℕ)
    (hcomponent : ∀ (x : A.left) (hx : Order.coheight x = q),
      ∃ c : ccm2_ComponentCycle Y q,
        homPullback f (2 * q) (cycleComponentSheafClass A x hx) = c.class) :
    (algebraicCycleClassSpan A q).map (homPullback f (2 * q)) ≤
      algebraicCycleClassSpan Y q :=
  ccm2_homPullback_span_of_component_cycles f q hcomponent

end HodgeLean.Adapters
