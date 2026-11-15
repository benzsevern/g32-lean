import HodgeLean.Adapters.HolomorphicPeriodsOnXProofs

/-! # Integrals of holomorphic `1`-forms along paths in `X(ℂ)`: frozen specification

Inputs stage 4h, the next stage of step 4 of the route to `F^1_B ≤ complexHolomorphicH1 X`
(`docs/specs/HolomorphicPeriodsOnX.md`). Stage 4g computed the integral of `exp^*θ` along segments
of `ℂ^g`, and froze step 5 as an implication from a period formula stated with those segment
integrals. This stage moves the integral to `X(ℂ)`: a global holomorphic `1`-form `θ` is
integrated along a continuous path `γ` of `X(ℂ)` by lifting `γ` along the uniformization
`exp : ℂ^d → X(ℂ)` and evaluating the primitive `v ↦ exp^*θ(0) v` of `exp^*θ` at the ends of the
lift (`holomorphicPathIntegral`).

Claimed:
* for abelian `X`: `exp` is a covering map, so every path of `X(ℂ)` lifts;
* for commutative `X`: two lifts of the same path have the same displacement, so the chosen
  displacement `expLiftDisplacement` is that of any lift;
* for abelian `X`: the integral along `exp ∘ [a, b]` is Mathlib's curve integral of `exp^*θ` along
  `[a, b]`; the integral is additive under concatenation of paths and invariant under homotopy
  rel endpoints;
* for abelian `X`: the lift of the S12 loop through `λ ∈ Λ` has displacement `λ`, and the integral
  of `θ` along it is the curve integral of `exp^*θ` along `[0, λ]`;
* for abelian `X`: the implication from the step-4 period formula stated with integrals along the
  S12 loops of `X(ℂ)` (an explicit binder, with a universal constant `c`) to the period formula
  that stage 4g's step 5 consumes, with exactly that type.

Not claimed: either period formula itself, any comparison between upstream's hypercohomology class
of a form and a singular cocycle, the singular cocycle `σ ↦ ∫_σ θ`, or integrals of forms that are
not global holomorphic `1`-forms.
HC no distance; AV milestone no distance.
-/

noncomputable section
open CategoryTheory AlgebraicGeometry ComplexPoint TopologicalSpace Opposite
open HodgeLean.RealDefs HodgeLean.Foundations
open scoped TensorProduct

namespace HodgeLean.Adapters

/-- For abelian `X`, the uniformization `exp : ℂ^d → X(ℂ)` is a covering map.
Source: Birkenhake–Lange, *Complex Abelian Varieties*, 2nd ed., §1.1 (`X(ℂ) = ℂ^g/Λ`); Mumford,
*Abelian Varieties*, §1; S12 `isOpenMap_complexExponential`, `surjective_complexExponential` and
`discrete_complexExponentialLattice`, with Mathlib's
`Topology.IsQuotientMap.isAddQuotientCoveringMap_of_isDiscrete_ker_addMonoidHom`. -/
theorem spec_isCoveringMap_complexExponential (X : Over (Spec ↧ℂ)) (d : ℕ) [GrpObj X]
    [IsCommMonObj X] [SmoothOfRelativeDimension d X.hom] [IsIntegral X.left]
    [IsProjective X.hom] :
    IsCoveringMap (fun v : Fin d → ℂ ↦ (complexExponential X d v).toMul) :=
  spec_isCoveringMap_complexExponential_aux X d

example (X : Over (Spec ↧ℂ)) (d : ℕ) [GrpObj X] [IsCommMonObj X]
    [SmoothOfRelativeDimension d X.hom] [IsIntegral X.left] [IsProjective X.hom]
    (γ : C(unitInterval, ComplexPoint X)) (v : Fin d → ℂ)
    (hv : (complexExponential X d v).toMul = γ 0) :
    ∃ Γ, IsExpLift X d γ Γ ∧ Γ 0 = v := by
  obtain ⟨Γ, hΓ, h0⟩ :=
    (spec_isCoveringMap_complexExponential X d).exists_path_lifts γ v hv.symm
  exact ⟨Γ, fun t ↦ congrFun hΓ t, h0⟩

/-- For commutative `X`, two lifts of the same path of `X(ℂ)` along `exp` have the same
displacement: they differ by a continuous map to the discrete lattice `Λ`, which is constant.
Source: Hatcher, *Algebraic Topology*, §1.3, Proposition 1.34 (uniqueness of lifts); S12
`discrete_complexExponentialLattice`. -/
theorem spec_isExpLift_sub_eq (X : Over (Spec ↧ℂ)) (d : ℕ) [GrpObj X] [IsCommMonObj X]
    [SmoothOfRelativeDimension d X.hom] (γ : C(unitInterval, ComplexPoint X))
    (Γ Γ' : C(unitInterval, Fin d → ℂ)) (h : IsExpLift X d γ Γ) (h' : IsExpLift X d γ Γ') :
    Γ 1 - Γ 0 = Γ' 1 - Γ' 0 :=
  spec_isExpLift_sub_eq_aux X d γ Γ Γ' h h'

example (X : Over (Spec ↧ℂ)) (d : ℕ) [GrpObj X] [IsCommMonObj X]
    [SmoothOfRelativeDimension d X.hom] (γ : C(unitInterval, ComplexPoint X))
    (Γ Γ' : C(unitInterval, Fin d → ℂ)) (h : IsExpLift X d γ Γ) (h' : IsExpLift X d γ Γ')
    (h0 : Γ 0 = Γ' 0) : Γ 1 = Γ' 1 := by
  have := spec_isExpLift_sub_eq X d γ Γ Γ' h h'
  rw [h0] at this
  exact sub_left_injective this

/-- For commutative `X`, the chosen displacement of a path of `X(ℂ)` that has a lift `Γ` is
`Γ 1 - Γ 0`.
Source: Hatcher, *Algebraic Topology*, §1.3, Proposition 1.34; `spec_isExpLift_sub_eq`. -/
theorem spec_expLiftDisplacement_eq (X : Over (Spec ↧ℂ)) (d : ℕ) [GrpObj X]
    [IsCommMonObj X] [SmoothOfRelativeDimension d X.hom] (γ : C(unitInterval, ComplexPoint X))
    (Γ : C(unitInterval, Fin d → ℂ)) (h : IsExpLift X d γ Γ) :
    expLiftDisplacement X d γ = Γ 1 - Γ 0 :=
  spec_expLiftDisplacement_eq_aux X d γ Γ h

example (X : Over (Spec ↧ℂ)) (d : ℕ) [GrpObj X] [IsCommMonObj X]
    [SmoothOfRelativeDimension d X.hom] (θ : (holomorphicDeRhamSheaf X d 1).presheaf.obj (op ⊤))
    (Γ : C(unitInterval, Fin d → ℂ)) :
    holomorphicPathIntegral X d θ (expPath X d Γ) = expPullback X d θ 0 (Γ 1 - Γ 0) := by
  rw [holomorphicPathIntegral, spec_expLiftDisplacement_eq X d _ Γ fun _ ↦ rfl]

/-- For abelian `X` and a global holomorphic `1`-form `θ`, the integral of `θ` along the path
`exp ∘ [a, b]` of `X(ℂ)` is Mathlib's curve integral of `exp^*θ` along the segment `[a, b]`.
Source: Rudin, *Real and Complex Analysis*, 3rd ed., Theorem 10.12; stage 4g
`spec_curveIntegral_segment_expPullback` and `spec_expLiftDisplacement_eq`. -/
theorem spec_holomorphicPathIntegral_expPath_segment (X : Over (Spec ↧ℂ)) (d : ℕ)
    [GrpObj X] [IsCommMonObj X] [SmoothOfRelativeDimension d X.hom] [IsIntegral X.left]
    [IsProjective X.hom] (θ : (holomorphicDeRhamSheaf X d 1).presheaf.obj (op ⊤))
    (a b : Fin d → ℂ) :
    holomorphicPathIntegral X d θ (expPath X d (Path.segment a b).toContinuousMap) =
      ∫ᶜ x in Path.segment a b, expPullback X d θ x :=
  spec_holomorphicPathIntegral_expPath_segment_aux X d θ a b

example (X : Over (Spec ↧ℂ)) (d : ℕ) [GrpObj X] [IsCommMonObj X]
    [SmoothOfRelativeDimension d X.hom] [IsIntegral X.left] [IsProjective X.hom]
    (θ : (holomorphicDeRhamSheaf X d 1).presheaf.obj (op ⊤)) (a b : Fin d → ℂ) :
    holomorphicPathIntegral X d θ (expPath X d (Path.segment a b).toContinuousMap) =
      expPullback X d θ 0 (b - a) := by
  rw [spec_holomorphicPathIntegral_expPath_segment, spec_curveIntegral_segment_expPullback]

/-- For abelian `X`, the integral of a global holomorphic `1`-form along a concatenation of paths
of `X(ℂ)` is the sum of the integrals.
Source: Rudin, *Real and Complex Analysis*, 3rd ed., §10.38; Mathlib's
`IsCoveringMap.liftPath_trans`, through `spec_isCoveringMap_complexExponential`. -/
theorem spec_holomorphicPathIntegral_trans (X : Over (Spec ↧ℂ)) (d : ℕ) [GrpObj X]
    [IsCommMonObj X] [SmoothOfRelativeDimension d X.hom] [IsIntegral X.left]
    [IsProjective X.hom] (θ : (holomorphicDeRhamSheaf X d 1).presheaf.obj (op ⊤))
    {x y z : ComplexPoint X} (γ : Path x y) (γ' : Path y z) :
    holomorphicPathIntegral X d θ (γ.trans γ').toContinuousMap =
      holomorphicPathIntegral X d θ γ.toContinuousMap +
        holomorphicPathIntegral X d θ γ'.toContinuousMap :=
  spec_holomorphicPathIntegral_trans_aux X d θ γ γ'

example (X : Over (Spec ↧ℂ)) (d : ℕ) [GrpObj X] [IsCommMonObj X]
    [SmoothOfRelativeDimension d X.hom] [IsIntegral X.left] [IsProjective X.hom]
    (θ : (holomorphicDeRhamSheaf X d 1).presheaf.obj (op ⊤)) {x y z w : ComplexPoint X}
    (γ : Path x y) (γ' : Path y z) (γ'' : Path z w) :
    holomorphicPathIntegral X d θ ((γ.trans γ').trans γ'').toContinuousMap =
      holomorphicPathIntegral X d θ γ.toContinuousMap +
        holomorphicPathIntegral X d θ γ'.toContinuousMap +
          holomorphicPathIntegral X d θ γ''.toContinuousMap := by
  rw [spec_holomorphicPathIntegral_trans, spec_holomorphicPathIntegral_trans]

/-- For abelian `X`, the integral of a global holomorphic `1`-form along a path of `X(ℂ)` depends
only on the homotopy class of the path rel endpoints.
Source: Rudin, *Real and Complex Analysis*, 3rd ed., Theorem 10.40 (homotopy invariance of
integrals of closed forms); Hatcher, *Algebraic Topology*, §1.3, Proposition 1.30; Mathlib's
`IsCoveringMap.liftPath_apply_one_eq_of_homotopicRel`. -/
theorem spec_holomorphicPathIntegral_eq_of_homotopic (X : Over (Spec ↧ℂ)) (d : ℕ)
    [GrpObj X] [IsCommMonObj X] [SmoothOfRelativeDimension d X.hom] [IsIntegral X.left]
    [IsProjective X.hom] (θ : (holomorphicDeRhamSheaf X d 1).presheaf.obj (op ⊤))
    {x y : ComplexPoint X} (γ₀ γ₁ : Path x y) (h : γ₀.Homotopic γ₁) :
    holomorphicPathIntegral X d θ γ₀.toContinuousMap =
      holomorphicPathIntegral X d θ γ₁.toContinuousMap :=
  spec_holomorphicPathIntegral_eq_of_homotopic_aux X d θ γ₀ γ₁ h

example (X : Over (Spec ↧ℂ)) (d : ℕ) [GrpObj X] [IsCommMonObj X]
    [SmoothOfRelativeDimension d X.hom] [IsIntegral X.left] [IsProjective X.hom]
    (θ : (holomorphicDeRhamSheaf X d 1).presheaf.obj (op ⊤)) {x y : ComplexPoint X}
    (γ₀ γ₁ : Path x y) (h : γ₀.Homotopic γ₁) :
    holomorphicPathIntegral X d θ γ₀.toContinuousMap -
      holomorphicPathIntegral X d θ γ₁.toContinuousMap = 0 := by
  rw [spec_holomorphicPathIntegral_eq_of_homotopic X d θ γ₀ γ₁ h, sub_self]

/-- For abelian `X`, the lift along `exp` of the S12 loop through a period `λ` has displacement
`λ`: the loop is `exp` of the segment `[0, λ]`.
Source: Birkenhake–Lange, *Complex Abelian Varieties*, 2nd ed., §1.1 (`π₁(ℂ^g/Λ) = Λ`); stage 4g
`spec_abelianLatticeLoop_eq_complexExponential_segment` and `spec_expLiftDisplacement_eq`. -/
theorem spec_expLiftDisplacement_abelianLatticePath (X : Over (Spec ↧ℂ)) [GrpObj X]
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] (l : abelianPeriodLattice X) :
    expLiftDisplacement X (dim X.left) (abelianLatticePath X l) = l :=
  spec_expLiftDisplacement_abelianLatticePath_aux X l

example (X : Over (Spec ↧ℂ)) [GrpObj X] [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    (l l' : abelianPeriodLattice X)
    (h : expLiftDisplacement X (dim X.left) (abelianLatticePath X l) =
      expLiftDisplacement X (dim X.left) (abelianLatticePath X l')) : l = l' := by
  rw [spec_expLiftDisplacement_abelianLatticePath, spec_expLiftDisplacement_abelianLatticePath]
    at h
  exact Subtype.ext h

/-- For abelian `X` and a global holomorphic `1`-form `θ`, the integral of `θ` along the S12 loop
through `λ` is the curve integral of `exp^*θ` along the segment `[0, λ]`.
Source: Birkenhake–Lange, *Complex Abelian Varieties*, 2nd ed., §1.1 and Lemma 1.3.1;
`spec_expLiftDisplacement_abelianLatticePath` and stage 4g
`spec_curveIntegral_segment_expPullback`. -/
theorem spec_holomorphicPathIntegral_abelianLatticePath (X : Over (Spec ↧ℂ)) [GrpObj X]
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    (θ : (holomorphicDeRhamSheaf X (dim X.left) 1).presheaf.obj (op ⊤))
    (l : abelianPeriodLattice X) :
    holomorphicPathIntegral X (dim X.left) θ (abelianLatticePath X l) =
      ∫ᶜ x in Path.segment 0 (l : Fin (dim X.left) → ℂ), expPullback X (dim X.left) θ x :=
  spec_holomorphicPathIntegral_abelianLatticePath_aux X θ l

example (X : Over (Spec ↧ℂ)) [GrpObj X] [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    (θ : (holomorphicDeRhamSheaf X (dim X.left) 1).presheaf.obj (op ⊤)) :
    holomorphicPathIntegral X (dim X.left) θ (abelianLatticePath X 0) = 0 := by
  rw [spec_holomorphicPathIntegral_abelianLatticePath, ZeroMemClass.coe_zero,
    curveIntegral_segment]
  simp

/-- **The step-4 period formula on `X(ℂ)` gives the one stage 4g's step 5 consumes.** For abelian
`X`, if for some universal constant `c` the Betti period along the S12 loop through `λ` of every
rational-coefficient class `ω` whose de Rham image is the class of a closed global holomorphic
`1`-form `θ` is `c` times the integral of `θ` along that loop, then the same holds with the curve
integral of `exp^*θ` along `[0, λ]` in place of the loop integral. The conclusion has exactly the
type of the binder `hper` of `spec_comap_hodgeFiltration_one_le_of_periods`.
Source: Birkenhake–Lange, *Complex Abelian Varieties*, 2nd ed., §1.1 and §1.4;
`spec_holomorphicPathIntegral_abelianLatticePath`. -/
theorem spec_periods_of_holomorphicPathIntegral (X : Over (Spec ↧ℂ)) [GrpObj X]
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] (c : ℂ)
    (hloop : ∀ (z : (filteredGlobalSections X).cycles ((1 : ℕ) : ℤ)) (ω : ℂ ⊗[ℚ] HQ X 1),
      bettiDeRhamHQ X 1 ω = cycleDeRhamClass X z → ∀ l : abelianPeriodLattice X,
        complexAbelianPeriod X ω l =
          c * holomorphicPathIntegral X (dim X.left) (cycleOneForm X z) (abelianLatticePath X l)) :
    ∀ (z : (filteredGlobalSections X).cycles ((1 : ℕ) : ℤ)) (ω : ℂ ⊗[ℚ] HQ X 1),
      bettiDeRhamHQ X 1 ω = cycleDeRhamClass X z → ∀ l : abelianPeriodLattice X,
        complexAbelianPeriod X ω l = c * ∫ᶜ x in Path.segment 0 (l : Fin (dim X.left) → ℂ),
          expPullback X (dim X.left) (cycleOneForm X z) x :=
  spec_periods_of_holomorphicPathIntegral_aux X c hloop

example (X : Over (Spec ↧ℂ)) [GrpObj X] [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    (c : ℂ)
    (hloop : ∀ (z : (filteredGlobalSections X).cycles ((1 : ℕ) : ℤ)) (ω : ℂ ⊗[ℚ] HQ X 1),
      bettiDeRhamHQ X 1 ω = cycleDeRhamClass X z → ∀ l : abelianPeriodLattice X,
        complexAbelianPeriod X ω l =
          c * holomorphicPathIntegral X (dim X.left) (cycleOneForm X z) (abelianLatticePath X l)) :
    (F^1 H_dR^((1 : ℕ) : ℤ)(X)).comap (bettiDeRhamHQ X 1) ≤ complexHolomorphicH1 X :=
  spec_comap_hodgeFiltration_one_le_of_periods X c
    (spec_periods_of_holomorphicPathIntegral X c hloop)

end HodgeLean.Adapters
