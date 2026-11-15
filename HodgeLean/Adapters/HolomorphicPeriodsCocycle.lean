import HodgeLean.Adapters.HolomorphicPeriodsCocycleProofs

/-! # The integration cocycle of a holomorphic `1`-form and its periods: frozen specification

Inputs stage 4i (`docs/specs/HolomorphicPeriodsCocycle.md`), the next stage of step 4 of the
route to `F^1_B ≤ complexHolomorphicH1 X`. Stage 4h reduced step 5 to one binder `hloop`: the
Betti period of `ω` along each S12 loop is a universal constant times the integral of `θ` along
that loop. This stage builds the singular side of the de Rham comparison and replaces `hloop` by
a comparison of two classes in `H^1(X(ℂ); ℂ)`.

Claimed:
* for every simplicial set: a function on singular `n`-simplices extends to a cochain with those
  values;
* for abelian `X` and a global holomorphic `1`-form `θ`: the integrals of `θ` along the three edges
  of a singular `2`-simplex of `X(ℂ)` satisfy `∫_{02} = ∫_{01} + ∫_{12}`, so the integration
  cochain `σ ↦ ∫_σ θ` is a singular `1`-cocycle;
* for every loop `p`: the path of its singular `1`-simplex is `p` on `[0, 1]`; for abelian `X` the
  integration cochain takes the value `∫ θ` along the S12 loop on that loop's simplex;
* for every commutative ring: cohomologous `1`-cocycles agree on the simplex of a loop;
* for the circle and then every space: the rational period `loopPeriod p` of the class of a
  cocycle is a universal nonzero rational times its value on the simplex of `p`;
* for every space: complex cocycles representing the base change of a rational class have the
  same values on loop simplices as the rational representative, so the `ℂ`-linear extension of
  `loopPeriod p` is that universal rational times the value on the simplex of `p`;
* for abelian `X`: the implication from the comparison binder `hsing`, the base change of the
  rational class of `ω` equals `c` times the class of the integration cocycle of `θ` whenever
  `β ω = [θ]`, to stage 4h's `hloop` with the constant `s c` for a universal `s ≠ 0`.

Not claimed: `hsing` itself (the de Rham comparison of the class of a closed holomorphic form with
its integration cocycle, open stage 4i-b), any statement about `fieldToDeRhamCohomology` with
complex coefficients or about `singularToFieldCohomology`, the value of the universal rational `s`
(it is `±1` for the oriented `circleClass`, which is not claimed), or integration of forms that are
not global holomorphic `1`-forms.
HC no distance; AV milestone no distance.
-/

noncomputable section
open CategoryTheory AlgebraicGeometry ComplexPoint TopologicalSpace Opposite
open HodgeLean.RealDefs HodgeLean.Foundations
open scoped Simplicial TensorProduct

namespace HodgeLean.Adapters

/-- The cochain `simplexCochain R Y n f` takes the value `f σ` on the chain of a single simplex
`σ`.
Source: Hatcher, *Algebraic Topology*, §3.1 (cochains as functions on simplices); Mathlib's
`SSet.isColimitChainComplexXCofan` (the chain group is the coproduct over simplices). -/
theorem spec_simplexCochain_chainOfSimplex (R : Type) [CommRing R] (Y : SSet.{0}) (n : ℕ)
    (f : Y _⦋n⦌ → R) (σ : Y _⦋n⦌) :
    simplexCochain R Y n f (AlgebraicTopology.Simplicial.chainOfSimplex R σ) = f σ :=
  spec_simplexCochain_chainOfSimplex_aux R Y n f σ

example (X : Over (Spec ↧ℂ)) (d : ℕ) [GrpObj X] [SmoothOfRelativeDimension d X.hom]
    (θ : (holomorphicDeRhamSheaf X d 1).presheaf.obj (op ⊤))
    (σ : (TopCat.toSSet.obj (TopCat.of (ComplexPoint X))) _⦋1⦌) :
    singularIntegrationCochain X d θ (AlgebraicTopology.Simplicial.chainOfSimplex ℂ σ) =
      holomorphicPathIntegral X d θ (simplexPath σ) :=
  spec_simplexCochain_chainOfSimplex ℂ _ 1 _ σ

/-- For abelian `X`, a global holomorphic `1`-form `θ` and a singular `2`-simplex `τ` of `X(ℂ)`,
the integral of `θ` along the edge from vertex `0` to vertex `2` (the face `δ 1 τ`) is the sum of
the integrals along the edges from `0` to `1` (`δ 2 τ`) and from `1` to `2` (`δ 0 τ`).
Source: Rudin, *Real and Complex Analysis*, 3rd ed., §10.38–10.40 (integrals of closed forms
along homotopic paths); Hatcher, *Algebraic Topology*, Propositions 1.30 and 1.33 (the
contractible `|Δ²|` lifts along the covering `exp`); stage 4h
`spec_isCoveringMap_complexExponential` and `spec_expLiftDisplacement_eq`. -/
theorem spec_holomorphicPathIntegral_simplexPath_faces (X : Over (Spec ↧ℂ)) (d : ℕ)
    [GrpObj X] [IsCommMonObj X] [SmoothOfRelativeDimension d X.hom] [IsIntegral X.left]
    [IsProjective X.hom] (θ : (holomorphicDeRhamSheaf X d 1).presheaf.obj (op ⊤))
    (τ : (TopCat.toSSet.obj (TopCat.of (ComplexPoint X))) _⦋1 + 1⦌) :
    holomorphicPathIntegral X d θ (simplexPath ((TopCat.toSSet.obj _).δ 1 τ)) =
      holomorphicPathIntegral X d θ (simplexPath ((TopCat.toSSet.obj _).δ 2 τ)) +
        holomorphicPathIntegral X d θ (simplexPath ((TopCat.toSSet.obj _).δ 0 τ)) :=
  spec_holomorphicPathIntegral_simplexPath_faces_aux X d θ τ

example (X : Over (Spec ↧ℂ)) (d : ℕ) [GrpObj X] [IsCommMonObj X]
    [SmoothOfRelativeDimension d X.hom] [IsIntegral X.left] [IsProjective X.hom]
    (θ : (holomorphicDeRhamSheaf X d 1).presheaf.obj (op ⊤))
    (τ : (TopCat.toSSet.obj (TopCat.of (ComplexPoint X))) _⦋1 + 1⦌) :
    holomorphicPathIntegral X d θ (simplexPath ((TopCat.toSSet.obj _).δ 0 τ)) -
        holomorphicPathIntegral X d θ (simplexPath ((TopCat.toSSet.obj _).δ 1 τ)) +
      holomorphicPathIntegral X d θ (simplexPath ((TopCat.toSSet.obj _).δ 2 τ)) = 0 := by
  rw [spec_holomorphicPathIntegral_simplexPath_faces X d θ τ]
  ring

/-- For abelian `X` and a global holomorphic `1`-form `θ`, the integration cochain
`σ ↦ ∫_σ θ` is a singular `1`-cocycle of `X(ℂ)` with complex coefficients.
Source: Bott–Tu, *Differential Forms in Algebraic Topology*, §15 (the de Rham map to singular
cochains is a chain map); Rudin, *Real and Complex Analysis*, 3rd ed., §10.38–10.40;
`spec_holomorphicPathIntegral_simplexPath_faces` and `spec_simplexCochain_chainOfSimplex`. -/
theorem spec_coboundary_singularIntegrationCochain (X : Over (Spec ↧ℂ)) (d : ℕ)
    [GrpObj X] [IsCommMonObj X] [SmoothOfRelativeDimension d X.hom] [IsIntegral X.left]
    [IsProjective X.hom] (θ : (holomorphicDeRhamSheaf X d 1).presheaf.obj (op ⊤)) :
    AlgebraicTopology.Simplicial.coboundary ℂ 1 (singularIntegrationCochain X d θ) = 0 :=
  spec_coboundary_singularIntegrationCochain_aux X d θ

example (X : Over (Spec ↧ℂ)) (d : ℕ) [GrpObj X] [IsCommMonObj X]
    [SmoothOfRelativeDimension d X.hom] [IsIntegral X.left] [IsProjective X.hom]
    (θ : (holomorphicDeRhamSheaf X d 1).presheaf.obj (op ⊤)) :
    ∃ Ψ : AlgebraicTopology.Simplicial.Cocycle ℂ
        (TopCat.toSSet.obj (TopCat.of (ComplexPoint X))) 1,
      Ψ.1 = singularIntegrationCochain X d θ :=
  ⟨⟨_, spec_coboundary_singularIntegrationCochain X d θ⟩, rfl⟩

/-- The path of the singular `1`-simplex of a loop `p : ℝ/ℤ → T` is `t ↦ p t` on `[0, 1]`.
Source: Mathlib's `Convexity.StdSimplex.homeomorphI` (`homeomorphI.symm_apply_apply`). -/
theorem spec_simplexPath_loopSimplex {T : Type} [TopologicalSpace T]
    (p : C(UnitAddCircle, T)) :
    simplexPath (loopSimplex p) = p.comp ⟨fun t : unitInterval ↦ ((t : ℝ) : UnitAddCircle),
      (AddCircle.continuous_mk' 1).comp continuous_subtype_val⟩ :=
  spec_simplexPath_loopSimplex_aux p

example (X : Over (Spec ↧ℂ)) [GrpObj X] [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    (l : abelianPeriodLattice X) :
    simplexPath (loopSimplex (abelianLatticeLoop X l)) = abelianLatticePath X l :=
  spec_simplexPath_loopSimplex _

/-- For abelian `X`, the integration cochain of `θ` takes the value `∫ θ` along the S12 loop
through `λ` on the singular `1`-simplex of that loop.
Source: Birkenhake–Lange, *Complex Abelian Varieties*, 2nd ed., §1.1;
`spec_simplexCochain_chainOfSimplex` and `spec_simplexPath_loopSimplex`. -/
theorem spec_singularIntegrationCochain_loopSimplex (X : Over (Spec ↧ℂ)) [GrpObj X]
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    (θ : (holomorphicDeRhamSheaf X (dim X.left) 1).presheaf.obj (op ⊤))
    (l : abelianPeriodLattice X) :
    singularIntegrationCochain X (dim X.left) θ
        (AlgebraicTopology.Simplicial.chainOfSimplex ℂ (loopSimplex (abelianLatticeLoop X l))) =
      holomorphicPathIntegral X (dim X.left) θ (abelianLatticePath X l) :=
  spec_singularIntegrationCochain_loopSimplex_aux X θ l

example (X : Over (Spec ↧ℂ)) [GrpObj X] [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    (θ : (holomorphicDeRhamSheaf X (dim X.left) 1).presheaf.obj (op ⊤))
    (l : abelianPeriodLattice X) :
    singularIntegrationCochain X (dim X.left) θ
        (AlgebraicTopology.Simplicial.chainOfSimplex ℂ (loopSimplex (abelianLatticeLoop X l))) =
      ∫ᶜ x in Path.segment 0 (l : Fin (dim X.left) → ℂ), expPullback X (dim X.left) θ x := by
  rw [spec_singularIntegrationCochain_loopSimplex, spec_holomorphicPathIntegral_abelianLatticePath]

/-- Two singular `1`-cocycles with the same cohomology class take the same value on the singular
`1`-simplex of a loop: they differ by a coboundary `δη`, and `δη` vanishes on that simplex, whose
two endpoints are the same point.
Source: Hatcher, *Algebraic Topology*, §3.1 (evaluation of cohomology on cycles) and §2.A (a loop
is a singular `1`-cycle). -/
theorem spec_cocycle_loopSimplex_eq_of_cohomologyClass_eq (R : Type) [CommRing R]
    {T : Type} [TopologicalSpace T] (p : C(UnitAddCircle, T))
    (ψ ψ' : AlgebraicTopology.Simplicial.Cocycle R (TopCat.toSSet.obj (TopCat.of T)) 1)
    (h : Singular.cohomologyClass (TopCat.of T) 1 ψ =
      Singular.cohomologyClass (TopCat.of T) 1 ψ') :
    ψ.1 (AlgebraicTopology.Simplicial.chainOfSimplex R (loopSimplex p)) =
      ψ'.1 (AlgebraicTopology.Simplicial.chainOfSimplex R (loopSimplex p)) :=
  spec_cocycle_loopSimplex_eq_of_cohomologyClass_eq_aux R p ψ ψ' h

example {T : Type} [TopologicalSpace T] (p : C(UnitAddCircle, T))
    (ψ : AlgebraicTopology.Simplicial.Cocycle ℚ (TopCat.toSSet.obj (TopCat.of T)) 1)
    (h : Singular.cohomologyClass (TopCat.of T) 1 ψ = 0) :
    ψ.1 (AlgebraicTopology.Simplicial.chainOfSimplex ℚ (loopSimplex p)) = 0 := by
  have h0 := spec_cocycle_loopSimplex_eq_of_cohomologyClass_eq ℚ p ψ 0 (h.trans (map_zero _).symm)
  simpa using h0

/-- On the circle, the degree `circleDegree` of the class of a rational singular `1`-cocycle `χ`
is a universal nonzero rational `s` times the value of `χ` on the simplex of the identity loop.
Source: Hatcher, *Algebraic Topology*, §3.1 (`H^1(S^1; ℚ) = Hom(H_1(S^1), ℚ)`, one-dimensional)
and §2.A (the identity loop generates `H_1(S^1)`, detected by the winding cocycle of the covering
`ℝ → ℝ/ℤ`); S4 `span_circleClass_eq_top`. -/
theorem spec_circleDegree_cohomologyClass :
    ∃ s : ℚ, s ≠ 0 ∧ ∀ χ : AlgebraicTopology.Simplicial.Cocycle ℚ
        (TopCat.toSSet.obj (TopCat.of UnitAddCircle)) 1,
      circleDegree (Singular.cohomologyClass (TopCat.of UnitAddCircle) 1 χ) =
        s * χ.1 (AlgebraicTopology.Simplicial.chainOfSimplex ℚ
          (loopSimplex (ContinuousMap.id UnitAddCircle))) :=
  spec_circleDegree_cohomologyClass_aux

example : ∃ χ : AlgebraicTopology.Simplicial.Cocycle ℚ
    (TopCat.toSSet.obj (TopCat.of UnitAddCircle)) 1,
      Singular.cohomologyClass (TopCat.of UnitAddCircle) 1 χ = Singular.circleClass ∧
        χ.1 (AlgebraicTopology.Simplicial.chainOfSimplex ℚ
          (loopSimplex (ContinuousMap.id UnitAddCircle))) ≠ 0 := by
  obtain ⟨s, -, hs⟩ := spec_circleDegree_cohomologyClass
  obtain ⟨χ, hχ⟩ :=
    Singular.cohomologyClass_surjective (TopCat.of UnitAddCircle) 1 Singular.circleClass
  refine ⟨χ, hχ, fun h0 => ?_⟩
  have h := hs χ
  rw [hχ, h0, mul_zero, circleDegree, Module.Basis.coord_apply,
    show Singular.circleClass = circleClassBasis 0 by simp [circleClassBasis],
    Module.Basis.repr_self, Finsupp.single_eq_same] at h
  exact one_ne_zero h

/-- The rational period `loopPeriod p` of the class of a rational singular `1`-cocycle `ψ` of any
space is a universal nonzero rational `s` times the value of `ψ` on the simplex of `p`.
Source: Hatcher, *Algebraic Topology*, §3.1 and §2.A; `spec_circleDegree_cohomologyClass` and
naturality of singular cochains (`Foundations.Singular.cohomologyMap_class`). -/
theorem spec_loopPeriod_cohomologyClass :
    ∃ s : ℚ, s ≠ 0 ∧ ∀ (T : Type) [TopologicalSpace T] (p : C(UnitAddCircle, T))
        (ψ : AlgebraicTopology.Simplicial.Cocycle ℚ (TopCat.toSSet.obj (TopCat.of T)) 1),
      loopPeriod p (Singular.cohomologyClass (TopCat.of T) 1 ψ) =
        s * ψ.1 (AlgebraicTopology.Simplicial.chainOfSimplex ℚ (loopSimplex p)) :=
  spec_loopPeriod_cohomologyClass_aux

example {T : Type} [TopologicalSpace T] (p : C(UnitAddCircle, T))
    (ψ : AlgebraicTopology.Simplicial.Cocycle ℚ (TopCat.toSSet.obj (TopCat.of T)) 1) :
    loopPeriod p (Singular.cohomologyClass (TopCat.of T) 1 ψ) = 0 ↔
      ψ.1 (AlgebraicTopology.Simplicial.chainOfSimplex ℚ (loopSimplex p)) = 0 := by
  obtain ⟨s, hs0, hs⟩ := spec_loopPeriod_cohomologyClass
  rw [hs T p ψ, mul_eq_zero, or_iff_right hs0]

/-- A complex singular `1`-cocycle `Ψ` whose class is the base change of the class of a rational
cocycle `ψ` has the value of `ψ` on the simplex of every loop.
Source: Hatcher, *Algebraic Topology*, §3.1 (universal coefficients, naturality in the
coefficients); upstream `cohomologyEquivDualHomology` and the port of `qToCHomology_isBaseChange`;
`spec_cocycle_loopSimplex_eq_of_cohomologyClass_eq`. -/
theorem spec_cohomologyBaseChange_tmul_loopSimplex {T : Type} [TopologicalSpace T]
    (p : C(UnitAddCircle, T))
    (ψ : AlgebraicTopology.Simplicial.Cocycle ℚ (TopCat.toSSet.obj (TopCat.of T)) 1)
    (Ψ : AlgebraicTopology.Simplicial.Cocycle ℂ (TopCat.toSSet.obj (TopCat.of T)) 1)
    (h : Singular.cohomologyClass (TopCat.of T) 1 Ψ =
      cohomologyBaseChange (TopCat.of T) 1 (1 ⊗ₜ Singular.cohomologyClass (TopCat.of T) 1 ψ)) :
    Ψ.1 (AlgebraicTopology.Simplicial.chainOfSimplex ℂ (loopSimplex p)) =
      (ψ.1 (AlgebraicTopology.Simplicial.chainOfSimplex ℚ (loopSimplex p)) : ℂ) :=
  spec_cohomologyBaseChange_tmul_loopSimplex_aux p ψ Ψ h

example : ∃ (χ : AlgebraicTopology.Simplicial.Cocycle ℚ
      (TopCat.toSSet.obj (TopCat.of UnitAddCircle)) 1)
    (Ψ : AlgebraicTopology.Simplicial.Cocycle ℂ (TopCat.toSSet.obj (TopCat.of UnitAddCircle)) 1),
      Singular.cohomologyClass (TopCat.of UnitAddCircle) 1 χ = Singular.circleClass ∧
      Singular.cohomologyClass (TopCat.of UnitAddCircle) 1 Ψ =
        cohomologyBaseChange (TopCat.of UnitAddCircle) 1
          (1 ⊗ₜ Singular.cohomologyClass (TopCat.of UnitAddCircle) 1 χ) ∧
      Ψ.1 (AlgebraicTopology.Simplicial.chainOfSimplex ℂ
          (loopSimplex (ContinuousMap.id UnitAddCircle))) =
        (χ.1 (AlgebraicTopology.Simplicial.chainOfSimplex ℚ
          (loopSimplex (ContinuousMap.id UnitAddCircle))) : ℂ) ∧
      Ψ.1 (AlgebraicTopology.Simplicial.chainOfSimplex ℂ
          (loopSimplex (ContinuousMap.id UnitAddCircle))) ≠ 0 := by
  obtain ⟨s, -, hs⟩ := spec_circleDegree_cohomologyClass
  obtain ⟨χ, hχ⟩ :=
    Singular.cohomologyClass_surjective (TopCat.of UnitAddCircle) 1 Singular.circleClass
  obtain ⟨Ψ, hΨ⟩ := Singular.cohomologyClass_surjective (TopCat.of UnitAddCircle) 1
    (cohomologyBaseChange (TopCat.of UnitAddCircle) 1
      (1 ⊗ₜ Singular.cohomologyClass (TopCat.of UnitAddCircle) 1 χ))
  have hv := spec_cohomologyBaseChange_tmul_loopSimplex (ContinuousMap.id UnitAddCircle) χ Ψ hΨ
  refine ⟨χ, Ψ, hχ, hΨ, hv, fun h0 => ?_⟩
  rw [h0, eq_comm, Rat.cast_eq_zero] at hv
  have h := hs χ
  rw [hχ, hv, mul_zero, circleDegree, Module.Basis.coord_apply,
    show Singular.circleClass = circleClassBasis 0 by simp [circleClassBasis],
    Module.Basis.repr_self, Finsupp.single_eq_same] at h
  exact one_ne_zero h

/-- The `ℂ`-linear extension of the rational period `loopPeriod p`, evaluated on `x`, is the
universal nonzero rational `s` times the value on the simplex of `p` of any complex cocycle that
represents the base change of `x`.
Source: Hatcher, *Algebraic Topology*, §3.1 and §2.A; `spec_loopPeriod_cohomologyClass`,
`spec_cohomologyBaseChange_tmul_loopSimplex` and
`spec_cocycle_loopSimplex_eq_of_cohomologyClass_eq`. -/
theorem spec_cohomologyBaseChange_loopPeriod :
    ∃ s : ℚ, s ≠ 0 ∧ ∀ (T : Type) [TopologicalSpace T] (p : C(UnitAddCircle, T))
        (x : ℂ ⊗[ℚ] AlgebraicTopology.Singular.Cohomology ℚ (TopCat.of T) 1)
        (Ψ : AlgebraicTopology.Simplicial.Cocycle ℂ (TopCat.toSSet.obj (TopCat.of T)) 1),
      Singular.cohomologyClass (TopCat.of T) 1 Ψ = cohomologyBaseChange (TopCat.of T) 1 x →
        LinearMap.liftBaseChange ℂ (Algebra.linearMap ℚ ℂ ∘ₗ loopPeriod p) x =
          (s : ℂ) * Ψ.1 (AlgebraicTopology.Simplicial.chainOfSimplex ℂ (loopSimplex p)) :=
  spec_cohomologyBaseChange_loopPeriod_aux

example : ∃ s : ℚ, s ≠ 0 ∧
    ∃ Ψ : AlgebraicTopology.Simplicial.Cocycle ℂ (TopCat.toSSet.obj (TopCat.of UnitAddCircle)) 1,
      Singular.cohomologyClass (TopCat.of UnitAddCircle) 1 Ψ =
        cohomologyBaseChange (TopCat.of UnitAddCircle) 1 (1 ⊗ₜ Singular.circleClass) ∧
      LinearMap.liftBaseChange ℂ
          (Algebra.linearMap ℚ ℂ ∘ₗ loopPeriod (ContinuousMap.id UnitAddCircle))
          (1 ⊗ₜ Singular.circleClass) = 1 ∧
      (s : ℂ) * Ψ.1 (AlgebraicTopology.Simplicial.chainOfSimplex ℂ
          (loopSimplex (ContinuousMap.id UnitAddCircle))) = 1 := by
  obtain ⟨s, hs0, hs⟩ := spec_cohomologyBaseChange_loopPeriod
  obtain ⟨Ψ, hΨ⟩ := Singular.cohomologyClass_surjective (TopCat.of UnitAddCircle) 1
    (cohomologyBaseChange (TopCat.of UnitAddCircle) 1 (1 ⊗ₜ Singular.circleClass))
  have h1 : LinearMap.liftBaseChange ℂ
      (Algebra.linearMap ℚ ℂ ∘ₗ loopPeriod (ContinuousMap.id UnitAddCircle))
      (1 ⊗ₜ Singular.circleClass) = 1 := by
    rw [LinearMap.liftBaseChange_tmul, LinearMap.comp_apply, loopPeriod_id_circleClass]
    simp
  exact ⟨s, hs0, Ψ, hΨ, h1, (hs UnitAddCircle _ _ Ψ hΨ).symm.trans h1⟩

/-- **Stage 4h's `hloop` from a comparison of classes in `H^1(X(ℂ); ℂ)`.** For abelian `X`, if for
some constant `c` the base change to complex coefficients of the singular class of every `ω` (through
`cupComparison`) is `c` times the class of the integration cocycle of `θ` whenever the de Rham image
of `ω` is the class of the closed global holomorphic `1`-form `θ`, then there is a universal `s ≠ 0`
such that the period formula `hloop` of stage 4h's `spec_periods_of_holomorphicPathIntegral` holds
with the constant `s c`; the conclusion after `∃ s, s ≠ 0 ∧` has exactly the type of `hloop`.
Source: Birkenhake–Lange, *Complex Abelian Varieties*, 2nd ed., §1.1 and §1.4; Bott–Tu,
*Differential Forms in Algebraic Topology*, §15 (de Rham theorem);
`spec_cohomologyBaseChange_loopPeriod` and `spec_singularIntegrationCochain_loopSimplex`. -/
theorem spec_periods_of_cohomologyBaseChange (X : Over (Spec ↧ℂ)) [GrpObj X]
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] (c : ℂ)
    (hsing : ∀ (z : (filteredGlobalSections X).cycles ((1 : ℕ) : ℤ)) (ω : ℂ ⊗[ℚ] HQ X 1),
      bettiDeRhamHQ X 1 ω = cycleDeRhamClass X z →
        ∀ Ψ : AlgebraicTopology.Simplicial.Cocycle ℂ
            (TopCat.toSSet.obj (TopCat.of (ComplexPoint X))) 1,
          Ψ.1 = singularIntegrationCochain X (dim X.left) (cycleOneForm X z) →
            cohomologyBaseChange (TopCat.of (ComplexPoint X)) 1
                (LinearMap.baseChange ℂ (cupComparison X 1).toLinearMap ω) =
              c • Singular.cohomologyClass (TopCat.of (ComplexPoint X)) 1 Ψ) :
    ∃ s : ℂ, s ≠ 0 ∧
      ∀ (z : (filteredGlobalSections X).cycles ((1 : ℕ) : ℤ)) (ω : ℂ ⊗[ℚ] HQ X 1),
        bettiDeRhamHQ X 1 ω = cycleDeRhamClass X z → ∀ l : abelianPeriodLattice X,
          complexAbelianPeriod X ω l = (s * c) *
            holomorphicPathIntegral X (dim X.left) (cycleOneForm X z) (abelianLatticePath X l) :=
  spec_periods_of_cohomologyBaseChange_aux X c hsing

example (X : Over (Spec ↧ℂ)) [GrpObj X] [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    (c : ℂ)
    (hsing : ∀ (z : (filteredGlobalSections X).cycles ((1 : ℕ) : ℤ)) (ω : ℂ ⊗[ℚ] HQ X 1),
      bettiDeRhamHQ X 1 ω = cycleDeRhamClass X z →
        ∀ Ψ : AlgebraicTopology.Simplicial.Cocycle ℂ
            (TopCat.toSSet.obj (TopCat.of (ComplexPoint X))) 1,
          Ψ.1 = singularIntegrationCochain X (dim X.left) (cycleOneForm X z) →
            cohomologyBaseChange (TopCat.of (ComplexPoint X)) 1
                (LinearMap.baseChange ℂ (cupComparison X 1).toLinearMap ω) =
              c • Singular.cohomologyClass (TopCat.of (ComplexPoint X)) 1 Ψ) :
    (F^1 H_dR^((1 : ℕ) : ℤ)(X)).comap (bettiDeRhamHQ X 1) ≤ complexHolomorphicH1 X := by
  obtain ⟨s, -, hloop⟩ := spec_periods_of_cohomologyBaseChange X c hsing
  exact spec_comap_hodgeFiltration_one_le_of_periods X (s * c)
    (spec_periods_of_holomorphicPathIntegral X (s * c) hloop)

end HodgeLean.Adapters
