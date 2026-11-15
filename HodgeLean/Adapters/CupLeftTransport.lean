import HodgeLean.Adapters.CupLeftTransportProofs

/-! # Transport of the left cup with a degree-one class to `HQ X k` and along `bettiDeRhamHQ`: frozen specification

Stage hl4 of the `hL` track (`docs/specs/CupLeftTransport.md`), comparison stage 2. Stage hl2
(`CupCocycleSheaf`) built, for a singular `1`-cocycle `a` on `X(ℂ)`, the morphism
`C_a : S• ⟶ S•⟦1⟧` of sheafified singular cochains and proved that its action on hypercohomology,
read through `singularToSheafHypercohomology`, is left cup with `[a]` on `H^k_sing(X(ℂ); K)`
(`spec_cupLeftHypercohomology_singularToSheafHypercohomology`). This stage reads that action on the
repository's rational cohomology `HQ X k`, with the cup of `cupProductOf X`, and on
`ℂ ⊗[ℚ] HQ X k` through `bettiDeRhamHQ`, with `cupC`.

Claimed:
* for every space: the universal-coefficient base change `ℂ ⊗ H^*_sing(Y; ℚ) → H^*_sing(Y; ℂ)`
  is multiplicative for a left factor of degree one;
* for smooth projective integral `X`: the complex singular class (`complexSingularClass`, the base
  change of `cupComparison`) is multiplicative for `cupC` with a left factor of degree one;
* for smooth projective integral `X`, over `ℚ`: if `[a] = cupComparison X 1 x`, then `ℍ(C_a)`,
  transported along `ℍ^k(S•_ℚ) ≃ H^k(X(ℂ); ℚ) = HQ X k`, is `(cupProductOf X).cup x`, with scalar
  exactly `1` (the normalization scalar of `cupComparison` is the same in every degree, so it
  cancels);
* over `ℂ`: if `[a]` is the complex singular class of `x ∈ ℂ ⊗ HQ X 1`, then `ℍ(C_a)` sends the
  class of `y` to the class of `(cupProductOf X).cupC x y`, with no scalar;
* through `bettiDeRhamHQ`: there is one nonzero `c : ℂ`, depending only on `X`, with
  `β_{1+k}(x ∪ y) = c · dR(e_{1+k}(ℍ(C_a)(class of y)))` for every `k`, `x`, `a`, `y`, where `dR` is
  `fieldToDeRhamCohomology ℂ X` and `e` the identification `ℍ(S•_ℂ) ≃ H(X(ℂ); ℂ)`; `c` is the
  inverse of the normalization scalar of `spec_singularToFieldCohomology_cupComparison` in degree
  `1 + k`; and `β_{1+k}(x ∪ y) = 0` exactly when `ℍ(C_a)` kills the class of `y`.

Every input is proved on the base: `spec_singularToFieldCohomology_cupComparison`,
`spec_deRham_singularToFieldCohomology_cohomologyBaseChange`,
`spec_singularToFieldCohomology_cochainBaseChange`, `spec_fieldToDeRhamCohomology_complex_bijective`
and hl2's statement 4. No statement carries an open input as a binder.

Not claimed: `hL`; the Yoneda comparison of the de Rham operator `ℍ(L_θ)` with `ℍ(C_a)` (stage hl3);
the integration of a holomorphic `1`-form `θ` as a cocycle `a_θ`; the value of `c` beyond its
identification with the inverse normalization scalar; any statement with a left factor of degree
other than one. No statement assumes `BettiDeRhamIso`, `HodgeDecomposition` or `CupFiltered`, and
none adds a hypothesis. It is an implication from no geometric input beyond smooth, projective and
integral. HC no distance; AV milestone no distance.
-/

noncomputable section

-- Boundary conversions between HQ and upstream sheaf cohomology have deep instance terms.
set_option maxRecDepth 4000

open CategoryTheory AlgebraicGeometry ComplexPoint
open HodgeLean.RealDefs HodgeLean.Foundations
open scoped TensorProduct

namespace HodgeLean.Adapters

/-- For every space `Y`, the universal-coefficient base change is multiplicative for a left factor
of degree one: if the complex `1`-cocycle `Ψ` is the base change of the rational `1`-cocycle `ψ`,
then `1 ⊗ ([ψ] ∪ v)` goes to `[Ψ] ∪ (image of 1 ⊗ v)`. On cochains, base change along the ring map
`ℚ → ℂ` commutes with the Alexander–Whitney product, since `(ψ ∪ φ)(σ) = ψ(front σ) · φ(back σ)`.
Source: Hatcher, *Algebraic Topology*, §3.2 (cup product with coefficients in a ring, naturality in
the coefficient ring) and §3.A (universal coefficients); stage 4j
`spec_cohomologyBaseChange_tmul_cohomologyClass`. -/
theorem spec_cohomologyBaseChange_cup_left (Y : TopCat.{0})
    (ψ : AlgebraicTopology.Simplicial.Cocycle ℚ (TopCat.toSSet.obj Y) 1)
    (Ψ : AlgebraicTopology.Simplicial.Cocycle ℂ (TopCat.toSSet.obj Y) 1)
    (h : Ψ.1 = cochainBaseChange _ 1 ψ.1) (k : ℕ)
    (v : AlgebraicTopology.Singular.Cohomology ℚ Y k) :
    cohomologyBaseChange Y (1 + k)
        (1 ⊗ₜ Singular.cup Y rfl (Singular.cohomologyClass Y 1 ψ) v) =
      Singular.cup Y rfl (Singular.cohomologyClass Y 1 Ψ) (cohomologyBaseChange Y k (1 ⊗ₜ v)) :=
  spec_cohomologyBaseChange_cup_left_aux Y ψ Ψ h k v

example (Y : TopCat.{0})
    (ψ : AlgebraicTopology.Simplicial.Cocycle ℚ (TopCat.toSSet.obj Y) 1)
    (Ψ : AlgebraicTopology.Simplicial.Cocycle ℂ (TopCat.toSSet.obj Y) 1)
    (h : Ψ.1 = cochainBaseChange _ 1 ψ.1) (k : ℕ)
    (v : AlgebraicTopology.Singular.Cohomology ℚ Y k) (z : ℂ) :
    cohomologyBaseChange Y (1 + k)
        (z ⊗ₜ Singular.cup Y rfl (Singular.cohomologyClass Y 1 ψ) v) =
      z • Singular.cup Y rfl (Singular.cohomologyClass Y 1 Ψ)
        (cohomologyBaseChange Y k (1 ⊗ₜ v)) := by
  rw [← spec_cohomologyBaseChange_cup_left Y ψ Ψ h k v, ← map_smul, TensorProduct.smul_tmul',
    smul_eq_mul, mul_one]

/-- For smooth projective integral `X`, the complex singular class is multiplicative for a left
factor of degree one: the class of `x ∪ y` (`cupC` of `cupProductOf X`) is the singular cup of the
classes of `x` and `y`. On pure tensors `z ⊗ u`, `w ⊗ v` this is `cupComparison_cup` followed by
`spec_cohomologyBaseChange_cup_left`.
Source: Hatcher, *Algebraic Topology*, §3.2 (cup product) and §3.A (universal coefficients);
`cupComparison_cup`, `CupProduct.cupC_tmul` and `spec_cohomologyBaseChange_cup_left`. -/
theorem spec_complexSingularClass_cupC (X : Over (Spec ↧ℂ))
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] (k : ℕ)
    (x : ℂ ⊗[ℚ] HQ X 1) (y : ℂ ⊗[ℚ] HQ X k) :
    complexSingularClass X (1 + k) ((cupProductOf X).cupC rfl x y) =
      Singular.cup (TopCat.of (ComplexPoint X)) rfl (complexSingularClass X 1 x)
        (complexSingularClass X k y) :=
  spec_complexSingularClass_cupC_aux X k x y

example (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    (u : HQ X 1) (v : HQ X 1) :
    complexSingularClass X (1 + 1) ((cupProductOf X).cupC rfl (1 ⊗ₜ u) (1 ⊗ₜ v)) =
      Singular.cup (TopCat.of (ComplexPoint X)) rfl (complexSingularClass X 1 (1 ⊗ₜ u))
        (complexSingularClass X 1 (1 ⊗ₜ v)) :=
  spec_complexSingularClass_cupC X 1 _ _

/-- **Over `ℚ`.** For smooth projective integral `X`, `x ∈ HQ X 1` and a rational singular
`1`-cocycle `a` with `[a] = cupComparison X 1 x`: the action of `C_a` on hypercohomology,
transported along `e_k : ℍ^k(S•_ℚ) ≃ H^k(X(ℂ); ℚ) = HQ X k` (`sheafHypercohomologyFieldEquiv`), is
left cup with `x` for `cupProductOf X`, with scalar exactly `1`. Here `singularToFieldCohomology =
e ∘ singularToSheafHypercohomology` sends `cupComparison X n v` to `r · v` with one nonzero
rational `r` for all `n` (`normalizedEquiv` rescales every degree by the same scalar), so
`e_k⁻¹ v` is the class of `r⁻¹ · cupComparison X k v`; hl2's statement 4 and `cupComparison_cup`
then give `r⁻¹ · r · (x ∪ v)`.
Source: Bredon, *Sheaf Theory*, 2nd ed., GTM 170, III.1 (the comparison of sheaf and singular
cohomology); Hatcher, *Algebraic Topology*, §3.2; hl2
`spec_cupLeftHypercohomology_singularToSheafHypercohomology`, `cupComparison_cup` and stage 4j
`spec_singularToFieldCohomology_cupComparison`. -/
theorem spec_cupLeftHypercohomology_transport_rat (X : Over (Spec ↧ℂ))
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] (x : HQ X 1)
    (a : AlgebraicTopology.Simplicial.Cocycle ℚ (TopCat.toSSet.obj (TopCat.of (ComplexPoint X))) 1)
    (ha : Singular.cohomologyClass _ 1 a = cupComparison X 1 x)
    (k : ℕ) (h : 1 + (k : ℤ) = ((1 + k : ℕ) : ℤ)) (v : HQ X k) :
    sheafHypercohomologyFieldEquiv ℚ X (1 + k)
        (cupLeftHypercohomology X a h
          ((sheafHypercohomologyFieldEquiv ℚ X k).symm (HQ.linearEquiv X k v))) =
      HQ.linearEquiv X (1 + k) ((cupProductOf X).cup rfl x v) :=
  spec_cupLeftHypercohomology_transport_rat_aux X x a ha k h v

example (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    (x : HQ X 1)
    (a : AlgebraicTopology.Simplicial.Cocycle ℚ (TopCat.toSSet.obj (TopCat.of (ComplexPoint X))) 1)
    (ha : Singular.cohomologyClass _ 1 a = cupComparison X 1 x) (v : HQ X 1)
    (hne : (cupProductOf X).cup rfl x v ≠ 0) :
    cupLeftHypercohomology X a (n := ((1 : ℕ) : ℤ)) (m := ((1 + 1 : ℕ) : ℤ)) (by omega)
      ((sheafHypercohomologyFieldEquiv ℚ X 1).symm (HQ.linearEquiv X 1 v)) ≠ 0 := by
  intro h0
  apply hne
  rw [← (HQ.linearEquiv X (1 + 1)).map_eq_zero_iff,
    ← spec_cupLeftHypercohomology_transport_rat X x a ha 1 (by omega) v, h0, map_zero]

/-- **Over `ℂ`.** For smooth projective integral `X`, `x ∈ ℂ ⊗[ℚ] HQ X 1` and a complex singular
`1`-cocycle `a` whose class is the complex singular class of `x`: `C_a` sends the hypercohomology
class of (the complex singular class of) `y ∈ ℂ ⊗[ℚ] HQ X k` to the class of
`(cupProductOf X).cupC x y`, with no scalar. This is hl2's statement 4 with `K = ℂ`, rewritten by
`spec_complexSingularClass_cupC`.
Source: Bredon, *Sheaf Theory*, 2nd ed., GTM 170, II.4 and III.1; Hatcher, *Algebraic Topology*,
§3.2 and §3.A; hl2 `spec_cupLeftHypercohomology_singularToSheafHypercohomology` and
`spec_complexSingularClass_cupC`. -/
theorem spec_cupLeftHypercohomology_transport_complex (X : Over (Spec ↧ℂ))
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] (x : ℂ ⊗[ℚ] HQ X 1)
    (a : AlgebraicTopology.Simplicial.Cocycle ℂ (TopCat.toSSet.obj (TopCat.of (ComplexPoint X))) 1)
    (ha : Singular.cohomologyClass _ 1 a = complexSingularClass X 1 x)
    (k : ℕ) (h : 1 + (k : ℤ) = ((1 + k : ℕ) : ℤ)) (y : ℂ ⊗[ℚ] HQ X k) :
    cupLeftHypercohomology X a h (singularToSheafHypercohomology X ℂ k (complexSingularClass X k y)) =
      singularToSheafHypercohomology X ℂ (1 + k)
        (complexSingularClass X (1 + k) ((cupProductOf X).cupC rfl x y)) :=
  spec_cupLeftHypercohomology_transport_complex_aux X x a ha k h y

example (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    (x : ℂ ⊗[ℚ] HQ X 1)
    (a : AlgebraicTopology.Simplicial.Cocycle ℂ (TopCat.toSSet.obj (TopCat.of (ComplexPoint X))) 1)
    (ha : Singular.cohomologyClass _ 1 a = complexSingularClass X 1 x) (y : ℂ ⊗[ℚ] HQ X 1) :
    singularToFieldCohomology ℂ X (1 + 1) (complexSingularClass X (1 + 1)
        ((cupProductOf X).cupC rfl x y)) =
      sheafHypercohomologyFieldEquiv ℂ X (1 + 1) (cupLeftHypercohomology X a
        (n := ((1 : ℕ) : ℤ)) (m := ((1 + 1 : ℕ) : ℤ)) (by omega)
        (singularToSheafHypercohomology X ℂ 1 (complexSingularClass X 1 y))) := by
  rw [spec_cupLeftHypercohomology_transport_complex X x a ha 1 _ y]
  rfl

/-- **Through `bettiDeRhamHQ`.** For smooth projective integral `X` there is one nonzero `c : ℂ`,
depending only on `X`, such that for every `k`, every `x ∈ ℂ ⊗[ℚ] HQ X 1`, every complex
`1`-cocycle `a` whose class is the complex singular class of `x` and every `y ∈ ℂ ⊗[ℚ] HQ X k`:
`β_{1+k}(x ∪ y)` is `c` times the de Rham image of `ℍ(C_a)` applied to the class of `y`. The de Rham
image is `fieldToDeRhamCohomology ℂ X ∘ e`, with `e : ℍ(S•_ℂ) ≃ H(X(ℂ); ℂ)`; its composite with
`singularToSheafHypercohomology` is stage 4k's `fieldToDeRhamCohomology ℂ X ∘
singularToFieldCohomology ℂ X`. The constant is `r⁻¹`, `r` the normalization scalar of
`cupComparison`.
Source: Bredon, *Sheaf Theory*, 2nd ed., GTM 170, III.1 (naturality of the comparison in the
coefficients); Hatcher, *Algebraic Topology*, §3.A; `spec_cupLeftHypercohomology_transport_complex`
and stage 4j `spec_deRham_singularToFieldCohomology_cohomologyBaseChange`. -/
theorem spec_bettiDeRhamHQ_cupC_eq_smul_deRham_cupLeft (X : Over (Spec ↧ℂ))
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] :
    ∃ c : ℂ, c ≠ 0 ∧ ∀ (k : ℕ) (h : 1 + (k : ℤ) = ((1 + k : ℕ) : ℤ)) (x : ℂ ⊗[ℚ] HQ X 1)
      (a : AlgebraicTopology.Simplicial.Cocycle ℂ
        (TopCat.toSSet.obj (TopCat.of (ComplexPoint X))) 1),
      Singular.cohomologyClass _ 1 a = complexSingularClass X 1 x →
      ∀ y : ℂ ⊗[ℚ] HQ X k,
        bettiDeRhamHQ X (1 + k) ((cupProductOf X).cupC rfl x y) =
          c • fieldToDeRhamCohomology ℂ X (1 + k) (sheafHypercohomologyFieldEquiv ℂ X (1 + k)
            (cupLeftHypercohomology X a h
              (singularToSheafHypercohomology X ℂ k (complexSingularClass X k y)))) :=
  spec_bettiDeRhamHQ_cupC_eq_smul_deRham_cupLeft_aux X

example (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    (k : ℕ) (h : 1 + (k : ℤ) = ((1 + k : ℕ) : ℤ)) (x : ℂ ⊗[ℚ] HQ X 1)
    (a : AlgebraicTopology.Simplicial.Cocycle ℂ (TopCat.toSSet.obj (TopCat.of (ComplexPoint X))) 1)
    (ha : Singular.cohomologyClass _ 1 a = complexSingularClass X 1 x) (y : ℂ ⊗[ℚ] HQ X k)
    (P : Submodule ℂ (H_dR^((1 + k : ℕ) : ℤ)(X)))
    (hP : fieldToDeRhamCohomology ℂ X (1 + k) (sheafHypercohomologyFieldEquiv ℂ X (1 + k)
      (cupLeftHypercohomology X a h
        (singularToSheafHypercohomology X ℂ k (complexSingularClass X k y)))) ∈ P) :
    bettiDeRhamHQ X (1 + k) ((cupProductOf X).cupC rfl x y) ∈ P := by
  obtain ⟨c, -, hc⟩ := spec_bettiDeRhamHQ_cupC_eq_smul_deRham_cupLeft X
  rw [hc k h x a ha y]
  exact P.smul_mem c hP

/-- **The scalar, pinned.** For smooth projective integral `X`, every `k` and every rational `q`
that is a normalization scalar of `cupComparison` in degree `1 + k` (the identity of
`spec_singularToFieldCohomology_cupComparison`): the constant of
`spec_bettiDeRhamHQ_cupC_eq_smul_deRham_cupLeft` can be taken to be `q⁻¹`. If `HQ X (1 + k) ≠ 0`,
`q` is the unique such scalar, and it is nonzero; if `HQ X (1 + k) = 0`, both sides vanish.
Source: stage 4j `spec_singularToFieldCohomology_cupComparison` and
`spec_deRham_singularToFieldCohomology_cohomologyBaseChange` (whose constant is any such `q`);
`spec_cupLeftHypercohomology_transport_complex`. -/
theorem spec_bettiDeRhamHQ_cupC_eq_inv_smul_deRham_cupLeft (X : Over (Spec ↧ℂ))
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] (k : ℕ) (q : ℚ)
    (hq : ∀ v : HQ X (1 + k),
      singularToFieldCohomology ℚ X (1 + k) (cupComparison X (1 + k) v) =
        q • HQ.linearEquiv X (1 + k) v)
    (h : 1 + (k : ℤ) = ((1 + k : ℕ) : ℤ)) (x : ℂ ⊗[ℚ] HQ X 1)
    (a : AlgebraicTopology.Simplicial.Cocycle ℂ (TopCat.toSSet.obj (TopCat.of (ComplexPoint X))) 1)
    (ha : Singular.cohomologyClass _ 1 a = complexSingularClass X 1 x) (y : ℂ ⊗[ℚ] HQ X k) :
    bettiDeRhamHQ X (1 + k) ((cupProductOf X).cupC rfl x y) =
      (q : ℂ)⁻¹ • fieldToDeRhamCohomology ℂ X (1 + k) (sheafHypercohomologyFieldEquiv ℂ X (1 + k)
        (cupLeftHypercohomology X a h
          (singularToSheafHypercohomology X ℂ k (complexSingularClass X k y)))) :=
  spec_bettiDeRhamHQ_cupC_eq_inv_smul_deRham_cupLeft_aux X k q hq h x a ha y

example (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    (k : ℕ) (h : 1 + (k : ℤ) = ((1 + k : ℕ) : ℤ)) (x : ℂ ⊗[ℚ] HQ X 1)
    (a : AlgebraicTopology.Simplicial.Cocycle ℂ (TopCat.toSSet.obj (TopCat.of (ComplexPoint X))) 1)
    (ha : Singular.cohomologyClass _ 1 a = complexSingularClass X 1 x) (y : ℂ ⊗[ℚ] HQ X k) :
    ∃ q : ℚ, q ≠ 0 ∧ bettiDeRhamHQ X (1 + k) ((cupProductOf X).cupC rfl x y) =
      (q : ℂ)⁻¹ • fieldToDeRhamCohomology ℂ X (1 + k) (sheafHypercohomologyFieldEquiv ℂ X (1 + k)
        (cupLeftHypercohomology X a h
          (singularToSheafHypercohomology X ℂ k (complexSingularClass X k y)))) := by
  obtain ⟨q, hq0, hq⟩ := spec_singularToFieldCohomology_cupComparison X (1 + k)
  exact ⟨q, hq0, spec_bettiDeRhamHQ_cupC_eq_inv_smul_deRham_cupLeft X k q hq h x a ha y⟩

/-- **Nonzero.** For smooth projective integral `X`, with `x`, `a`, `y` as above:
`β_{1+k}(x ∪ y) = 0` exactly when `ℍ(C_a)` kills the class of `y`. So the transport is not
degenerate: the scalar is nonzero, `e` is an equivalence and `fieldToDeRhamCohomology ℂ X` is
injective for smooth integral `X`.
Source: `spec_bettiDeRhamHQ_cupC_eq_smul_deRham_cupLeft`; stage 4j
`spec_fieldToDeRhamCohomology_complex_bijective` (holomorphic Poincaré lemma). -/
theorem spec_bettiDeRhamHQ_cupC_eq_zero_iff_cupLeft (X : Over (Spec ↧ℂ))
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] (k : ℕ)
    (h : 1 + (k : ℤ) = ((1 + k : ℕ) : ℤ)) (x : ℂ ⊗[ℚ] HQ X 1)
    (a : AlgebraicTopology.Simplicial.Cocycle ℂ (TopCat.toSSet.obj (TopCat.of (ComplexPoint X))) 1)
    (ha : Singular.cohomologyClass _ 1 a = complexSingularClass X 1 x) (y : ℂ ⊗[ℚ] HQ X k) :
    bettiDeRhamHQ X (1 + k) ((cupProductOf X).cupC rfl x y) = 0 ↔
      cupLeftHypercohomology X a h
        (singularToSheafHypercohomology X ℂ k (complexSingularClass X k y)) = 0 :=
  spec_bettiDeRhamHQ_cupC_eq_zero_iff_cupLeft_aux X k h x a ha y

example (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    (k : ℕ) (h : 1 + (k : ℤ) = ((1 + k : ℕ) : ℤ)) (x : ℂ ⊗[ℚ] HQ X 1)
    (a : AlgebraicTopology.Simplicial.Cocycle ℂ (TopCat.toSSet.obj (TopCat.of (ComplexPoint X))) 1)
    (ha : Singular.cohomologyClass _ 1 a = complexSingularClass X 1 x) (y : ℂ ⊗[ℚ] HQ X k)
    (hne : bettiDeRhamHQ X (1 + k) ((cupProductOf X).cupC rfl x y) ≠ 0) :
    cupLeftHypercohomology X a h
      (singularToSheafHypercohomology X ℂ k (complexSingularClass X k y)) ≠ 0 :=
  fun h0 ↦ hne ((spec_bettiDeRhamHQ_cupC_eq_zero_iff_cupLeft X k h x a ha y).mpr h0)

end HodgeLean.Adapters
