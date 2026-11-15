import HodgeLean.Foundations.GeometricIntegralityCProofs
import HodgeLean.Adapters.AbelianPowerHodge

/-! # The Powers flagship, stage G3 part 2a: geometric integrality over `ℂ` (FROZEN SPEC)

Stage G3 (optional), part 2a, of formalizing PW v0.3, Theorem 4.2 (`thm:gen`)
(doi:10.5281/zenodo.23570103). G3 part 1 (`Adapters/AbelianPower.lean`) shows that the power
`A^r = g3_power A r` is integral **if** `A` is geometrically integral over `ℂ` (its S11). This
stage freezes the statements that remove that binder: an integral scheme locally of finite type
over `ℂ` is geometrically integral, so `A^r` is integral for every `r` as soon as `A` is integral
and smooth over `ℂ`. Each theorem is the matching `_aux` theorem of
`GeometricIntegralityCProofs.lean`, whose proofs are open.

The route is the Nullstellensatz route (`docs/specs/GeometricIntegralityC.md`). It claims:

* over an algebraically closed field `k`, the `k`-points `A →ₐ[k] k` of a finitely generated
  reduced `k`-algebra `A` separate its elements, and the same holds for `A ⊗[k] B` with `B` any
  `k`-algebra, through the maps `φ ⊗ id` (S1, S2);
* over an algebraically closed field `k`, `A ⊗[k] B` is a domain when `A` is a finitely generated
  domain and `B` is any domain (S3);
* for an integral complex scheme `X`, locally of finite type, and any field `K` over `ℂ`, the base
  change `X ×_ℂ Spec K` is integral: affine case (S4), reduced (S5), irreducible (S6);
* hence `X` is geometrically integral over `ℂ` (S7), and `A^r` is integral for every `r` when `A`
  is integral and smooth over `ℂ`, with no geometric-integrality binder (S8);
* falsification checks: `ℂ ⊗[ℝ] ℂ` is not a domain, and `Spec ℂ` is integral and of finite type
  over `ℝ` but not geometrically integral, so S3 and S7 fail without an algebraically closed base
  (N1, N2); `Spec (ℂ × ℂ)` (not connected) and `Spec ℂ[ε]` (irreducible, not reduced) are of finite
  type over `ℂ` and not geometrically integral, so integrality cannot be weakened to either half
  (N3, N4); `RatFunc ℂ` has no `ℂ`-points, so S1 fails without finite generation (N5).

It does not claim: projectivity of `A^r` for `r ≥ 2` (the Segre embedding, part 2b); geometric
reducedness over a perfect field that is not algebraically closed; any statement over a base other
than `ℂ` at the scheme level; that `LocallyOfFiniteType` is necessary in S5–S7 (it is not; it is
what the Nullstellensatz route uses). Where `[IsProjective (g3_power A r).hom]` appears in the link
examples, the statement is an implication from it. HC no distance; AV milestone no distance.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory
open scoped TensorProduct CategoryTheory.MonObj
open HodgeLean.Adapters AlgebraicGeometry.ComplexPoint HodgeLean.RealDefs TopologicalSpace

namespace HodgeLean.Foundations

/-! ### Commutative algebra over an algebraically closed field -/

/-- **S1. The `k`-points separate elements.** If `A` is a finitely generated reduced algebra over
an algebraically closed field `k` and `φ a = 0` for every `k`-algebra map `φ : A → k`, then
`a = 0`: `A` is a Jacobson ring, so its nilradical (here `0`) is the intersection of the maximal
ideals, and every maximal ideal is the kernel of a `k`-point (the residue field is finite over
`k`, hence `k`).
Source: Atiyah–Macdonald, *Introduction to Commutative Algebra*, Ex. 5.26 and Cor. 7.10 (weak
Nullstellensatz); Mathlib `isJacobsonRing_of_finiteType`,
`finite_of_algHom_finiteType_of_isJacobsonRing`,
`IsAlgClosed.algebraMap_surjective_of_isIntegral`. -/
theorem spec_g3b_eq_zero_of_forall_algHom {k A : Type*} [Field k] [IsAlgClosed k]
    [CommRing A] [Algebra k A] [Algebra.FiniteType k A] [IsReduced A] (a : A)
    (h : ∀ φ : A →ₐ[k] k, φ a = 0) : a = 0 :=
  spec_g3b_eq_zero_of_forall_algHom_aux a h

example (a : MvPolynomial (Fin 2) ℂ) (h : ∀ φ : MvPolynomial (Fin 2) ℂ →ₐ[ℂ] ℂ, φ a = 0) :
    a = 0 :=
  spec_g3b_eq_zero_of_forall_algHom a h

/-- **S2. The `k`-points separate elements of `A ⊗[k] B`.** With `A` as in S1 and `B` any
`k`-algebra, if `(φ ⊗ id) f = 0` in `k ⊗[k] B` for every `k`-point `φ` of `A`, then `f = 0`:
expand `f = Σ_j a_j ⊗ e_j` in a `k`-basis `(e_j)` of `B`; then `(φ ⊗ id) f = Σ_j φ(a_j) ⊗ e_j`, so
each `a_j` is killed by every `φ`, and `a_j = 0` by S1.
Source: Milne, *Algebraic Geometry*, Prop. 4.15 (products of affine varieties); Mathlib
`TensorProduct.equivFinsuppOfBasisRight`, `Algebra.TensorProduct.map_tmul`. -/
theorem spec_g3b_tensor_eq_zero_of_forall_algHom {k A B : Type*} [Field k] [IsAlgClosed k]
    [CommRing A] [Algebra k A] [Algebra.FiniteType k A] [IsReduced A] [CommRing B] [Algebra k B]
    (f : A ⊗[k] B) (h : ∀ φ : A →ₐ[k] k, Algebra.TensorProduct.map φ (AlgHom.id k B) f = 0) :
    f = 0 :=
  spec_g3b_tensor_eq_zero_of_forall_algHom_aux f h

example (f : MvPolynomial (Fin 1) ℂ ⊗[ℂ] RatFunc ℂ)
    (h : ∀ φ : MvPolynomial (Fin 1) ℂ →ₐ[ℂ] ℂ,
      Algebra.TensorProduct.map φ (AlgHom.id ℂ (RatFunc ℂ)) f = 0) : f = 0 :=
  spec_g3b_tensor_eq_zero_of_forall_algHom f h

/-- **S3. Tensor products of domains over an algebraically closed field.** If `k` is algebraically
closed, `A` a finitely generated `k`-domain and `B` any `k`-domain, then `A ⊗[k] B` is a domain.
Let `f g = 0` and write `f = Σ_j a_j ⊗ e_j`, `g = Σ_j c_j ⊗ e_j` in a `k`-basis of `B`. For each
`k`-point `φ` of `A`, `(φ ⊗ id) f · (φ ⊗ id) g = 0` in the domain `B`, so `φ` kills all `a_j` or
all `c_j`; hence `φ (a_i c_j) = 0` for all `i, j` and all `φ`, so `a_i c_j = 0` (S1) and, `A` being
a domain, all `a_i = 0` or all `c_j = 0`. Nontriviality: `A ⊗[k] B` contains `k ⊗ k`.
Source: Milne, *Algebraic Geometry*, Prop. 4.15; Hartshorne, *Algebraic Geometry*, Ex. I.3.15(a)
(the product of varieties over an algebraically closed field is irreducible). -/
theorem spec_g3b_isDomain_tensorProduct {k A B : Type*} [Field k] [IsAlgClosed k]
    [CommRing A] [Algebra k A] [Algebra.FiniteType k A] [IsDomain A] [CommRing B] [Algebra k B]
    [IsDomain B] : IsDomain (A ⊗[k] B) :=
  spec_g3b_isDomain_tensorProduct_aux

example : IsDomain (MvPolynomial (Fin 2) ℂ ⊗[ℂ] RatFunc ℂ) :=
  spec_g3b_isDomain_tensorProduct

/-! ### Base change of an integral complex scheme to a field -/

/-- **S4. The affine case.** For a finitely generated `ℂ`-domain `A` and a field `K` over `ℂ`,
`Spec A ×_ℂ Spec K ≅ Spec (A ⊗[ℂ] K)` is integral, by S3.
Source: Hartshorne, *Algebraic Geometry*, Ex. II.3.15; Mathlib `pullbackSpecIso`,
`affine_isIntegral_iff`, `IsIntegral.of_isIso`. -/
theorem spec_g3b_isIntegral_pullback_spec (A : Type) [CommRing A] [Algebra ℂ A]
    [Algebra.FiniteType ℂ A] [IsDomain A] (K : Type) [Field K] [Algebra ℂ K] :
    IsIntegral (pullback (Spec.map (CommRingCat.ofHom (algebraMap ℂ A)))
      (Spec.map (CommRingCat.ofHom (algebraMap ℂ K)))) :=
  spec_g3b_isIntegral_pullback_spec_aux A K

example (K : Type) [Field K] [Algebra ℂ K] :
    IsIntegral (pullback (Spec.map (CommRingCat.ofHom (algebraMap ℂ (MvPolynomial (Fin 1) ℂ))))
      (Spec.map (CommRingCat.ofHom (algebraMap ℂ K)))) :=
  spec_g3b_isIntegral_pullback_spec _ K

/-- **S5. The base change is reduced.** Reducedness is local; the base changes of the affine opens
`U = Spec A` of `X` cover `X ×_ℂ Spec K`, each `A` is a finitely generated `ℂ`-domain (`X`
integral, locally of finite type), and each piece is integral by S4.
Source: Hartshorne, *Algebraic Geometry*, Ex. II.3.15; Mathlib `IsReduced.iff_of_openCover`,
`Scheme.OpenCover.pullback₁`, `IsAffineOpen.isoSpec`. -/
theorem spec_g3b_isReduced_baseChange (X : Over (Spec ↧ℂ)) [IsIntegral X.left]
    [LocallyOfFiniteType X.hom] (K : Type) [Field K] [Algebra ℂ K] :
    IsReduced (pullback X.hom (Spec.map (CommRingCat.ofHom (algebraMap ℂ K)))) :=
  spec_g3b_isReduced_baseChange_aux X K

example (K : Type) [Field K] [Algebra ℂ K] :
    IsReduced (pullback (𝟙_ (Over (Spec ↧ℂ))).hom
      (Spec.map (CommRingCat.ofHom (algebraMap ℂ K)))) :=
  spec_g3b_isReduced_baseChange _ K

/-- **S6. The base change is irreducible.** The base changes `U_K` of the nonempty affine opens
`U` of `X` are irreducible (S4) open subsets covering `X_K`; any two meet, because `U ∩ V` is a
nonempty open of the irreducible `X` and `X_K → X` is surjective (base change of the surjection
`Spec K → Spec ℂ`). An open cover by irreducible opens with pairwise nonempty intersections gives
an irreducible space (Mathlib), and `X_K` is nonempty.
Source: Hartshorne, *Algebraic Geometry*, Ex. II.3.15; Mathlib
`PreirreducibleSpace.of_isOpenCover`, `Surjective` stable under base change. -/
theorem spec_g3b_irreducibleSpace_baseChange (X : Over (Spec ↧ℂ)) [IsIntegral X.left]
    [LocallyOfFiniteType X.hom] (K : Type) [Field K] [Algebra ℂ K] :
    IrreducibleSpace ↥(pullback X.hom (Spec.map (CommRingCat.ofHom (algebraMap ℂ K)))) :=
  spec_g3b_irreducibleSpace_baseChange_aux X K

example (K : Type) [Field K] [Algebra ℂ K] :
    IrreducibleSpace ↥(pullback (𝟙_ (Over (Spec ↧ℂ))).hom
      (Spec.map (CommRingCat.ofHom (algebraMap ℂ K)))) :=
  spec_g3b_irreducibleSpace_baseChange _ K

/-- **S7. An integral complex scheme of finite type is geometrically integral.** By Mathlib's
`geometrically_iff_of_commRing`, it suffices that `X ×_ℂ Spec K` is integral for every field `K`
over `ℂ`: it is reduced (S5) and irreducible (S6).
Source: Hartshorne, *Algebraic Geometry*, Ex. II.3.15; Stacks Project, Section 33.9 (Tag 0366,
geometrically integral schemes) and Lemma 33.3.3 (Tag 05P3); Mathlib `GeometricallyIntegral`,
`geometrically_iff_of_commRing`,
`isIntegral_of_irreducibleSpace_of_isReduced`. -/
theorem spec_g3b_geometricallyIntegral (X : Over (Spec ↧ℂ)) [IsIntegral X.left]
    [LocallyOfFiniteType X.hom] : GeometricallyIntegral X.hom :=
  spec_g3b_geometricallyIntegral_aux X

/-- The zero-dimensional case: the point `Spec ℂ` is geometrically integral over itself. -/
example : GeometricallyIntegral (𝟙_ (Over (Spec ↧ℂ))).hom :=
  spec_g3b_geometricallyIntegral _

/-- The target form for G3: a commutative group object that is integral and smooth over `ℂ` is
geometrically integral (the group structure is not used). -/
example (A : Over (Spec ↧ℂ)) [GrpObj A] [IsCommMonObj A] [IsIntegral A.left] [Smooth A.hom] :
    GeometricallyIntegral A.hom :=
  spec_g3b_geometricallyIntegral A

/-- **S8. `A^r` is integral, with no geometric-integrality binder.** S7 supplies
`GeometricallyIntegral A.hom` (smooth implies locally of finite type), and G3 part 1's S11
(`spec_g3_isIntegral_power`) gives integrality of `A^r`.
Source: Hartshorne, *Algebraic Geometry*, Ex. II.3.15 and Ex. I.3.15;
`spec_g3b_geometricallyIntegral`,
`spec_g3_isIntegral_power`. -/
theorem spec_g3b_isIntegral_power (A : Over (Spec ↧ℂ)) [IsIntegral A.left] [Smooth A.hom]
    (r : ℕ) : IsIntegral (g3_power A r).left :=
  spec_g3b_isIntegral_power_aux A r

example (A : Over (Spec ↧ℂ)) [IsIntegral A.left] [Smooth A.hom] (r : ℕ) :
    IsIntegral (g3_power A r).left :=
  spec_g3b_isIntegral_power A r

attribute [instance] spec_g3b_isIntegral_power

/-- `r = 2`, the first case not covered by G3 part 1 without a binder. -/
example (A : Over (Spec ↧ℂ)) [IsIntegral A.left] [Smooth A.hom] :
    IsIntegral (g3_power A 2).left := inferInstance

/-- `r = 0`: `A^0 = Spec ℂ`, integral for every `A`. -/
example (A : Over (Spec ↧ℂ)) [IsIntegral A.left] [Smooth A.hom] :
    IsIntegral (g3_power A 0).left := spec_g3b_isIntegral_power A 0

/-- `r = 1`: `A^1 = A ⊗ 𝟙_`. -/
example (A : Over (Spec ↧ℂ)) [IsIntegral A.left] [Smooth A.hom] :
    IsIntegral (g3_power A 1).left := spec_g3b_isIntegral_power A 1

/-! ### Falsification checks -/

/-- **N1. S3 fails over `ℝ`.** `(1 ⊗ i - i ⊗ 1)(1 ⊗ i + i ⊗ 1) = 1 ⊗ i² - i² ⊗ 1 = 0`, and both
factors are nonzero (`ℂ ⊗[ℝ] ℂ ≅ ℂ × ℂ`). So the algebraically closed base in S3 is needed.
Source: Milne, *Fields and Galois Theory*, §8 (`ℂ ⊗_ℝ ℂ ≅ ℂ × ℂ`). -/
theorem spec_g3b_not_isDomain_complex_tensor : ¬ IsDomain (ℂ ⊗[ℝ] ℂ) :=
  spec_g3b_not_isDomain_complex_tensor_aux

example : ¬ IsDomain (ℂ ⊗[ℝ] ℂ) := spec_g3b_not_isDomain_complex_tensor

/-- **N2. S7 fails over `ℝ`.** `Spec ℂ` is integral and of finite type over `ℝ`, but its base change
to `ℂ` is `Spec (ℂ ⊗[ℝ] ℂ)`, not integral (N1). So the field must be algebraically closed.
Source: Hartshorne, *Algebraic Geometry*, Ex. II.3.15(b) (`Spec ℂ` over `ℝ`). -/
theorem spec_g3b_not_geometricallyIntegral_real :
    IsIntegral (Spec (CommRingCat.of ℂ)) ∧
      LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (algebraMap ℝ ℂ))) ∧
      ¬ GeometricallyIntegral (Spec.map (CommRingCat.ofHom (algebraMap ℝ ℂ))) :=
  spec_g3b_not_geometricallyIntegral_real_aux

example : ¬ GeometricallyIntegral (Spec.map (CommRingCat.ofHom (algebraMap ℝ ℂ))) :=
  spec_g3b_not_geometricallyIntegral_real.2.2

/-- **N3. Integrality cannot be dropped: a non-connected example.** `Spec (ℂ × ℂ) = Spec ℂ ⊔ Spec ℂ`
(the constant group scheme `ℤ/2`) is finite over `ℂ` but not geometrically integral: its base
change to `ℂ` is itself, and `ℂ × ℂ` is not a domain.
Source: Mathlib `self_of_isIntegral_of_geometrically`, `affine_isIntegral_iff`. -/
theorem spec_g3b_not_geometricallyIntegral_prod :
    LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (algebraMap ℂ (ℂ × ℂ)))) ∧
      ¬ GeometricallyIntegral (Spec.map (CommRingCat.ofHom (algebraMap ℂ (ℂ × ℂ)))) :=
  spec_g3b_not_geometricallyIntegral_prod_aux

example : ¬ GeometricallyIntegral (Spec.map (CommRingCat.ofHom (algebraMap ℂ (ℂ × ℂ)))) :=
  spec_g3b_not_geometricallyIntegral_prod.2

/-- **N4. Integrality cannot be weakened to irreducibility: a non-reduced example.**
`Spec ℂ[ε]` (`ε² = 0`) is irreducible (one point) and finite over `ℂ`, but not geometrically
integral, since `ε` is a nonzero nilpotent.
Source: Hartshorne, *Algebraic Geometry*, Ex. II.2.3 (reduced schemes); Mathlib `DualNumber`. -/
theorem spec_g3b_not_geometricallyIntegral_dualNumber :
    IrreducibleSpace (Spec (CommRingCat.of (DualNumber ℂ))) ∧
      LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (algebraMap ℂ (DualNumber ℂ)))) ∧
      ¬ GeometricallyIntegral (Spec.map (CommRingCat.ofHom (algebraMap ℂ (DualNumber ℂ)))) :=
  spec_g3b_not_geometricallyIntegral_dualNumber_aux

example :
    ¬ GeometricallyIntegral (Spec.map (CommRingCat.ofHom (algebraMap ℂ (DualNumber ℂ)))) :=
  spec_g3b_not_geometricallyIntegral_dualNumber.2.2

/-- **N5. S1 fails without finite generation.** `RatFunc ℂ` is a domain with no `ℂ`-point (a
`ℂ`-point would send `X - φ(X)`, a unit, to `0`), so in S1 every element, `1` included, is killed
by every `ℂ`-point.
Source: Atiyah–Macdonald, *Introduction to Commutative Algebra*, Ex. 5.26 (finite generation in
the Nullstellensatz); Mathlib `RatFunc`. -/
theorem spec_g3b_isEmpty_algHom_ratFunc : IsEmpty (RatFunc ℂ →ₐ[ℂ] ℂ) :=
  spec_g3b_isEmpty_algHom_ratFunc_aux

example : IsEmpty (RatFunc ℂ →ₐ[ℂ] ℂ) := spec_g3b_isEmpty_algHom_ratFunc

/-! ### The link with G2 and G4: integrality of `A^r` discharged -/

section Link

variable (A : Over (Spec ↧ℂ)) [GrpObj A] [IsCommMonObj A] [IsIntegral A.left] [Smooth A.hom]
  [IsProjective A.hom]

/-- G2's dimension formula at `Y = A^r`: the only remaining binder is projectivity of `A^r`. -/
example (r : ℕ) [IsProjective (g3_power A r).hom] :
    dim (g3_power A r).left = r * dim A.left :=
  spec_g2_dim_eq (g3_powerData A r)

/-- G4's pullback formula at `Y = A^r`, under the same single binder. -/
example (r : ℕ) [IsProjective (g3_power A r).hom] (a : Fin r → AbelianEnd A) :
    homPullback ((g3_powerData A r).sumMap a) 1 =
      ∑ i, homPullback ((g3_powerData A r).proj i) 1 ∘ₗ abelianEndAction A (a i) :=
  spec_g4_homPullback_sumMap (g3_powerData A r) a

end Link

end HodgeLean.Foundations
