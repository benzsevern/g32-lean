import HodgeLean.Foundations.Program.CompensationProductProofs

/-! # Compensation product, stages C1–C4 of G34 Proposition 10.2 (FROZEN SPEC)

The frozen spec for `docs/specs/CompensationProduct.md` (plan `G32RemainingPremises.md` §5.3, as
amended by its review section). Each theorem is the matching `_aux` theorem of
`CompensationProductProofs.lean`.

It claims, for abelian varieties `A`, `Y` over `ℂ` in the repository's sense (a group object of
`Over (Spec ℂ)` that is integral, smooth and projective):

* **C1.** The product `A ⊗ Y` carries the five instances. This is on `main` and is not restated:
  `GrpObj` and `IsCommMonObj` are Mathlib instances, the other three are `gagam_product_*`, made
  instances on `A ⊗ Y` in `CompensationProductDefs`. New here: `dim (A × Y) = dim A + dim Y`.
* **C2.** Künneth: `H¹(A × Y) = pr_A^* H¹(A) ⊕ pr_Y^* H¹(Y)`, and in every degree the cup
  product of pulled-back classes is an isomorphism `⊕_{i+j=n} H^i(A) ⊗ H^j(Y) ≅ H^n(A × Y)`.
* **C3.** The `j = 0` cubic `y² = x³ + 1` with `(x, y) ↦ (ζx, y)`, `ζ` a primitive cube root of
  unity: the map is additive with `P + ζP + ζ²P = 0` on Mathlib's points, and some elliptic curve
  over `ℂ` in the repository's sense carries a group endomorphism `ρ` inducing it. For any
  endomorphism `σ` with `1 + σ + σ² = 0`, the operator `J = 1 + 2σ*` squares to `-3`. For
  `ρ` with `1 + ρ + ρ² = 0`, `σ = ρ × ρ²` on `E ⊗ E` satisfies the same relation (the second
  factor is `Ē`, the same curve with the conjugate action), and `E ⊗ E` with `J = 1 + 2σ*` is of
  Weil type. For an elliptic `E` the `(1, m)` polarization is nondegenerate, Rosati-compatible and
  positive with Weil class `[-m]`. Weil classes of every abelian surface are algebraic.
* **C4.** Given Weil actions of `ℚ(√-3)` on `A` and `Y`, there is one on `A ⊗ Y` restricting to
  them along the projections; it is of Weil type when both factors are; with the product
  polarization it is Rosati-compatible and positive, and its Weil class is the product of the
  two classes. With `dim A = 6`, `dim Y = 2` and inverse classes, `A ⊗ Y` is a member of
  `M(4, ℚ(√-3), [1])`, the hypothesis shape of `G34TheoremAStatement` (chain check below).

It does not claim: the pullback of algebraic classes along the projection (C6, which largely
exists as `CycleClassPullbackSpan.lean:66`), the projection pushforward `H¹⁰(A × Y) → H⁶(A)`
and its compatibility with cycle pushforward (C7, narrowed), the Künneth decomposition of Weil
classes (C5), the assembly of `hComp` (C8), or that the Weil class of a sixfold of Weil type is
the class of a negative rational. Every statement is about the actual cohomology `HQ`, pullback
`homPullback` and cup product `cupProductOf`; no conclusion is stored in a definition.
HC no distance; AV milestone no distance.
-/

set_option maxHeartbeats 400000

noncomputable section
attribute [local instance 100] LieRing.ofAssociativeRing

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj TensorProduct DirectSum
open HodgeLean.RealDefs HodgeLean.Adapters HodgeLean.Foundations HodgeLean.Foundations.Symplectic
open HodgeLean.Foundations.HermitianForm HodgeLean.Papers

namespace HodgeLean.Foundations.Program

/-! ### C1 and C2 -/

section Product

variable (A Y : Over (Spec ↧ℂ)) [GrpObj A] [IsIntegral A.left] [Smooth A.hom]
  [IsProjective A.hom] [GrpObj Y] [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]

/-- **C1, dimension.** The dimension of `A × Y` is the sum of the dimensions.
Source: Hartshorne, *Algebraic Geometry*, Exercise II.3.20; Stacks Project, Tag 0AFH (dimension
of a product of schemes locally of finite type over a field). -/
theorem cp_product_dim :
    TopologicalSpace.dim (A ⊗ Y).left = TopologicalSpace.dim A.left + TopologicalSpace.dim Y.left :=
  cp_product_dim_aux A Y

example (hA : TopologicalSpace.dim A.left = 6) (hY : TopologicalSpace.dim Y.left = 2) :
    TopologicalSpace.dim (A ⊗ Y).left = 8 := by
  rw [cp_product_dim, hA, hY]

/-- **C2, degree one.** `(a, b) ↦ pr_A^* a + pr_Y^* b` is a bijection
`H¹(A; ℚ) × H¹(Y; ℚ) → H¹(A × Y; ℚ)`.
Source: Hatcher, *Algebraic Topology*, Theorem 3.15 (Künneth formula), with `H⁰ = ℚ` for the
connected tori `A(ℂ)`, `Y(ℂ)`; Birkenhake–Lange, *Complex Abelian Varieties*, 2nd ed., §1.1. -/
theorem cp_kunneth_H1 :
    Function.Bijective (fun p : HQ A 1 × HQ Y 1 =>
      homPullback (fst A Y) 1 p.1 + homPullback (snd A Y) 1 p.2) :=
  cp_kunneth_H1_aux A Y

/-- Each projection is injective on `H¹`. -/
example (a : HQ A 1) (h : homPullback (fst A Y) 1 a = 0) : a = 0 := by
  have := (cp_kunneth_H1 A Y).1 (a₁ := (a, 0)) (a₂ := (0, 0)) (by simp [h])
  exact congrArg Prod.fst this

/-- **C2, every degree.** The cup product of pulled-back classes,
`⊕_{i+j=n} H^i(A; ℚ) ⊗ H^j(Y; ℚ) → H^n(A × Y; ℚ)`, is bijective.
Source: Hatcher, *Algebraic Topology*, Theorem 3.15 and §3.2 (the cross product
`a × b = pr_A^* a ∪ pr_Y^* b`); Birkenhake–Lange, §1.3. -/
theorem cp_kunneth (n : ℕ) : Function.Bijective (cp_kunnethMap A Y n) :=
  cp_kunneth_aux A Y n

example (n : ℕ) : Function.Surjective (cp_kunnethMap A Y n) := (cp_kunneth A Y n).2

end Product

/-! ### C3: the CM curve and the CM surface -/

/-- **C3, the cubic automorphism is additive.** `(x, y) ↦ (ζx, y)` is a group endomorphism of
the points of `y² = x³ + 1`: it is the change of variables `x = ζ⁻²x'`, `y = y'` (`ζ⁶ = 1`),
which fixes the equation and the point at infinity.
Source: Silverman, *The Arithmetic of Elliptic Curves*, III.3.1 and III.10.1. -/
theorem cp_cubicAut_add (P Q : cp_W.toAffine.Point) :
    cp_cubicAut (P + Q) = cp_cubicAut P + cp_cubicAut Q :=
  cp_cubicAut_add_aux P Q

example (P : cp_W.toAffine.Point) : cp_cubicAut (-P) = -cp_cubicAut P :=
  (AddMonoidHom.mk' cp_cubicAut cp_cubicAut_add).map_neg P

/-- **C3, the relation `1 + ζ + ζ² = 0` on points.** For `P = (x, y)` the points `P`, `ζP`, `ζ²P`
are the three points of the line `Y = y` on the cubic, so their sum is `0`; the points with
`x = 0` are flexes, of order three.
Source: Silverman, *The Arithmetic of Elliptic Curves*, III.2.3 (the group law) and III.10.1. -/
theorem cp_cubicAut_relation (P : cp_W.toAffine.Point) :
    P + cp_cubicAut P + cp_cubicAut (cp_cubicAut P) = 0 :=
  cp_cubicAut_relation_aux P

/-- `ζ` has order three on points. -/
example (P : cp_W.toAffine.Point) : cp_cubicAut (cp_cubicAut (cp_cubicAut P)) = P := by
  have h1 := cp_cubicAut_relation P
  have h2 := cp_cubicAut_relation (cp_cubicAut P)
  have h3 : cp_cubicAut (P + cp_cubicAut P + cp_cubicAut (cp_cubicAut P)) = 0 := by
    rw [h1]; rfl
  rw [cp_cubicAut_add, cp_cubicAut_add] at h3
  calc cp_cubicAut (cp_cubicAut (cp_cubicAut P))
      = (cp_cubicAut P + cp_cubicAut (cp_cubicAut P) + cp_cubicAut (cp_cubicAut (cp_cubicAut P)))
          - (cp_cubicAut P + cp_cubicAut (cp_cubicAut P)) := by abel
    _ = P := by rw [h3, ← h1]; abel

/-- **C3, the CM curve.** Some elliptic curve over `ℂ` in the repository's sense, with its points
identified with those of `y² = x³ + 1` as groups, carries a group endomorphism `ρ` inducing the
cubic automorphism, and `1 + ρ + ρ² = 0` in its endomorphism group.
Source: Silverman, *The Arithmetic of Elliptic Curves*, III.3.6 and III.10.1; G34 v1.5,
Lemma 10.1. -/
theorem cp_exists_cm_curve :
    ∃ (E : Over (Spec ↧ℂ)) (_ : GrpObj E) (_ : IsIntegral E.left) (ρ : E ⟶ E),
      Smooth E.hom ∧ IsProjective E.hom ∧ TopologicalSpace.dim E.left = 1 ∧ IsMonHom ρ ∧
        𝟙 E * ρ * (ρ ≫ ρ) = 1 ∧
        ∃ e : ComplexPoint E ≃ cp_W.toAffine.Point,
          (∀ P Q : ComplexPoint E, e (P * Q) = e P + e Q) ∧
            ∀ P : ComplexPoint E, e (P ≫ ρ) = cp_cubicAut (e P) :=
  cp_exists_cm_curve_aux

/-- The endomorphism is not the identity: it moves the point `(2, 3)`. -/
example : ∃ (E : Over (Spec ↧ℂ)) (_ : GrpObj E) (ρ : E ⟶ E), ρ ≠ 𝟙 E := by
  obtain ⟨E, G, -, ρ, -, -, -, -, -, e, -, he⟩ := cp_exists_cm_curve
  refine ⟨E, G, ρ, fun h => ?_⟩
  obtain ⟨P, hP⟩ := e.surjective (.some 2 3 cp_W_nonsingular_two_three)
  have := he P
  rw [h, Category.comp_id, hP] at this
  have h' : cp_cubicAut (.some 2 3 cp_W_nonsingular_two_three) =
      .some (cp_zeta * 2) 3 _ := rfl
  rw [h', WeierstrassCurve.Affine.Point.some.injEq] at this
  have hz : cp_zeta = 1 := by linear_combination -this.1 / 2
  have := cp_zeta_sq_add
  rw [hz] at this
  norm_num at this

/-- **C3, `J² = -3`.** For an endomorphism `σ` of an abelian `X` with `1 + σ + σ² = 0` in the
group `X ⟶ X`, the operator `J = 1 + 2σ*` on `H¹(X; ℚ)` squares to `-3`: pullback on `H¹` is
additive in `σ` and kills the unit, so `1 + σ* + σ*² = 0`.
Source: Birkenhake–Lange, *Complex Abelian Varieties*, 2nd ed., §1.2 (the rational representation
is a ring map); `spec_homPullback_mul`, `spec_homPullback_comp`, `spec_homPullback_one`. -/
theorem cp_weilOperator_sq (X : Over (Spec ↧ℂ)) [GrpObj X] [IsIntegral X.left]
    [Smooth X.hom] [IsProjective X.hom] (σ : X ⟶ X) (hσ : 𝟙 X * σ * (σ ≫ σ) = 1) :
    cp_weilOperator X σ ∘ₗ cp_weilOperator X σ = (-3 : ℚ) • LinearMap.id :=
  cp_weilOperator_sq_aux X σ hσ

/-- Nondegeneracy: on `B ⊗ B` the rotation satisfies the relation for every commutative `B`, so
the theorem gives a Weil action of `ℚ(√-3)` on `H¹(B × B)`. -/
example (B : Over (Spec ↧ℂ)) [GrpObj B] [IsCommMonObj B] [IsIntegral B.left] [Smooth B.hom]
    [IsProjective B.hom] :
    letI := (finiteBetti_abelian (B ⊗ B)).finite 1
    (cp_weilAction (B ⊗ B) (cp_rotation B)
      (cp_weilOperator_sq _ _ (cp_rotation_relation B))).J = cp_weilOperator _ (cp_rotation B) :=
  rfl

/-- **C3, the conjugate factor.** If `1 + ρ + ρ² = 0` for a group endomorphism `ρ` of a commutative
`E`, then `σ = ρ × ρ²` on `E ⊗ E` satisfies `1 + σ + σ² = 0`: the relation gives `ρ³ = 1`, so
`1 + ρ² + ρ⁴ = 1 + ρ² + ρ = 0`.
Source: G34 v1.5, Lemma 10.1 (`Ē` carries the conjugate action); Mathlib `MonObj.comp_mul`,
`MonObj.mul_comp`. -/
theorem cp_conjAut_relation (E : Over (Spec ↧ℂ)) [GrpObj E] [IsCommMonObj E] (ρ : E ⟶ E)
    [IsMonHom ρ] (hρ : 𝟙 E * ρ * (ρ ≫ ρ) = 1) :
    𝟙 (E ⊗ E) * cp_conjAut E ρ * (cp_conjAut E ρ ≫ cp_conjAut E ρ) = 1 :=
  cp_conjAut_relation_aux E ρ hρ

example (E : Over (Spec ↧ℂ)) [GrpObj E] [IsCommMonObj E] [IsIntegral E.left] [Smooth E.hom]
    [IsProjective E.hom] (ρ : E ⟶ E) [IsMonHom ρ] (hρ : 𝟙 E * ρ * (ρ ≫ ρ) = 1) :
    cp_weilOperator (E ⊗ E) (cp_conjAut E ρ) ∘ₗ cp_weilOperator (E ⊗ E) (cp_conjAut E ρ) =
      (-3 : ℚ) • LinearMap.id :=
  cp_weilOperator_sq _ _ (cp_conjAut_relation E ρ hρ)

section Surface

variable (E : Over (Spec ↧ℂ)) [GrpObj E] [IsCommMonObj E] [IsIntegral E.left] [Smooth E.hom]
  [IsProjective E.hom]

/-- **C3, Weil type of `E × Ē`.** For `1 + ρ + ρ² = 0`, every Weil action on `E ⊗ E` with
`J = 1 + 2σ*`, `σ = ρ × ρ²`, is of Weil type. On the first factor `J` is `1 + 2ρ*`, on the second
`1 + 2ρ*² = -(1 + 2ρ*)`, so `V_s = V_s(E) ⊕ V_{s̄}(E)` and `V_s ∩ H^{1,0}` has half the dimension
of `V_s`.
Source: G34 v1.5, Lemma 10.1; van Geemen, *An introduction to the Hodge conjecture for abelian
varieties*, LNM 1594, §5.2 (`E × Ē` is of Weil type). -/
theorem cp_cm_surface_weilType (ρ : E ⟶ E) [IsMonHom ρ] (hρ : 𝟙 E * ρ * (ρ ≫ ρ) = 1)
    (W : letI := (finiteBetti_abelian (E ⊗ E)).finite 1
      HodgeBlocks.WeilAction (abelianWeightOneHodgeStructure (E ⊗ E)) 3)
    (hJ : W.J = cp_weilOperator (E ⊗ E) (cp_conjAut E ρ)) :
    letI := (finiteBetti_abelian (E ⊗ E)).finite 1
    W.IsWeilType :=
  cp_cm_surface_weilType_aux E ρ hρ W hJ

example (ρ : E ⟶ E) [IsMonHom ρ] (hρ : 𝟙 E * ρ * (ρ ≫ ρ) = 1) :
    letI := (finiteBetti_abelian (E ⊗ E)).finite 1
    (cp_weilAction (E ⊗ E) (cp_conjAut E ρ)
      (cp_weilOperator_sq _ _ (cp_conjAut_relation E ρ hρ))).IsWeilType :=
  cp_cm_surface_weilType E ρ hρ _ rfl

/-- **C3, Rosati on the curve.** On an elliptic curve, `J = 1 + 2ρ*` with `J² = -3` acts on the
rank-two `H¹` with determinant `3`, so `⋀²J ω = 3ω` and `J` is Rosati-skew for every
nondegenerate class.
Source: Birkenhake–Lange, *Complex Abelian Varieties*, 2nd ed., §5.1 (the Rosati involution);
`isRosatiSkew_iff`. -/
theorem cp_curve_rosati (hE : TopologicalSpace.dim E.left = 1) (ρ : E ⟶ E) [IsMonHom ρ]
    (hρ : 𝟙 E * ρ * (ρ ≫ ρ) = 1) (pol : HQ E 2)
    (hη : IsNondegenerate (polarizationVec (torusCohomology_cupProductOf E) pol)) :
    letI := (finiteBetti_abelian E).finite 1
    IsRosatiSkew (polarizationVec (torusCohomology_cupProductOf E) pol) (cp_weilOperator E ρ) :=
  cp_curve_rosati_aux E hE ρ hρ pol hη

example (hE : TopologicalSpace.dim E.left = 1) (ρ : E ⟶ E) [IsMonHom ρ]
    (hρ : 𝟙 E * ρ * (ρ ≫ ρ) = 1) (pol : HQ E 2)
    (hη : IsNondegenerate (polarizationVec (torusCohomology_cupProductOf E) pol)) :
    letI := (finiteBetti_abelian E).finite 1
    IsRosatiSkew (polarizationVec (torusCohomology_cupProductOf E) pol)
      (cp_weilAction E ρ (cp_weilOperator_sq E ρ hρ)).J :=
  cp_curve_rosati E hE ρ hρ pol hη

/-- **C3, the `(1, m)` polarization of `E × Ē` and its class `[-m]`.** For an elliptic `E` with
`1 + ρ + ρ² = 0`, a positive polarization class `θ` of `E` and `m > 0`, the class
`pr₁^* θ + m · pr₂^* θ` of `E ⊗ E` is nondegenerate, Rosati-compatible with `J = 1 + 2σ*`,
positive, and its Weil class is `[-m]`: the Hermitian form is `h ⊕ (-h/m)` on `K²`, of
determinant `-h²/m`.
Source: G34 v1.5, Lemma 10.1 (`Y = E × Ē` with the `(1, m)` polarization has class `[-m]`);
van Geemen, LNM 1594, §5.2; Birkenhake–Lange, §5.2 (product polarizations). -/
theorem cp_cm_surface_polarization (hE : TopologicalSpace.dim E.left = 1) (ρ : E ⟶ E)
    [IsMonHom ρ] (hρ : 𝟙 E * ρ * (ρ ≫ ρ) = 1) (pol : HQ E 2)
    (hη : IsNondegenerate (polarizationVec (torusCohomology_cupProductOf E) pol))
    (hPos : PolarizationPositive (finiteBetti_abelian E) (spec_bettiDeRhamIso_abelian E)
      (hodgeDecomposition_of_abelian E) (torusCohomology_cupProductOf E) hη)
    (m : ℕ) (hm : 0 < m)
    (W : letI := (finiteBetti_abelian (E ⊗ E)).finite 1
      HodgeBlocks.WeilAction (abelianWeightOneHodgeStructure (E ⊗ E)) 3)
    (hJ : W.J = cp_weilOperator (E ⊗ E) (cp_conjAut E ρ)) :
    ∃ hηY : IsNondegenerate (polarizationVec (torusCohomology_cupProductOf (E ⊗ E))
        (cp_productPol E E pol ((m : ℚ) • pol))),
      ∃ hR : (letI := (finiteBetti_abelian (E ⊗ E)).finite 1
        IsRosatiSkew (polarizationVec (torusCohomology_cupProductOf (E ⊗ E))
          (cp_productPol E E pol ((m : ℚ) • pol))) W.J),
        PolarizationPositive (finiteBetti_abelian (E ⊗ E)) (spec_bettiDeRhamIso_abelian (E ⊗ E))
          (hodgeDecomposition_of_abelian (E ⊗ E)) (torusCohomology_cupProductOf (E ⊗ E)) hηY ∧
        weilDatumClass (finiteBetti_abelian (E ⊗ E)) (spec_bettiDeRhamIso_abelian (E ⊗ E))
          (hodgeDecomposition_of_abelian (E ⊗ E)) (torusCohomology_cupProductOf (E ⊗ E))
          W hηY hR = cp_ratClass (-(m : ℚ)) (neg_ne_zero.mpr (Nat.cast_ne_zero.mpr hm.ne')) :=
  cp_cm_surface_polarization_aux E hE ρ hρ pol hη hPos m hm W hJ

/-- Falsification: with `m = 2` the class is `[-2]`, which is not the trivial class, so the
surface alone is not split. -/
example (hE : TopologicalSpace.dim E.left = 1) (ρ : E ⟶ E) [IsMonHom ρ]
    (hρ : 𝟙 E * ρ * (ρ ≫ ρ) = 1) (pol : HQ E 2)
    (hη : IsNondegenerate (polarizationVec (torusCohomology_cupProductOf E) pol))
    (hPos : PolarizationPositive (finiteBetti_abelian E) (spec_bettiDeRhamIso_abelian E)
      (hodgeDecomposition_of_abelian E) (torusCohomology_cupProductOf E) hη)
    (W : letI := (finiteBetti_abelian (E ⊗ E)).finite 1
      HodgeBlocks.WeilAction (abelianWeightOneHodgeStructure (E ⊗ E)) 3)
    (hJ : W.J = cp_weilOperator (E ⊗ E) (cp_conjAut E ρ)) :
    ∃ hηY : IsNondegenerate (polarizationVec (torusCohomology_cupProductOf (E ⊗ E))
        (cp_productPol E E pol (((2 : ℕ) : ℚ) • pol))),
      ∃ hR : (letI := (finiteBetti_abelian (E ⊗ E)).finite 1
        IsRosatiSkew (polarizationVec (torusCohomology_cupProductOf (E ⊗ E))
          (cp_productPol E E pol (((2 : ℕ) : ℚ) • pol))) W.J),
        weilDatumClass (finiteBetti_abelian (E ⊗ E)) (spec_bettiDeRhamIso_abelian (E ⊗ E))
          (hodgeDecomposition_of_abelian (E ⊗ E)) (torusCohomology_cupProductOf (E ⊗ E))
          W hηY hR ≠ 1 := by
  obtain ⟨hηY, hR, -, hc⟩ := cp_cm_surface_polarization E hE ρ hρ pol hη hPos 2 two_pos W hJ
  refine ⟨hηY, hR, ?_⟩
  have h2 : cp_ratClass (-((2 : ℕ) : ℚ)) (neg_ne_zero.mpr (Nat.cast_ne_zero.mpr two_pos.ne')) =
      classNegTwo := by
    simp only [cp_ratClass, classNegTwo]
    congr 1
  rw [hc, h2]
  exact class_neg_two_ne_one

end Surface

/-- **C3, Weil classes of abelian surfaces are divisor classes.** On an abelian surface a
Weil-type action has `k = 1`, so its Weil classes lie in `Hdg¹`, and Lefschetz (1,1) makes them
algebraic.
Source: Weil, "Abelian varieties and the Hodge ring" (1977); Griffiths–Harris, *Principles of
Algebraic Geometry*, Ch. 1 §2 (Lefschetz (1,1)); `two_mul_finrank_vs_inf_h10_eq`,
`abelian_weilClassOf_le_hdg`, `chowG_lefschetzOneOne_abelian`. -/
theorem cp_surface_weilClassesAlgebraic (Y : Over (Spec ↧ℂ)) [GrpObj Y] [IsCommMonObj Y]
    [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom] (hY : TopologicalSpace.dim Y.left = 2)
    {d : ℚ} (hd : 0 < d)
    (W : letI := (finiteBetti_abelian Y).finite 1
      HodgeBlocks.WeilAction (abelianWeightOneHodgeStructure Y) d)
    (hW : letI := (finiteBetti_abelian Y).finite 1; W.IsWeilType) :
    letI := (finiteBetti_abelian Y).finite 1
    WeilClassesAlgebraic (finiteBetti_abelian Y) (spec_bettiDeRhamIso_abelian Y)
      (hodgeDecomposition_of_abelian Y) (torusCohomology_cupProductOf Y) W hW :=
  cp_surface_weilClassesAlgebraic_aux Y hY hd W hW

/-- On `E × Ē` with `J = 1 + 2σ*`, the Weil classes are algebraic. -/
example (E : Over (Spec ↧ℂ)) [GrpObj E] [IsCommMonObj E] [IsIntegral E.left] [Smooth E.hom]
    [IsProjective E.hom] (hE : TopologicalSpace.dim E.left = 1) (ρ : E ⟶ E) [IsMonHom ρ]
    (hρ : 𝟙 E * ρ * (ρ ≫ ρ) = 1) :
    letI := (finiteBetti_abelian (E ⊗ E)).finite 1
    WeilClassesAlgebraic (finiteBetti_abelian (E ⊗ E)) (spec_bettiDeRhamIso_abelian (E ⊗ E))
      (hodgeDecomposition_of_abelian (E ⊗ E)) (torusCohomology_cupProductOf (E ⊗ E))
      (cp_weilAction (E ⊗ E) (cp_conjAut E ρ)
        (cp_weilOperator_sq _ _ (cp_conjAut_relation E ρ hρ)))
      (cp_cm_surface_weilType E ρ hρ _ rfl) :=
  cp_surface_weilClassesAlgebraic (E ⊗ E) (by rw [cp_product_dim, hE]) (by norm_num) _ _

/-! ### C4: the product is a member of `M(4, ℚ(√-3), [1])` -/

section Member

variable (A Y : Over (Spec ↧ℂ)) [GrpObj A] [IsCommMonObj A] [IsIntegral A.left] [Smooth A.hom]
  [IsProjective A.hom] [GrpObj Y] [IsCommMonObj Y] [IsIntegral Y.left] [Smooth Y.hom]
  [IsProjective Y.hom]

/-- **C4, the sum action.** Weil actions of `ℚ(√-3)` on `H¹(A)` and `H¹(Y)` extend to one on
`H¹(A × Y)` that restricts to them along `pr_A^*` and `pr_Y^*`: `J = J_A ⊕ J_Y` under C2, which
preserves the Hodge pieces because the pullbacks do.
Source: G34 v1.5, proof of Proposition 10.2 (`A × Y` with the sum action); Birkenhake–Lange,
§1.2 and Theorem 1.4.1; `spec_homPullback_hodgePiece_one`. -/
theorem cp_product_weilAction
    (WA : letI := (finiteBetti_abelian A).finite 1
      HodgeBlocks.WeilAction (abelianWeightOneHodgeStructure A) 3)
    (WY : letI := (finiteBetti_abelian Y).finite 1
      HodgeBlocks.WeilAction (abelianWeightOneHodgeStructure Y) 3) :
    ∃ W : (letI := (finiteBetti_abelian (A ⊗ Y)).finite 1
        HodgeBlocks.WeilAction (abelianWeightOneHodgeStructure (A ⊗ Y)) 3),
      (∀ a, W.J (homPullback (fst A Y) 1 a) = homPullback (fst A Y) 1 (WA.J a)) ∧
        ∀ b, W.J (homPullback (snd A Y) 1 b) = homPullback (snd A Y) 1 (WY.J b) :=
  cp_product_weilAction_aux A Y WA WY

/-- **C4, Weil type.** A Weil action on `A × Y` restricting to Weil-type actions on both factors
is of Weil type: `V_s` and `V_s ∩ H^{1,0}` split along C2, and the dimensions add.
Source: G34 v1.5, proof of Proposition 10.2; van Geemen, LNM 1594, §5.2. -/
theorem cp_product_weilType
    (WA : letI := (finiteBetti_abelian A).finite 1
      HodgeBlocks.WeilAction (abelianWeightOneHodgeStructure A) 3)
    (hWA : letI := (finiteBetti_abelian A).finite 1; WA.IsWeilType)
    (WY : letI := (finiteBetti_abelian Y).finite 1
      HodgeBlocks.WeilAction (abelianWeightOneHodgeStructure Y) 3)
    (hWY : letI := (finiteBetti_abelian Y).finite 1; WY.IsWeilType)
    (W : letI := (finiteBetti_abelian (A ⊗ Y)).finite 1
      HodgeBlocks.WeilAction (abelianWeightOneHodgeStructure (A ⊗ Y)) 3)
    (hA : ∀ a, W.J (homPullback (fst A Y) 1 a) = homPullback (fst A Y) 1 (WA.J a))
    (hY : ∀ b, W.J (homPullback (snd A Y) 1 b) = homPullback (snd A Y) 1 (WY.J b)) :
    letI := (finiteBetti_abelian (A ⊗ Y)).finite 1
    W.IsWeilType :=
  cp_product_weilType_aux A Y WA hWA WY hWY W hA hY

example
    (WA : letI := (finiteBetti_abelian A).finite 1
      HodgeBlocks.WeilAction (abelianWeightOneHodgeStructure A) 3)
    (hWA : letI := (finiteBetti_abelian A).finite 1; WA.IsWeilType)
    (WY : letI := (finiteBetti_abelian Y).finite 1
      HodgeBlocks.WeilAction (abelianWeightOneHodgeStructure Y) 3)
    (hWY : letI := (finiteBetti_abelian Y).finite 1; WY.IsWeilType) :
    ∃ W : (letI := (finiteBetti_abelian (A ⊗ Y)).finite 1
        HodgeBlocks.WeilAction (abelianWeightOneHodgeStructure (A ⊗ Y)) 3),
      letI := (finiteBetti_abelian (A ⊗ Y)).finite 1
      W.IsWeilType := by
  obtain ⟨W, hA, hY⟩ := cp_product_weilAction A Y WA WY
  exact ⟨W, cp_product_weilType A Y WA hWA WY hWY W hA hY⟩

/-- **C4, the product polarization and its class.** With the product polarization
`pr_A^* θ_A + pr_Y^* θ_Y`, a Weil action on `A × Y` restricting to `W_A`, `W_Y` is
Rosati-compatible, the polarization is nondegenerate and positive, and the Weil class is the
product of the two classes: the Hermitian form is the orthogonal sum.
Source: G34 v1.5, proof of Proposition 10.2 (the discriminant multiplies);
`papers_sameNormClass_mul`; van Geemen, LNM 1594, §5; Birkenhake–Lange, §5.2. -/
theorem cp_product_polarization
    (WA : letI := (finiteBetti_abelian A).finite 1
      HodgeBlocks.WeilAction (abelianWeightOneHodgeStructure A) 3)
    (polA : HQ A 2)
    (hηA : IsNondegenerate (polarizationVec (torusCohomology_cupProductOf A) polA))
    (hRA : letI := (finiteBetti_abelian A).finite 1;
      IsRosatiSkew (polarizationVec (torusCohomology_cupProductOf A) polA) WA.J)
    (hPosA : PolarizationPositive (finiteBetti_abelian A) (spec_bettiDeRhamIso_abelian A)
      (hodgeDecomposition_of_abelian A) (torusCohomology_cupProductOf A) hηA)
    (WY : letI := (finiteBetti_abelian Y).finite 1
      HodgeBlocks.WeilAction (abelianWeightOneHodgeStructure Y) 3)
    (polY : HQ Y 2)
    (hηY : IsNondegenerate (polarizationVec (torusCohomology_cupProductOf Y) polY))
    (hRY : letI := (finiteBetti_abelian Y).finite 1;
      IsRosatiSkew (polarizationVec (torusCohomology_cupProductOf Y) polY) WY.J)
    (hPosY : PolarizationPositive (finiteBetti_abelian Y) (spec_bettiDeRhamIso_abelian Y)
      (hodgeDecomposition_of_abelian Y) (torusCohomology_cupProductOf Y) hηY)
    (W : letI := (finiteBetti_abelian (A ⊗ Y)).finite 1
      HodgeBlocks.WeilAction (abelianWeightOneHodgeStructure (A ⊗ Y)) 3)
    (hA : ∀ a, W.J (homPullback (fst A Y) 1 a) = homPullback (fst A Y) 1 (WA.J a))
    (hY : ∀ b, W.J (homPullback (snd A Y) 1 b) = homPullback (snd A Y) 1 (WY.J b)) :
    ∃ hη : IsNondegenerate (polarizationVec (torusCohomology_cupProductOf (A ⊗ Y))
        (cp_productPol A Y polA polY)),
      ∃ hR : (letI := (finiteBetti_abelian (A ⊗ Y)).finite 1
        IsRosatiSkew (polarizationVec (torusCohomology_cupProductOf (A ⊗ Y))
          (cp_productPol A Y polA polY)) W.J),
        PolarizationPositive (finiteBetti_abelian (A ⊗ Y)) (spec_bettiDeRhamIso_abelian (A ⊗ Y))
          (hodgeDecomposition_of_abelian (A ⊗ Y)) (torusCohomology_cupProductOf (A ⊗ Y)) hη ∧
        weilDatumClass (finiteBetti_abelian (A ⊗ Y)) (spec_bettiDeRhamIso_abelian (A ⊗ Y))
            (hodgeDecomposition_of_abelian (A ⊗ Y)) (torusCohomology_cupProductOf (A ⊗ Y))
            W hη hR =
          weilDatumClass (finiteBetti_abelian A) (spec_bettiDeRhamIso_abelian A)
              (hodgeDecomposition_of_abelian A) (torusCohomology_cupProductOf A) WA hηA hRA *
            weilDatumClass (finiteBetti_abelian Y) (spec_bettiDeRhamIso_abelian Y)
              (hodgeDecomposition_of_abelian Y) (torusCohomology_cupProductOf Y) WY hηY hRY :=
  cp_product_polarization_aux A Y WA polA hηA hRA hPosA WY polY hηY hRY hPosY W hA hY

/-- **Chain check toward `hComp`: C1, C4 and Theorem A.** For a sixfold `A` and a surface `Y`
with inverse Weil classes, `A ⊗ Y` with the sum action and product polarization meets every
hypothesis of `G34TheoremAStatement (A ⊗ Y)`, so Theorem A for it gives algebraicity of the Weil
classes of the eightfold. C5–C8 then carry them back to `A`. -/
example (hA6 : TopologicalSpace.dim A.left = 6) (hY2 : TopologicalSpace.dim Y.left = 2)
    (WA : letI := (finiteBetti_abelian A).finite 1
      HodgeBlocks.WeilAction (abelianWeightOneHodgeStructure A) 3)
    (hWA : letI := (finiteBetti_abelian A).finite 1; WA.IsWeilType)
    (polA : HQ A 2)
    (hηA : IsNondegenerate (polarizationVec (torusCohomology_cupProductOf A) polA))
    (hRA : letI := (finiteBetti_abelian A).finite 1;
      IsRosatiSkew (polarizationVec (torusCohomology_cupProductOf A) polA) WA.J)
    (hPosA : PolarizationPositive (finiteBetti_abelian A) (spec_bettiDeRhamIso_abelian A)
      (hodgeDecomposition_of_abelian A) (torusCohomology_cupProductOf A) hηA)
    (WY : letI := (finiteBetti_abelian Y).finite 1
      HodgeBlocks.WeilAction (abelianWeightOneHodgeStructure Y) 3)
    (hWY : letI := (finiteBetti_abelian Y).finite 1; WY.IsWeilType)
    (polY : HQ Y 2)
    (hηY : IsNondegenerate (polarizationVec (torusCohomology_cupProductOf Y) polY))
    (hRY : letI := (finiteBetti_abelian Y).finite 1;
      IsRosatiSkew (polarizationVec (torusCohomology_cupProductOf Y) polY) WY.J)
    (hPosY : PolarizationPositive (finiteBetti_abelian Y) (spec_bettiDeRhamIso_abelian Y)
      (hodgeDecomposition_of_abelian Y) (torusCohomology_cupProductOf Y) hηY)
    (hcls : weilDatumClass (finiteBetti_abelian A) (spec_bettiDeRhamIso_abelian A)
        (hodgeDecomposition_of_abelian A) (torusCohomology_cupProductOf A) WA hηA hRA *
      weilDatumClass (finiteBetti_abelian Y) (spec_bettiDeRhamIso_abelian Y)
        (hodgeDecomposition_of_abelian Y) (torusCohomology_cupProductOf Y) WY hηY hRY = 1)
    (hThmA : G34TheoremAStatement (A ⊗ Y)) :
    ∃ W : (letI := (finiteBetti_abelian (A ⊗ Y)).finite 1
        HodgeBlocks.WeilAction (abelianWeightOneHodgeStructure (A ⊗ Y)) 3),
      (∀ a, W.J (homPullback (fst A Y) 1 a) = homPullback (fst A Y) 1 (WA.J a)) ∧
      (∀ b, W.J (homPullback (snd A Y) 1 b) = homPullback (snd A Y) 1 (WY.J b)) ∧
      ∃ hW : (letI := (finiteBetti_abelian (A ⊗ Y)).finite 1; W.IsWeilType),
        letI := (finiteBetti_abelian (A ⊗ Y)).finite 1
        WeilClassesAlgebraic (finiteBetti_abelian (A ⊗ Y)) (spec_bettiDeRhamIso_abelian (A ⊗ Y))
          (hodgeDecomposition_of_abelian (A ⊗ Y)) (torusCohomology_cupProductOf (A ⊗ Y)) W hW := by
  obtain ⟨W, hA, hY⟩ := cp_product_weilAction A Y WA WY
  have hW := cp_product_weilType A Y WA hWA WY hWY W hA hY
  obtain ⟨hη, hR, hPos, hc⟩ :=
    cp_product_polarization A Y WA polA hηA hRA hPosA WY polY hηY hRY hPosY W hA hY
  refine ⟨W, hA, hY, hW, hThmA W hW _ hη hR hPos ?_ ?_⟩
  · rw [cp_product_dim, hA6, hY2]
  · rw [hc, hcls]

end Member

/-- **Chain check C3 → C4.** For the CM surface `Y = E ⊗ E` with `J = 1 + 2σ*` and the `(1, m)`
polarization, the product `A ⊗ Y` carries a Weil-type action restricting to `W_A` and to `J`,
with Weil class `[A] · [-m]`. With `m` from `g34c_split_class` this is the class `[1]` that
Theorem A asks for. -/
example (A : Over (Spec ↧ℂ)) [GrpObj A] [IsCommMonObj A] [IsIntegral A.left] [Smooth A.hom]
    [IsProjective A.hom] (E : Over (Spec ↧ℂ)) [GrpObj E] [IsCommMonObj E] [IsIntegral E.left]
    [Smooth E.hom] [IsProjective E.hom] (hE : TopologicalSpace.dim E.left = 1) (ρ : E ⟶ E)
    [IsMonHom ρ] (hρ : 𝟙 E * ρ * (ρ ≫ ρ) = 1) (pol : HQ E 2)
    (hη : IsNondegenerate (polarizationVec (torusCohomology_cupProductOf E) pol))
    (hPos : PolarizationPositive (finiteBetti_abelian E) (spec_bettiDeRhamIso_abelian E)
      (hodgeDecomposition_of_abelian E) (torusCohomology_cupProductOf E) hη)
    (m : ℕ) (hm : 0 < m)
    (WA : letI := (finiteBetti_abelian A).finite 1
      HodgeBlocks.WeilAction (abelianWeightOneHodgeStructure A) 3)
    (hWA : letI := (finiteBetti_abelian A).finite 1; WA.IsWeilType)
    (polA : HQ A 2)
    (hηA : IsNondegenerate (polarizationVec (torusCohomology_cupProductOf A) polA))
    (hRA : letI := (finiteBetti_abelian A).finite 1;
      IsRosatiSkew (polarizationVec (torusCohomology_cupProductOf A) polA) WA.J)
    (hPosA : PolarizationPositive (finiteBetti_abelian A) (spec_bettiDeRhamIso_abelian A)
      (hodgeDecomposition_of_abelian A) (torusCohomology_cupProductOf A) hηA) :
    ∃ W : (letI := (finiteBetti_abelian (A ⊗ (E ⊗ E))).finite 1
        HodgeBlocks.WeilAction (abelianWeightOneHodgeStructure (A ⊗ (E ⊗ E))) 3),
      (letI := (finiteBetti_abelian (A ⊗ (E ⊗ E))).finite 1; W.IsWeilType) ∧
      ∃ hη' : IsNondegenerate (polarizationVec (torusCohomology_cupProductOf (A ⊗ (E ⊗ E)))
          (cp_productPol A (E ⊗ E) polA (cp_productPol E E pol ((m : ℚ) • pol)))),
        ∃ hR : (letI := (finiteBetti_abelian (A ⊗ (E ⊗ E))).finite 1
          IsRosatiSkew (polarizationVec (torusCohomology_cupProductOf (A ⊗ (E ⊗ E)))
            (cp_productPol A (E ⊗ E) polA (cp_productPol E E pol ((m : ℚ) • pol)))) W.J),
          weilDatumClass (finiteBetti_abelian (A ⊗ (E ⊗ E)))
              (spec_bettiDeRhamIso_abelian (A ⊗ (E ⊗ E)))
              (hodgeDecomposition_of_abelian (A ⊗ (E ⊗ E)))
              (torusCohomology_cupProductOf (A ⊗ (E ⊗ E))) W hη' hR =
            weilDatumClass (finiteBetti_abelian A) (spec_bettiDeRhamIso_abelian A)
                (hodgeDecomposition_of_abelian A) (torusCohomology_cupProductOf A) WA hηA hRA *
              cp_ratClass (-(m : ℚ)) (neg_ne_zero.mpr (Nat.cast_ne_zero.mpr hm.ne')) := by
  let WY := cp_weilAction (E ⊗ E) (cp_conjAut E ρ)
    (cp_weilOperator_sq _ _ (cp_conjAut_relation E ρ hρ))
  have hWY := cp_cm_surface_weilType E ρ hρ WY rfl
  obtain ⟨hηY, hRY, hPosY, hcY⟩ := cp_cm_surface_polarization E hE ρ hρ pol hη hPos m hm WY rfl
  obtain ⟨W, hA, hY⟩ := cp_product_weilAction A (E ⊗ E) WA WY
  obtain ⟨hη', hR, -, hc⟩ :=
    cp_product_polarization A (E ⊗ E) WA polA hηA hRA hPosA WY _ hηY hRY hPosY W hA hY
  exact ⟨W, cp_product_weilType A (E ⊗ E) WA hWA WY hWY W hA hY, hη', hR, hc.trans (by rw [hcY])⟩

end HodgeLean.Foundations.Program
