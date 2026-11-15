import HodgeLean.Papers.G34Compensation
import HodgeLean.Adapters.GagaMapsProofs
import HodgeLean.Adapters.AbelianHomPullbackDegrees
import HodgeLean.Foundations.Curves.CubicGrpObj

/-! # Definitions for the compensation product, stages C1–C4 (G34 Proposition 10.2)

Definitions for `docs/specs/CompensationProduct.md`. They are data, with proofs only where a
structure field needs one, and every such proof uses results already on `main`.

* `cp_tensor_isIntegral`, `cp_tensor_smooth`, `cp_tensor_isProjective`: the three scheme
  instances of a product `A ⊗ Y` in `Over (Spec ℂ)`, as instances on `A ⊗ Y` itself. They are
  `gagam_product_isIntegral`, `gagam_product_smooth`, `gagam_product_projective` (stage C1 is
  on `main`); `GrpObj (A ⊗ Y)` and `IsCommMonObj (A ⊗ Y)` are Mathlib instances.
* `cp_zeta`, the primitive cube root of unity `(-1 + √3 i)/2`; `cp_W`, the Weierstrass equation
  `y² = x³ + 1`; `cp_cubicAut`, the automorphism `(x, y) ↦ (ζx, y)` on Mathlib's points of `cp_W`.
* `cp_weilOperator X σ = 1 + 2σ*` on `HQ X 1`, for an endomorphism `σ`; `cp_weilAction`, the
  Weil action it gives once `J² = -3` is supplied as an argument.
* `cp_conjAut E ρ = ρ × ρ²` on `E ⊗ E`: the second factor is the same curve with the conjugate
  action, since `ρ² = ρ⁻¹`.
* `cp_productPol`, the sum of the pulled-back polarization classes; `cp_kunnethMap`, the cup
  product of pulled-back classes on `⊕_{i+j=n} H^i(A) ⊗ H^j(Y)`; `cp_ratClass`, the class of a
  nonzero rational modulo norms from `ℚ(√-3)`.

HC no distance; AV milestone no distance.
-/

set_option maxHeartbeats 400000

noncomputable section
attribute [local instance 100] LieRing.ofAssociativeRing

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj TensorProduct DirectSum
open HodgeLean.RealDefs HodgeLean.Adapters HodgeLean.Foundations HodgeLean.Foundations.Symplectic
open HodgeLean.Foundations.HermitianForm

namespace HodgeLean.Foundations.Program

/-! ### C1: the product carries the five instances -/

/-- The product of two integral schemes of finite type over `ℂ` is integral, as an instance on
`A ⊗ Y`.
Source: Stacks Project, Tag 05P3; `gagam_product_isIntegral`. -/
instance cp_tensor_isIntegral (A Y : Over (Spec ↧ℂ)) [IsIntegral A.left] [IsIntegral Y.left]
    [LocallyOfFiniteType A.hom] [LocallyOfFiniteType Y.hom] : IsIntegral (A ⊗ Y).left :=
  gagam_product_isIntegral A Y

/-- The product of two smooth schemes over `ℂ` is smooth, as an instance on `A ⊗ Y`.
Source: Mathlib, stability of smooth morphisms under base change and composition;
`gagam_product_smooth`. -/
instance cp_tensor_smooth (A Y : Over (Spec ↧ℂ)) [Smooth A.hom] [Smooth Y.hom] :
    Smooth (A ⊗ Y).hom :=
  gagam_product_smooth A Y

/-- The product of two projective schemes over `ℂ` is projective, as an instance on `A ⊗ Y`.
Source: EGA II, 5.5.5; `gagam_product_projective`. -/
instance cp_tensor_isProjective (A Y : Over (Spec ↧ℂ)) [IsProjective A.hom]
    [IsProjective Y.hom] : IsProjective (A ⊗ Y).hom :=
  gagam_product_projective A Y

/-- Stage C1: the product of two abelian varieties carries all five instances, by inference. -/
example (A Y : Over (Spec ↧ℂ)) [GrpObj A] [IsCommMonObj A] [IsIntegral A.left] [Smooth A.hom]
    [IsProjective A.hom] [GrpObj Y] [IsCommMonObj Y] [IsIntegral Y.left] [Smooth Y.hom]
    [IsProjective Y.hom] :
    Nonempty (GrpObj (A ⊗ Y)) ∧ IsCommMonObj (A ⊗ Y) ∧ IsIntegral (A ⊗ Y).left ∧
      Smooth (A ⊗ Y).hom ∧ IsProjective (A ⊗ Y).hom :=
  ⟨⟨inferInstance⟩, inferInstance, inferInstance, inferInstance, inferInstance⟩

/-! ### C3: the cubic automorphism of `y² = x³ + 1` -/

/-- The primitive cube root of unity `ζ = (-1 + √3 i)/2`. It is not `QuadraticAlgebra.omega`,
which squares to `-3`; the element `1 + 2ζ = √3 i` is the one that does.
Source: Silverman, *The Arithmetic of Elliptic Curves*, III.10 (the automorphism group of
`j = 0`). -/
def cp_zeta : ℂ := (-1 + Real.sqrt 3 * Complex.I) / 2

/-- `ζ² + ζ + 1 = 0`. -/
theorem cp_zeta_sq_add : cp_zeta ^ 2 + cp_zeta + 1 = 0 := by
  have h3 : (Real.sqrt 3 : ℂ) ^ 2 = 3 := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num)]; norm_num
  simp only [cp_zeta]
  linear_combination (Complex.I ^ 2 / 4) * h3 + (3 / 4) * Complex.I_sq

/-- `ζ³ = 1`. -/
theorem cp_zeta_cube : cp_zeta ^ 3 = 1 := by
  linear_combination (cp_zeta - 1) * cp_zeta_sq_add

/-- `ζ ≠ 1`, so `ζ` is a primitive cube root: `1 + 1 + 1 ≠ 0`. -/
example : cp_zeta ≠ 1 := by
  intro h
  have := cp_zeta_sq_add
  rw [h] at this
  norm_num at this

/-- `(1 + 2ζ)² = -3`: the operator `J = 1 + 2ζ` is a square root of `-3`. -/
example : (1 + 2 * cp_zeta) ^ 2 = -3 := by
  linear_combination 4 * cp_zeta_sq_add

/-- The Weierstrass equation `y² = x³ + 1`, of `j`-invariant `0`.
Source: Silverman, *The Arithmetic of Elliptic Curves*, III.1 and III.10. -/
def cp_W : WeierstrassCurve ℂ where
  a₁ := 0
  a₂ := 0
  a₃ := 0
  a₄ := 0
  a₆ := 1

/-- The discriminant of `y² = x³ + 1` is `-432`. -/
theorem cp_W_discriminant : cp_W.Δ = -432 := by
  simp [cp_W, WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.b₈]
  norm_num

/-- `y² = x³ + 1` is elliptic. -/
instance cp_W_isElliptic : cp_W.IsElliptic := by
  rw [WeierstrassCurve.isElliptic_iff, cp_W_discriminant]
  exact isUnit_iff_ne_zero.mpr (by norm_num)

/-- `(x, y) ↦ (ζx, y)` preserves the equation `y² = x³ + 1`. -/
theorem cp_W_equation_zeta {x y : ℂ} (h : cp_W.toAffine.Equation x y) :
    cp_W.toAffine.Equation (cp_zeta * x) y := by
  rw [WeierstrassCurve.Affine.equation_iff] at h ⊢
  simp only [cp_W] at h ⊢
  linear_combination h - x ^ 3 * cp_zeta_cube

/-- The cubic automorphism `(x, y) ↦ (ζx, y)` of `y² = x³ + 1`, on Mathlib's points, fixing the
point at infinity.
Source: Silverman, *The Arithmetic of Elliptic Curves*, III.10.1 (automorphisms of `j = 0`). -/
def cp_cubicAut : cp_W.toAffine.Point → cp_W.toAffine.Point
  | .zero => .zero
  | .some x y h => .some (cp_zeta * x) y
      (WeierstrassCurve.Affine.equation_iff_nonsingular.mp (cp_W_equation_zeta h.1))

/-- `(2, 3)` is a point of `y² = x³ + 1`. -/
theorem cp_W_nonsingular_two_three : cp_W.toAffine.Nonsingular 2 3 :=
  WeierstrassCurve.Affine.equation_iff_nonsingular.mp (by
    rw [WeierstrassCurve.Affine.equation_iff]; simp only [cp_W]; norm_num)

/-- Nondegeneracy: the automorphism moves the point `(2, 3)`, so it is not the identity. -/
example : cp_cubicAut (.some 2 3 cp_W_nonsingular_two_three) ≠
    .some 2 3 cp_W_nonsingular_two_three := by
  intro h
  simp only [cp_cubicAut, WeierstrassCurve.Affine.Point.some.injEq] at h
  have hz : cp_zeta = 1 := by
    linear_combination h.1 / 2
  have := cp_zeta_sq_add
  rw [hz] at this
  norm_num at this

/-- On a finite point the automorphism multiplies `x` by `ζ` and keeps `y`. -/
example (x y : ℂ) (h : cp_W.toAffine.Nonsingular x y) :
    ∃ h' : cp_W.toAffine.Nonsingular (cp_zeta * x) y,
      cp_cubicAut (.some x y h) = .some (cp_zeta * x) y h' :=
  ⟨_, rfl⟩

/-! ### C3: the operator `J = 1 + 2σ*` and its Weil action -/

section Operator

variable (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]

/-- The operator `J = 1 + 2σ*` on `HQ X 1` for an endomorphism `σ : X ⟶ X`. For `σ` with
`1 + σ + σ² = 0` it squares to `-3`, and it is the action of `√-3 = 1 + 2ζ` for the `ℤ[ζ]`-action
in which `ζ` acts by `σ`.
Source: G34 v1.5, Lemma 10.1 (the CM surface and its `ℚ(√-3)`-action); Birkenhake–Lange,
*Complex Abelian Varieties*, 2nd ed., §1.2 (rational representation); `homPullback`. -/
def cp_weilOperator (σ : X ⟶ X) : Module.End ℚ (HQ X 1) :=
  LinearMap.id + (2 : ℚ) • homPullback σ 1

example (σ : X ⟶ X) (x : HQ X 1) :
    cp_weilOperator X σ x = x + (2 : ℚ) • homPullback σ 1 x := rfl

/-- The Weil action with operator `cp_weilOperator X σ`, for a group endomorphism `σ` of an
abelian `X`. The relation `J² = -3` is the argument `hsq`; preservation of the Hodge pieces is
`spec_homPullback_hodgePiece_one`, which holds for every homomorphism.
Source: `HodgeBlocks.WeilAction`; Birkenhake–Lange, §1.2 and Theorem 1.4.1;
`spec_homPullback_hodgePiece_one`. -/
def cp_weilAction [GrpObj X] (σ : X ⟶ X) [IsMonHom σ]
    (hsq : cp_weilOperator X σ ∘ₗ cp_weilOperator X σ = (-3 : ℚ) • LinearMap.id) :
    letI := (finiteBetti_abelian X).finite 1
    HodgeBlocks.WeilAction (abelianWeightOneHodgeStructure X) 3 :=
  letI := (finiteBetti_abelian X).finite 1
  { J := cp_weilOperator X σ
    J_sq := hsq
    preserves := by
      intro pq
      rintro _ ⟨x, hx, rfl⟩
      simp only [cp_weilOperator, LinearMap.baseChange_add, LinearMap.baseChange_smul,
        LinearMap.baseChange_id, LinearMap.add_apply, LinearMap.id_apply,
        LinearMap.smul_apply]
      exact Submodule.add_mem _ hx (Submodule.smul_of_tower_mem _ _
        (spec_homPullback_hodgePiece_one σ pq (Submodule.mem_map_of_mem hx))) }

example [GrpObj X] (σ : X ⟶ X) [IsMonHom σ]
    (hsq : cp_weilOperator X σ ∘ₗ cp_weilOperator X σ = (-3 : ℚ) • LinearMap.id) :
    letI := (finiteBetti_abelian X).finite 1
    (cp_weilAction X σ hsq).J = cp_weilOperator X σ := rfl

end Operator

/-- The automorphism `ρ × ρ²` of `E ⊗ E`. The second factor is `Ē`: the same curve with the
conjugate action, since `ρ² = ρ⁻¹` when `1 + ρ + ρ² = 0`.
Source: G34 v1.5, Lemma 10.1 (`Y = E × Ē`). -/
def cp_conjAut (E : Over (Spec ↧ℂ)) (ρ : E ⟶ E) : E ⊗ E ⟶ E ⊗ E :=
  lift (fst E E ≫ ρ) (snd E E ≫ ρ ≫ ρ)

example (E : Over (Spec ↧ℂ)) (ρ : E ⟶ E) :
    cp_conjAut E ρ ≫ snd E E = snd E E ≫ ρ ≫ ρ := by
  simp [cp_conjAut]

/-- `cp_conjAut` is a group homomorphism when `ρ` is one: `lift` and composites of homomorphisms
are homomorphisms.
Source: Mathlib `IsMonHom (lift f g)`, `IsMonHom (f ≫ g)`, `IsMonHom (fst M N)`,
`IsMonHom (snd M N)`. -/
instance cp_conjAut_isMonHom (E : Over (Spec ↧ℂ)) [GrpObj E] [IsCommMonObj E] (ρ : E ⟶ E)
    [IsMonHom ρ] : IsMonHom (cp_conjAut E ρ) := by
  unfold cp_conjAut; infer_instance

example (E : Over (Spec ↧ℂ)) [GrpObj E] [IsCommMonObj E] : IsMonHom (cp_conjAut E (𝟙 E)) :=
  inferInstance

/-! ### A nondegenerate instance of `1 + σ + σ² = 0` on a scheme -/

section Rotation

variable {C : Type*} [Category C] [CartesianMonoidalCategory C] [BraidedCategory C]
  (B : C) [GrpObj B] [IsCommMonObj B]

/-- The order-three rotation `(x, y) ↦ (-y, x - y)` of `B × B`, for a commutative group object
`B`. It satisfies `1 + σ + σ² = 0` for every `B`, so the relation that the C3 statements assume
is met by `E × E` for every elliptic curve `E`, not only by curves with complex multiplication.
Source: Birkenhake–Lange, *Complex Abelian Varieties*, 2nd ed., §1.2 (`M₂(ℤ)` acting on `E²`);
Mathlib `MonObj.mul_comp`, `MonObj.comp_mul`, `GrpObj.comp_inv`. -/
def cp_rotation : B ⊗ B ⟶ B ⊗ B := lift (snd B B)⁻¹ (fst B B * (snd B B)⁻¹)

/-- The rotation is a group homomorphism: `lift`, products and inverses of homomorphisms into a
commutative group object are homomorphisms.
Source: Mathlib `IsMonHom (lift f g)`, `IsMonHom μ[M]` for commutative `M`, `IsMonHom f⁻¹`. -/
instance cp_rotation_isMonHom : IsMonHom (cp_rotation B) := by
  have : IsMonHom (fst B B * (snd B B)⁻¹) := by rw [Hom.mul_def]; infer_instance
  unfold cp_rotation; infer_instance

/-- `1 + σ + σ² = 0` for the rotation, in the group `B ⊗ B ⟶ B ⊗ B`. -/
theorem cp_rotation_relation :
    𝟙 (B ⊗ B) * cp_rotation B * (cp_rotation B ≫ cp_rotation B) = 1 := by
  apply CartesianMonoidalCategory.hom_ext <;>
    simp [MonObj.mul_comp, MonObj.comp_mul, cp_rotation, GrpObj.comp_inv, mul_comm,
      mul_left_comm]

/-- The rotation is not the identity once `B` has a point other than the unit. -/
theorem cp_rotation_ne_id (P : 𝟙_ C ⟶ B) (hP : P ≠ 1) : cp_rotation B ≠ 𝟙 (B ⊗ B) := by
  intro h
  have h1 : lift P 1 ≫ cp_rotation B ≫ fst B B = lift P 1 ≫ fst B B := by
    rw [h, Category.id_comp]
  simp [cp_rotation, GrpObj.comp_inv] at h1
  exact hP h1.symm

end Rotation

/-- Nondegeneracy at the level of schemes: the cubic `Curves.E` of the curves track gives an
integral, smooth, projective group object `E ⊗ E` with an endomorphism `σ ≠ 𝟙` satisfying
`1 + σ + σ² = 0`. -/
example : ∃ (X : Over (Spec ↧ℂ)) (_ : GrpObj X) (σ : X ⟶ X), IsIntegral X.left ∧
    Smooth X.hom ∧ IsProjective X.hom ∧ 𝟙 X * σ * (σ ≫ σ) = 1 ∧ σ ≠ 𝟙 X := by
  obtain ⟨e, he⟩ := Curves.exists_isCubicPointEquiv
  obtain ⟨m, hm⟩ := Curves.exists_add_morphism e he
  obtain ⟨i, hi⟩ := Curves.exists_neg_morphism e he
  obtain ⟨G, -, hG, -⟩ := Curves.exists_grpObj e he m hm i hi
  let := G
  have : IsCommMonObj Curves.E :=
    isCommMonObj_of_complexSelfProductIntegral Curves.E
      (complexSelfProductIntegral_of_isIntegral Curves.E)
  refine ⟨Curves.E ⊗ Curves.E, inferInstance, cp_rotation Curves.E, inferInstance,
    inferInstance, inferInstance, cp_rotation_relation Curves.E,
    cp_rotation_ne_id Curves.E (Over.homMk Curves.finitePoint Curves.finitePoint_over) ?_⟩
  rw [← MonObj.one_eq_one]
  exact (Curves.finitePoint_ne_one e he (hG ▸ hm)).1

/-! ### C2 and C4: classes on the product -/

section Product

variable (A Y : Over (Spec ↧ℂ)) [IsIntegral A.left] [Smooth A.hom] [IsProjective A.hom]
  [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]

/-- The product polarization class `pr_A^* η_A + pr_Y^* η_Y ∈ H²(A × Y; ℚ)`.
Source: Birkenhake–Lange, *Complex Abelian Varieties*, 2nd ed., §5.2 (the product
polarization); `homPullback`. -/
def cp_productPol (ηA : HQ A 2) (ηY : HQ Y 2) : HQ (A ⊗ Y) 2 :=
  homPullback (fst A Y) 2 ηA + homPullback (snd A Y) 2 ηY

example (ηA : HQ A 2) :
    cp_productPol A Y ηA 0 = homPullback (fst A Y) 2 ηA := by
  simp [cp_productPol]

/-- The Künneth map `⊕_{i+j=n} H^i(A; ℚ) ⊗ H^j(Y; ℚ) → H^n(A × Y; ℚ)`, `a ⊗ b ↦ pr_A^* a ∪ pr_Y^* b`,
for the cup product `cupProductOf (A ⊗ Y)`.
Source: Hatcher, *Algebraic Topology*, Theorem 3.15 and §3.2 (cross product); `homPullback`,
`cupProductOf`. -/
def cp_kunnethMap (n : ℕ) :
    (⨁ p : Finset.HasAntidiagonal.antidiagonal n, HQ A p.1.1 ⊗[ℚ] HQ Y p.1.2) →ₗ[ℚ] HQ (A ⊗ Y) n :=
  DirectSum.toModule ℚ _ _ fun p => TensorProduct.lift
    (((cupProductOf (A ⊗ Y)).cup (Finset.HasAntidiagonal.mem_antidiagonal.mp p.2)).compl₁₂
      (homPullback (fst A Y) p.1.1) (homPullback (snd A Y) p.1.2))

example (n : ℕ) : cp_kunnethMap A Y n 0 = 0 := map_zero _

end Product

/-- The class of a nonzero rational in `ℚˣ ⧸ Nm(ℚ(√-3)ˣ)`, the codomain of `weilDatumClass`.
Source: van Geemen, *An introduction to the Hodge conjecture for abelian varieties*, LNM 1594,
§5; `HermitianForm.normSubgroup`. -/
def cp_ratClass (q : ℚ) (hq : q ≠ 0) : ℚˣ ⧸ normSubgroup (QuadraticAlgebra ℚ (-3) 0) :=
  ((Units.mk0 q hq : ℚˣ) : ℚˣ ⧸ normSubgroup (QuadraticAlgebra ℚ (-3) 0))

/-- `[-2]` is F-1569's `classNegTwo`, which is not the trivial class. -/
example : cp_ratClass (-2) (by norm_num) = classNegTwo := rfl

example : cp_ratClass (-2) (by norm_num) ≠ 1 := class_neg_two_ne_one

/-! ### Rank-two linear algebra: the hypotheses are not degenerate -/

/-- The order-three rotation `R` of `ℚ²` satisfies `1 + R + R² = 0`, is not the identity, and
`J = 1 + 2R` squares to `-3`. This is the action of `ρ^*` on `H¹` of an elliptic curve with an
automorphism of order three, in a rational basis. -/
example :
    let R : Matrix (Fin 2) (Fin 2) ℚ := !![0, -1; 1, -1]
    1 + R + R ^ 2 = 0 ∧ R ≠ 1 ∧ (1 + 2 • R) ^ 2 = (-3 : ℚ) • 1 := by
  refine ⟨?_, ?_, ?_⟩
  · ext i j; fin_cases i <;> fin_cases j <;> simp [sq]
  · intro h
    have := congrFun (congrFun h 0) 0
    simp at this
  · ext i j; fin_cases i <;> fin_cases j <;>
      simp [sq, Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply] <;> norm_num

end HodgeLean.Foundations.Program
