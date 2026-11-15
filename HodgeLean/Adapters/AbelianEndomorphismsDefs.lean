import HodgeLean.Adapters.LatticeClassHQDefs

/-! # Endomorphisms of an abelian variety and their action on `HQ X 1`: definitions (FROZEN)

* `AbelianEnd X`: the endomorphisms of a commutative group object `X` of `Over (Spec ℂ)`, i.e.
  morphisms `X ⟶ X` that are morphisms of monoid objects. They form a ring: addition is the
  pointwise product through the group law of `X` (Mathlib's `Hom.commGroup`), multiplication is
  composition (`f * g = g ≫ f`, so `f * g` is `f ∘ g`), and `(n : AbelianEnd X)` is
  multiplication by `n`, `𝟙 X ^ n` in the group `X ⟶ X`.
* `AbelianEnd0 X = ℚ ⊗[ℤ] AbelianEnd X`, with Mathlib's tensor-product ring structure.
* `complexPointPullback X f n`: pullback along the continuous map `X(ℂ) → X(ℂ)` of a morphism
  `f : X ⟶ X`, on singular cohomology of `X(ℂ)`, carried to `HQ X n` along the S7 comparison
  `cupComparison X n`. The comparison is a rescaling of U1 by one scalar in every degree, so the
  conjugate does not depend on that scalar. Nothing here compares it with a pullback of sheaf
  cohomology.
* `abelianEndAction X f`: the case `n = 1` for `f : AbelianEnd X`.

No statement here says the action is additive, multiplicative, injective or Hodge-preserving.
HC no distance; AV milestone no distance.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint TopologicalSpace
open CategoryTheory.CartesianMonoidalCategory
open AlgebraicTopology.Singular
open scoped CategoryTheory.MonObj TensorProduct
open HodgeLean.RealDefs HodgeLean.Foundations

namespace HodgeLean.Adapters

/-- The endomorphisms of a group object `X` of `Over (Spec ℂ)`: morphisms `X ⟶ X` of monoid
objects. For an abelian variety these are the endomorphisms of `X` as an abelian variety.
Source: Mumford, *Abelian Varieties*, §19 (`End(X)`); Milne, *Abelian Varieties* (2008), §I.10;
Mathlib `IsMonHom`. -/
@[ext]
structure AbelianEnd (X : Over (Spec ↧ℂ)) [GrpObj X] where
  /-- The underlying morphism of schemes over `Spec ℂ`. -/
  hom : X ⟶ X
  /-- It respects the unit and the multiplication of `X`. -/
  isMonHom : IsMonHom hom

attribute [instance] AbelianEnd.isMonHom

example (X : Over (Spec ↧ℂ)) [GrpObj X] : AbelianEnd X := ⟨𝟙 X, inferInstance⟩

namespace AbelianEnd

variable {X : Over (Spec ↧ℂ)} [GrpObj X] [IsCommMonObj X]

private theorem isMonHom_mul (f g : X ⟶ X) [IsMonHom f] [IsMonHom g] : IsMonHom (f * g) := by
  rw [Hom.mul_def]
  infer_instance

private theorem isMonHom_one : IsMonHom (1 : X ⟶ X) := by
  rw [Hom.one_def]
  infer_instance

instance : Zero (AbelianEnd X) := ⟨⟨1, isMonHom_one⟩⟩
instance : One (AbelianEnd X) := ⟨⟨𝟙 X, inferInstance⟩⟩
instance : Add (AbelianEnd X) := ⟨fun f g => ⟨f.hom * g.hom, isMonHom_mul _ _⟩⟩
instance : Neg (AbelianEnd X) := ⟨fun f => ⟨f.hom⁻¹, inferInstance⟩⟩
instance : Sub (AbelianEnd X) := ⟨fun f g => f + -g⟩
instance : Mul (AbelianEnd X) := ⟨fun f g => ⟨g.hom ≫ f.hom, inferInstance⟩⟩
instance : SMul ℕ (AbelianEnd X) := ⟨nsmulRec⟩
instance : SMul ℤ (AbelianEnd X) := ⟨zsmulRec⟩
instance : Pow (AbelianEnd X) ℕ := ⟨fun f n => npowRec n f⟩
instance : NatCast (AbelianEnd X) := ⟨fun n => n • (1 : AbelianEnd X)⟩
instance : IntCast (AbelianEnd X) := ⟨fun n => n • (1 : AbelianEnd X)⟩

@[simp] theorem zero_hom : (0 : AbelianEnd X).hom = 1 := rfl
omit [IsCommMonObj X] in
@[simp] theorem one_hom : (1 : AbelianEnd X).hom = 𝟙 X := rfl
@[simp] theorem add_hom (f g : AbelianEnd X) : (f + g).hom = f.hom * g.hom := rfl
@[simp] theorem neg_hom (f : AbelianEnd X) : (-f).hom = f.hom⁻¹ := rfl
omit [IsCommMonObj X] in
@[simp] theorem mul_hom (f g : AbelianEnd X) : (f * g).hom = g.hom ≫ f.hom := rfl

/-- The additive endomorphism of the group `X ⟶ X` given by composing with `f` on the right;
injective in `f` and compatible with every ring operation. -/
private def toEnd (f : AbelianEnd X) : AddMonoid.End (Additive (X ⟶ X)) where
  toFun g := Additive.ofMul (g.toMul ≫ f.hom)
  map_zero' := by
    change Additive.ofMul ((1 : X ⟶ X) ≫ f.hom) = Additive.ofMul 1
    rw [MonObj.one_comp]
  map_add' g g' := by
    change Additive.ofMul ((g.toMul * g'.toMul) ≫ f.hom) = Additive.ofMul _
    rw [MonObj.mul_comp]
    rfl

private theorem toEnd_apply (f : AbelianEnd X) (g : Additive (X ⟶ X)) :
    toEnd f g = Additive.ofMul (g.toMul ≫ f.hom) := rfl

private theorem toEnd_injective : Function.Injective (toEnd (X := X)) := by
  intro f g h
  have := DFunLike.congr_fun h (Additive.ofMul (𝟙 X))
  simp only [toEnd_apply, toMul_ofMul, Category.id_comp, EmbeddingLike.apply_eq_iff_eq] at this
  exact AbelianEnd.ext this

private theorem toEnd_zero : toEnd (0 : AbelianEnd X) = 0 := by
  refine AddMonoidHom.ext fun g => ?_
  change Additive.ofMul (g.toMul ≫ (1 : X ⟶ X)) = Additive.ofMul (1 : X ⟶ X)
  rw [MonObj.comp_one]

private theorem toEnd_one : toEnd (1 : AbelianEnd X) = 1 := by
  refine AddMonoidHom.ext fun g => ?_
  change Additive.ofMul (g.toMul ≫ 𝟙 X) = g
  rw [Category.comp_id]
  rfl

private theorem toEnd_add (f g : AbelianEnd X) : toEnd (f + g) = toEnd f + toEnd g := by
  refine AddMonoidHom.ext fun h => ?_
  change Additive.ofMul (h.toMul ≫ (f.hom * g.hom)) = Additive.ofMul _
  rw [MonObj.comp_mul]
  rfl

private theorem toEnd_neg (f : AbelianEnd X) : toEnd (-f) = -toEnd f := by
  refine AddMonoidHom.ext fun h => ?_
  change Additive.ofMul (h.toMul ≫ f.hom⁻¹) = Additive.ofMul _
  rw [GrpObj.comp_inv]
  rfl

private theorem toEnd_mul (f g : AbelianEnd X) : toEnd (f * g) = toEnd f * toEnd g := by
  refine AddMonoidHom.ext fun h => ?_
  change Additive.ofMul (h.toMul ≫ g.hom ≫ f.hom) = Additive.ofMul ((h.toMul ≫ g.hom) ≫ f.hom)
  rw [Category.assoc]

private theorem toEnd_sub (f g : AbelianEnd X) : toEnd (f - g) = toEnd f - toEnd g := by
  change toEnd (f + -g) = _
  rw [toEnd_add, toEnd_neg, sub_eq_add_neg]

private theorem toEnd_nsmul (n : ℕ) (f : AbelianEnd X) : toEnd (n • f) = n • toEnd f := by
  induction n with
  | zero => exact toEnd_zero
  | succ n ih =>
    change toEnd (n • f + f) = _
    rw [toEnd_add, ih, succ_nsmul]

private theorem toEnd_zsmul (n : ℤ) (f : AbelianEnd X) : toEnd (n • f) = n • toEnd f := by
  cases n with
  | ofNat n =>
    change toEnd (n • f) = _
    rw [toEnd_nsmul, Int.ofNat_eq_natCast, natCast_zsmul]
  | negSucc n =>
    change toEnd (-((n + 1) • f)) = _
    rw [toEnd_neg, toEnd_nsmul, negSucc_zsmul]

private theorem toEnd_npow (f : AbelianEnd X) (n : ℕ) : toEnd (f ^ n) = toEnd f ^ n := by
  induction n with
  | zero => exact toEnd_one
  | succ n ih =>
    change toEnd (f ^ n * f) = _
    rw [toEnd_mul, ih, pow_succ]

private theorem toEnd_natCast (n : ℕ) : toEnd (n : AbelianEnd X) = n := by
  change toEnd (n • (1 : AbelianEnd X)) = _
  rw [toEnd_nsmul, toEnd_one, nsmul_one]

private theorem toEnd_intCast (n : ℤ) : toEnd (n : AbelianEnd X) = n := by
  change toEnd (n • (1 : AbelianEnd X)) = _
  rw [toEnd_zsmul, toEnd_one, zsmul_one]

/-- The ring of endomorphisms of a commutative group object: addition through the group law,
multiplication by composition.
Source: Mumford, *Abelian Varieties*, §19; Milne, *Abelian Varieties* (2008), §I.10; Mathlib
`Hom.commGroup`, `MonObj.mul_comp`, `MonObj.comp_mul`. -/
instance : Ring (AbelianEnd X) :=
  toEnd_injective.ring _ toEnd_zero toEnd_one toEnd_add toEnd_mul toEnd_neg toEnd_sub
    toEnd_nsmul toEnd_zsmul toEnd_npow toEnd_natCast toEnd_intCast

example (f g : AbelianEnd X) : (f + g).hom = lift f.hom g.hom ≫ μ := rfl

/-- `(n : AbelianEnd X)` is multiplication by `n`: the `n`-th power of `𝟙 X` in the group
`X ⟶ X`. -/
example (n : ℕ) : (n : AbelianEnd X).hom = 𝟙 X ^ n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change ((n : AbelianEnd X) + 1).hom = _
    rw [add_hom, ih, pow_succ, one_hom]

end AbelianEnd

/-- The rational endomorphism algebra `End⁰(X) = ℚ ⊗ End(X)`.
Source: Mumford, *Abelian Varieties*, §19 (`End⁰(X) = End(X) ⊗_ℤ ℚ`); Mathlib
`Algebra.TensorProduct`. -/
abbrev AbelianEnd0 (X : Over (Spec ↧ℂ)) [GrpObj X] [IsCommMonObj X] : Type :=
  ℚ ⊗[ℤ] AbelianEnd X

example (X : Over (Spec ↧ℂ)) [GrpObj X] [IsCommMonObj X] : Algebra ℚ (AbelianEnd0 X) :=
  inferInstance

-- For an abelian variety, commutativity is derived, not assumed.
example (X : Over (Spec ↧ℂ)) [GrpObj X] [IsIntegral X.left] [Smooth X.hom]
    [IsProjective X.hom] : IsCommMonObj X :=
  isCommMonObj_of_complexSelfProductIntegral X (complexSelfProductIntegral_of_isIntegral X)

variable (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]

/-- Pullback along the map of complex points of `f : X ⟶ X`, on singular cohomology of `X(ℂ)`,
carried to `HQ X n` along `cupComparison X n`.
Source: Hatcher, *Algebraic Topology*, §3.1 (induced maps on cohomology); upstream
`Point.continuousMap` at `2ead713`; S7 `cupComparison`. -/
def complexPointPullback (f : X ⟶ X) (n : ℕ) : Module.End ℚ (HQ X n) :=
  (cupComparison X n).symm.toLinearMap ∘ₗ
    cohomologyMap ℚ n (TopCat.ofHom (Point.continuousMap f)) ∘ₗ (cupComparison X n).toLinearMap

example (f : X ⟶ X) (n : ℕ) (x : HQ X n) :
    cupComparison X n (complexPointPullback X f n x) =
      cohomologyMap ℚ n (TopCat.ofHom (Point.continuousMap f)) (cupComparison X n x) := by
  simp [complexPointPullback]

/-- The action of an endomorphism on `HQ X 1` by pullback.
Source: Birkenhake–Lange, *Complex Abelian Varieties*, 2nd ed., §1.2 (rational representation);
`complexPointPullback`. -/
def abelianEndAction [GrpObj X] (f : AbelianEnd X) : Module.End ℚ (HQ X 1) :=
  complexPointPullback X f.hom 1

example [GrpObj X] (f : AbelianEnd X) :
    abelianEndAction X f = complexPointPullback X f.hom 1 := rfl

end HodgeLean.Adapters
