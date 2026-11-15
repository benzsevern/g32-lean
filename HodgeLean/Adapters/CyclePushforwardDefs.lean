import HodgeLean.Adapters.GagaMapsDefs
import HodgeLean.Foundations.Mathlib.CyclePushforwardCore

/-! # Quasi-compact cycle pushforward extending Fulton's proper pushforward, by construction

The degree `a1p_degree` and the quasi-compact cycle pushforward extending Fulton's proper
pushforward, `a1p_pushforward`, are the Mathlib-only definitions of
`HodgeLean.Foundations.Mathlib.CyclePushforwardCore`. This file adds the external product of
cycles and the witness objects: the affine line `Spec ℂ[X]` over `ℂ`, its generic point and the
squaring map `X ↦ X²`. The external
product of prime cycles is the generic point of the closed set `pr₁⁻¹(Z) ∩ pr₂⁻¹(W)` in
`gagam_product X Y`, with coefficient `1`. Every statement about these objects is in
`HodgeLean.Adapters.CyclePushforward`. HC no distance; AV milestone no distance.
-/

noncomputable section
open CategoryTheory AlgebraicGeometry Polynomial
open scoped MonoidalCategory

namespace HodgeLean.Adapters

universe u

/-- The product map of two quasi-compact maps over `Spec ℂ` is quasi-compact.
Source: Mathlib, `MorphismProperty.pullbackMap` for quasi-compact morphisms
(stable under base change and composition). -/
instance a1p_tensorHom_quasiCompact {X Y X' Y' : Over (Spec ↧ℂ)} (f : X ⟶ X') (g : Y ⟶ Y')
    [QuasiCompact f.left] [QuasiCompact g.left] : QuasiCompact (f ⊗ₘ g).left := by
  rw [Over.tensorHom_left]
  exact MorphismProperty.pullbackMap (P := @QuasiCompact) (inferInstanceAs (QuasiCompact f.left))
    (inferInstanceAs (QuasiCompact g.left)) (Over.w f).symm (Over.w g).symm

example {X Y : Over (Spec ↧ℂ)} : QuasiCompact (𝟙 X ⊗ₘ 𝟙 Y).left := inferInstance

/-- The underlying set of `Z ×_ℂ W` inside `gagam_product X Y`, for `Z = closure {z}` and
`W = closure {w}`: the points lying over `Z` and over `W`.
Source: Fulton, *Intersection Theory*, second edition, §1.10, the product `V × W`. -/
def a1p_productSet (X Y : Over (Spec ↧ℂ)) (z : X.left) (w : Y.left) :
    Set (gagam_product X Y).left :=
  (CartesianMonoidalCategory.fst X Y).left ⁻¹' closure {z} ∩
    (CartesianMonoidalCategory.snd X Y).left ⁻¹' closure {w}

example (X Y : Over (Spec ↧ℂ)) (z : X.left) (w : Y.left) (p : (gagam_product X Y).left) :
    p ∈ a1p_productSet X Y z w ↔
      (CartesianMonoidalCategory.fst X Y).left p ∈ closure {z} ∧
        (CartesianMonoidalCategory.snd X Y).left p ∈ closure {w} :=
  Iff.rfl

/-- External product of the prime cycles `[closure {z}]` and `[closure {w}]`: the generic point
of `a1p_productSet X Y z w` with coefficient `1`, and `0` if that set is not irreducible.
Over `ℂ` with `X`, `Y` locally of finite type the set is irreducible
(`a1p_productSet_isIrreducible` in the spec file).
Source: Fulton, *Intersection Theory*, second edition, §1.10, `[V] × [W] = [V × W]`. -/
def a1p_externalProduct (X Y : Over (Spec ↧ℂ)) (z : X.left) (w : Y.left) (R : Type*)
    [Semiring R] : AlgebraicCycle (gagam_product X Y).left R := by
  classical
  exact if h : IsIrreducible (a1p_productSet X Y z w) then
    Function.locallyFinsuppWithin.single h.genericPoint 1
  else 0

example (X Y : Over (Spec ↧ℂ)) (z : X.left) (w : Y.left) :
    AlgebraicCycle (gagam_product X Y).left ℚ := a1p_externalProduct X Y z w ℚ

/-- Bilinear extension of the external product: `α × β = ∑ α z β w [closure {z} × closure {w}]`.
On quasi-compact `X` and `Y` the supports are finite and the sum is the honest finite sum.
Source: Fulton, *Intersection Theory*, second edition, §1.10, exterior product of cycles. -/
def a1p_externalProductCycle {X Y : Over (Spec ↧ℂ)} {R : Type*} [Semiring R]
    (α : AlgebraicCycle X.left R) (β : AlgebraicCycle Y.left R) :
    AlgebraicCycle (gagam_product X Y).left R :=
  ∑ᶠ z : X.left, ∑ᶠ w : Y.left,
    (a1p_externalProduct X Y z w R).mapRange (α z * β w * ·) (mul_zero _)

example {X Y : Over (Spec ↧ℂ)} (α : AlgebraicCycle X.left ℚ) (β : AlgebraicCycle Y.left ℚ) :
    AlgebraicCycle (gagam_product X Y).left ℚ := a1p_externalProductCycle α β

/-- The affine line `𝔸¹ = Spec ℂ[X]` over `ℂ`, with structure map `Spec` of `algebraMap ℂ ℂ[X]`.
Source: Hartshorne, *Algebraic Geometry*, II.2, the affine line `Spec k[x]`. -/
def a1p_affineLine : Over (Spec ↧ℂ) :=
  Over.mk (Spec.map (CommRingCat.ofHom (algebraMap ℂ ℂ[X])))

example : a1p_affineLine.left = Spec (.of ℂ[X]) := rfl

/-- The affine line is of finite type over `ℂ`.
Source: Mathlib, `HasRingHomProperty.Spec_iff` and `Algebra.FiniteType` of `ℂ[X]` over `ℂ`. -/
instance a1p_affineLine_locallyOfFiniteType : LocallyOfFiniteType a1p_affineLine.hom := by
  change LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (algebraMap ℂ ℂ[X])))
  rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType), CommRingCat.hom_ofHom,
    RingHom.finiteType_algebraMap]
  infer_instance

example : LocallyOfFiniteType a1p_affineLine.hom := inferInstance

/-- The point `Spec ℂ`, the monoidal unit of `Over (Spec ℂ)`, is of finite type over `ℂ`.
Source: Mathlib, `LocallyOfFiniteType` holds for identities. -/
instance a1p_unit_locallyOfFiniteType : LocallyOfFiniteType (𝟙_ (Over (Spec ↧ℂ))).hom := by
  dsimp
  infer_instance

example : (𝟙_ (Over (Spec ↧ℂ))).left = Spec ↧ℂ := rfl

/-- The affine line is irreducible: `ℂ[X]` is a domain.
Source: Mathlib, `IsIntegral (Spec R)` for a domain `R`. -/
instance a1p_affineLine_irreducibleSpace : IrreducibleSpace a1p_affineLine.left :=
  inferInstanceAs (IrreducibleSpace (Spec (.of ℂ[X])))

example : IrreducibleSpace a1p_affineLine.left := inferInstance

/-- The generic point `η` of the affine line, the zero ideal of `ℂ[X]`; `κ(η) = ℂ(X)`.
Source: Hartshorne, *Algebraic Geometry*, II, Exercise 2.9 (generic points). -/
def a1p_affineLineGeneric : a1p_affineLine.left := genericPoint a1p_affineLine.left

example : closure {a1p_affineLineGeneric} = Set.univ := genericPoint_spec _ |>.def

/-- The squaring map `𝔸¹ → 𝔸¹` over `ℂ`: `Spec` of the `ℂ`-algebra map `ℂ[X] → ℂ[X]`, `X ↦ X²`.
Source: Fulton, *Intersection Theory*, second edition, §1.4, definition of `deg(V/W)`; the
extension `ℂ(X) ⊇ ℂ(X²)` has degree `2`. -/
def a1p_squareMap : a1p_affineLine ⟶ a1p_affineLine :=
  Over.homMk (Spec.map (CommRingCat.ofHom (aeval (X ^ 2 : ℂ[X])).toRingHom)) (by
    simp only [a1p_affineLine, Over.mk_hom, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    ext c
    simp)

example : a1p_squareMap.left = Spec.map (CommRingCat.ofHom (aeval (X ^ 2 : ℂ[X])).toRingHom) :=
  rfl

/-- The squaring map is quasi-compact: it is a morphism of affine schemes.
Source: Mathlib, `IsAffineHom` of `Spec.map` and `QuasiCompact` of affine morphisms. -/
instance a1p_squareMap_quasiCompact : QuasiCompact a1p_squareMap.left :=
  inferInstanceAs (QuasiCompact (Spec.map (CommRingCat.ofHom
    (aeval (R := ℂ) (X ^ 2 : ℂ[X])).toRingHom)))

example : QuasiCompact a1p_squareMap.left := inferInstance

end HodgeLean.Adapters
