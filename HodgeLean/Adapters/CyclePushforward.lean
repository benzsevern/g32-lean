import HodgeLean.Adapters.CyclePushforwardProofs

/-!
# Quasi-compact cycle pushforward extending Fulton's proper pushforward (FROZEN SPEC)

Track A1, stage 1. The objects are constructed in
`HodgeLean.Foundations.Mathlib.CyclePushforwardCore` and `HodgeLean.Adapters.CyclePushforwardDefs`:
`a1p_degree f x` is the residue-field degree `[κ(x) : κ(f x)]` (`0` when infinite), and
`a1p_pushforward f`, the quasi-compact cycle pushforward extending Fulton's proper pushforward, is
the linear extension `[x] ↦ a1p_degree f x • [f x]` on Mathlib's carrier `AlgebraicCycle X R`, for
quasi-compact `f` (proper maps are quasi-compact). The external product of prime cycles is the
generic point of `pr₁⁻¹(Z) ∩ pr₂⁻¹(W)` in `gagam_product X Y`.

Twelve statements (S1–S12) and four witness theorems on the affine line `𝔸¹ = Spec ℂ[X]` over
`ℂ`, at its generic point `η`: the squaring map `X ↦ X²` has degree `2`
(`a1p_degree_square_eq_two`), the contraction `𝔸¹ → Spec ℂ` has degree `0`
(`a1p_degree_contraction_eq_zero`), and the two sides of `a1p_degree_pos_iff` at these maps, the
squaring map keeping the dimension of `closure {η}` (`a1p_height_square_generic`) and the
contraction dropping it (`a1p_height_contraction_generic`).

Claimed, for cycles only: the value on a prime cycle, additivity and left scalar linearity,
`id_* = id`, `(f ≫ g)_* = g_* ∘ f_*` with the tower law for degrees, and over `ℂ` with schemes
locally of finite type: positivity of the degree exactly when the dimension of `closure {x}` does
not drop, preservation of the dimension grading (`Order.height`, the dimension of
`closure {x}`), agreement with Mathlib's `AlgebraicCycle.map` weighted by `Order.height`,
irreducibility of the product set, and `(f × g)_* (α × β) = f_* α × g_* β`.

Not claimed: anything about rational equivalence, Chow groups, cohomology or cycle classes;
the codimension grading is not used here (on an equidimensional `X` of dimension `n`,
dimension `k` is codimension `n - k`, and `Order.coheight` is the codimension used by
`ccm3_cycleClass`). HC no distance; AV milestone no distance.
-/

noncomputable section
open CategoryTheory AlgebraicGeometry
open scoped MonoidalCategory

namespace HodgeLean.Adapters

universe u

/-- Witness: the squaring map `𝔸¹ → 𝔸¹`, `X ↦ X²`, of `Spec ℂ[X]` over `ℂ`, has degree `2` at the
generic point `η`: `κ(η) = ℂ(X)` over `κ(sq η) = ℂ(X²)`, and `X` has minimal polynomial
`T² - X²`.
Source: Fulton, *Intersection Theory*, second edition, §1.4, definition of `deg(V/W)`;
Lang, *Algebra*, revised third edition, V, §1 (degree of a simple algebraic extension). -/
theorem a1p_degree_square_eq_two :
    a1p_degree a1p_squareMap.left a1p_affineLineGeneric = 2 :=
  a1p_degree_square_eq_two_aux

example : 0 < a1p_degree a1p_squareMap.left a1p_affineLineGeneric := by
  rw [a1p_degree_square_eq_two]
  norm_num

/-- Witness: the contraction `𝔸¹ → Spec ℂ` (`toUnit` of `Spec ℂ[X]` in `Over (Spec ℂ)`) has
degree `0` at the generic point `η`: `κ(η) = ℂ(X)` is infinite over `ℂ`.
Source: Fulton, *Intersection Theory*, second edition, §1.4 (`deg(V/W) = 0` when
`dim W < dim V`); Mathlib, `Module.finrank_of_not_finite`. -/
theorem a1p_degree_contraction_eq_zero :
    a1p_degree (CartesianMonoidalCategory.toUnit a1p_affineLine).left a1p_affineLineGeneric = 0 :=
  a1p_degree_contraction_eq_zero_aux

example : ¬ 0 < a1p_degree (CartesianMonoidalCategory.toUnit a1p_affineLine).left
    a1p_affineLineGeneric := by
  rw [a1p_degree_contraction_eq_zero]
  exact lt_irrefl 0

/-- Witness, positive side of S7: the squaring map keeps the dimension of `closure {η}`; both
`η` and `sq η = η` have height `1` in `Spec ℂ[X]`.
Source: Hartshorne, *Algebraic Geometry*, II, Exercise 3.20 (dimension is the transcendence
degree of the function field); the squaring map is dominant, so it sends `η` to `η`. -/
theorem a1p_height_square_generic :
    Order.height (a1p_squareMap.left a1p_affineLineGeneric) =
      Order.height a1p_affineLineGeneric :=
  a1p_height_square_generic_aux

example : IsMin (a1p_squareMap.left a1p_affineLineGeneric) ↔ IsMin a1p_affineLineGeneric := by
  rw [← Order.height_eq_zero, ← Order.height_eq_zero, a1p_height_square_generic]

/-- Witness, zero side of S7: the contraction drops the dimension of `closure {η}`; the point of
`Spec ℂ` has height `0` and `η` has height `1`.
Source: Hartshorne, *Algebraic Geometry*, II, Exercise 3.20; `ℂ[X]` has Krull dimension `1`. -/
theorem a1p_height_contraction_generic :
    Order.height ((CartesianMonoidalCategory.toUnit a1p_affineLine).left a1p_affineLineGeneric) ≠
      Order.height a1p_affineLineGeneric :=
  a1p_height_contraction_generic_aux

example : Order.height a1p_affineLineGeneric ≠ 0 := fun h =>
  a1p_height_contraction_generic <| h ▸ Order.height_eq_zero.2 fun _ _ =>
    (Subsingleton.elim (α := (Spec ↧ℂ : Scheme)) _ _).le

/-- The pushforward of a prime cycle `r [closure {x}]` is `r · deg [closure {f x}]`.
Source: Fulton, *Intersection Theory*, second edition, §1.4, `f_*[V] = deg(V/f(V)) [f(V)]`. -/
theorem a1p_pushforward_single {X Y : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f]
    {R : Type*} [Semiring R] [DecidableEq X] [DecidableEq Y] (x : X) (r : R) :
    a1p_pushforward f (Function.locallyFinsuppWithin.single x r) =
      Function.locallyFinsuppWithin.single (f x) (r * (a1p_degree f x : R)) :=
  a1p_pushforward_single_aux f x r

/-- The squaring map pushes the generic cycle `[𝔸¹]` to `2 [𝔸¹]`. -/
example [DecidableEq a1p_affineLine.left] :
    a1p_pushforward a1p_squareMap.left
        (Function.locallyFinsuppWithin.single a1p_affineLineGeneric (1 : ℤ)) =
      Function.locallyFinsuppWithin.single (a1p_squareMap.left a1p_affineLineGeneric) 2 := by
  rw [a1p_pushforward_single, a1p_degree_square_eq_two]
  norm_num

/-- Pushforward is additive.
Source: Fulton, *Intersection Theory*, second edition, §1.4, linear extension of `f_*`. -/
theorem a1p_pushforward_add {X Y : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f]
    {R : Type*} [Semiring R] (c d : AlgebraicCycle X R) :
    a1p_pushforward f (c + d) = a1p_pushforward f c + a1p_pushforward f d :=
  a1p_pushforward_add_aux f c d

example (c d : AlgebraicCycle (Spec ↧ℂ) ℤ) :
    a1p_pushforward (Spec.map (CommRingCat.ofHom (algebraMap ℝ ℂ))) (c + d) =
      a1p_pushforward (Spec.map (CommRingCat.ofHom (algebraMap ℝ ℂ))) c +
        a1p_pushforward (Spec.map (CommRingCat.ofHom (algebraMap ℝ ℂ))) d :=
  a1p_pushforward_add _ c d

/-- Pushforward commutes with multiplying every coefficient by `r` on the left.
Source: Fulton, *Intersection Theory*, second edition, §1.4, linear extension of `f_*`. -/
theorem a1p_pushforward_mul {X Y : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f]
    {R : Type*} [Semiring R] (r : R) (c : AlgebraicCycle X R) :
    a1p_pushforward f (c.mapRange (r * ·) (mul_zero r)) =
      (a1p_pushforward f c).mapRange (r * ·) (mul_zero r) :=
  a1p_pushforward_mul_aux f r c

example (c : AlgebraicCycle (Spec ↧ℂ) ℚ) :
    a1p_pushforward (Spec.map (CommRingCat.ofHom (algebraMap ℝ ℂ)))
        (c.mapRange ((-2 : ℚ) * ·) (mul_zero _)) =
      (a1p_pushforward (Spec.map (CommRingCat.ofHom (algebraMap ℝ ℂ))) c).mapRange
        ((-2 : ℚ) * ·) (mul_zero _) :=
  a1p_pushforward_mul _ _ c

/-- `id_* = id`.
Source: Fulton, *Intersection Theory*, second edition, §1.4. -/
theorem a1p_pushforward_id {X : Scheme.{u}} {R : Type*} [Semiring R]
    (c : AlgebraicCycle X R) :
    a1p_pushforward (𝟙 X) c = c :=
  a1p_pushforward_id_aux c

example (c : AlgebraicCycle (Spec ↧ℂ) ℤ) : a1p_pushforward (𝟙 (Spec ↧ℂ)) c = c :=
  a1p_pushforward_id c

/-- Degrees are multiplicative in towers, the infinite case included (both sides `0`).
Source: Fulton, *Intersection Theory*, second edition, §1.4, proof of Theorem 1.4;
Mathlib, `Module.finrank_mul_finrank`. -/
theorem a1p_degree_comp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (x : X) :
    a1p_degree (f ≫ g) x = a1p_degree g (f x) * a1p_degree f x :=
  a1p_degree_comp_aux f g x

/-- `ℚ ⊆ ℝ ⊆ ℂ`; the first step is infinite, so the composite degree is the degree of `ℂ` over
`ℝ` times `0`. -/
example : a1p_degree (Spec.map (CommRingCat.ofHom (algebraMap ℝ ℂ)) ≫
      Spec.map (CommRingCat.ofHom (algebraMap ℚ ℝ))) (IsLocalRing.closedPoint ℂ) =
    a1p_degree (Spec.map (CommRingCat.ofHom (algebraMap ℚ ℝ)))
        ((Spec.map (CommRingCat.ofHom (algebraMap ℝ ℂ))) (IsLocalRing.closedPoint ℂ)) *
      a1p_degree (Spec.map (CommRingCat.ofHom (algebraMap ℝ ℂ))) (IsLocalRing.closedPoint ℂ) :=
  a1p_degree_comp _ _ _

/-- The squaring map twice: the composite degree at `η` is twice the degree of the second
squaring at `sq η`. -/
example : a1p_degree (a1p_squareMap.left ≫ a1p_squareMap.left) a1p_affineLineGeneric =
    a1p_degree a1p_squareMap.left (a1p_squareMap.left a1p_affineLineGeneric) * 2 := by
  rw [a1p_degree_comp, a1p_degree_square_eq_two]

/-- `(f ≫ g)_* = g_* ∘ f_*`.
Source: Fulton, *Intersection Theory*, second edition, §1.4, Theorem 1.4 (functoriality). -/
theorem a1p_pushforward_comp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [QuasiCompact f] [QuasiCompact g] {R : Type*} [Semiring R] (c : AlgebraicCycle X R) :
    a1p_pushforward (f ≫ g) c = a1p_pushforward g (a1p_pushforward f c) :=
  a1p_pushforward_comp_aux f g c

example (c : AlgebraicCycle (Spec ↧ℂ) ℤ) :
    a1p_pushforward (Spec.map (CommRingCat.ofHom (algebraMap ℝ ℂ)) ≫
        Spec.map (CommRingCat.ofHom (algebraMap ℚ ℝ))) c =
      a1p_pushforward (Spec.map (CommRingCat.ofHom (algebraMap ℚ ℝ)))
        (a1p_pushforward (Spec.map (CommRingCat.ofHom (algebraMap ℝ ℂ))) c) :=
  a1p_pushforward_comp _ _ c

/-- Over `ℂ`, for schemes locally of finite type, the degree at `x` is positive exactly when
`f` restricted to `Z = closure {x}` is generically finite, i.e. when `dim f(Z) = dim Z`
(`Order.height` of a point is the dimension of its closure).
Source: Fulton, *Intersection Theory*, second edition, §1.4 (`deg(V/W) = 0` when
`dim W < dim V`); Hartshorne, *Algebraic Geometry*, Exercise II.3.20 (dimension is the
transcendence degree of the function field). -/
theorem a1p_degree_pos_iff {X Y : Over (Spec ↧ℂ)} (f : X ⟶ Y)
    [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom] (x : X.left) :
    0 < a1p_degree f.left x ↔ Order.height (f.left x) = Order.height x :=
  a1p_degree_pos_iff_aux f x

/-- The positive case of S7 at the squaring map agrees with `a1p_degree_square_eq_two`. -/
example : 0 < a1p_degree a1p_squareMap.left a1p_affineLineGeneric :=
  (a1p_degree_pos_iff a1p_squareMap a1p_affineLineGeneric).2 a1p_height_square_generic

/-- The zero case of S7 at the contraction agrees with `a1p_degree_contraction_eq_zero`. -/
example : a1p_degree (CartesianMonoidalCategory.toUnit a1p_affineLine).left
    a1p_affineLineGeneric = 0 :=
  Nat.eq_zero_of_not_pos fun h =>
    a1p_height_contraction_generic ((a1p_degree_pos_iff _ a1p_affineLineGeneric).1 h)

/-- Pushforward preserves the dimension grading: a cycle of pure dimension `k` is sent to a
cycle of pure dimension `k`.
Source: Fulton, *Intersection Theory*, second edition, §1.4, `f_* : Z_k X → Z_k Y`. -/
theorem a1p_pushforward_preserves_dimension {X Y : Over (Spec ↧ℂ)} (f : X ⟶ Y)
    [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom] [QuasiCompact f.left]
    {R : Type*} [Semiring R] (k : ℕ∞) (c : AlgebraicCycle X.left R)
    (hc : ∀ x, c x ≠ 0 → Order.height x = k) (y : Y.left)
    (hy : a1p_pushforward f.left c y ≠ 0) :
    Order.height y = k :=
  a1p_pushforward_preserves_dimension_aux f k c hc y hy

example (X : Over (Spec ↧ℂ)) [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    (k : ℕ∞) (c : AlgebraicCycle X.left ℤ) (hc : ∀ x, c x ≠ 0 → Order.height x = k)
    (y : (𝟙_ (Over (Spec ↧ℂ))).left)
    (hy : haveI : QuasiCompact (CartesianMonoidalCategory.toUnit X).left :=
      inferInstanceAs (QuasiCompact X.hom)
      a1p_pushforward (CartesianMonoidalCategory.toUnit X).left c y ≠ 0) :
    Order.height y = k :=
  haveI : QuasiCompact (CartesianMonoidalCategory.toUnit X).left :=
    inferInstanceAs (QuasiCompact X.hom)
  a1p_pushforward_preserves_dimension _ k c hc y hy

/-- Over `ℂ`, for schemes locally of finite type, the pushforward is Mathlib's
`AlgebraicCycle.map` with the dimension weight `Order.height` on both sides.
Source: Stacks Project, Tag 02R4; Mathlib, `AlgebraicGeometry.AlgebraicCycle.map`. -/
theorem a1p_pushforward_eq_map {X Y : Over (Spec ↧ℂ)} (f : X ⟶ Y)
    [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom] [QuasiCompact f.left]
    {R : Type*} [Semiring R] (c : AlgebraicCycle X.left R) :
    a1p_pushforward f.left c = AlgebraicCycle.map f.left Order.height Order.height c :=
  a1p_pushforward_eq_map_aux f c

example (c : AlgebraicCycle (𝟙_ (Over (Spec ↧ℂ))).left ℤ) :
    a1p_pushforward (Over.Hom.left (𝟙 (𝟙_ (Over (Spec ↧ℂ))))) c =
      AlgebraicCycle.map (Over.Hom.left (𝟙 (𝟙_ (Over (Spec ↧ℂ))))) Order.height Order.height c :=
  a1p_pushforward_eq_map _ c

/-- Over `ℂ`, for `X` and `Y` locally of finite type, `pr₁⁻¹(closure {z}) ∩ pr₂⁻¹(closure {w})`
is irreducible: it underlies `Z ×_ℂ W`, which is integral.
Source: Stacks Project, Tag 05P3 (`isIntegral_pullback_of_isAlgClosed`); Fulton,
*Intersection Theory*, second edition, §1.10. -/
theorem a1p_productSet_isIrreducible (X Y : Over (Spec ↧ℂ))
    [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom] (z : X.left) (w : Y.left) :
    IsIrreducible (a1p_productSet X Y z w) :=
  a1p_productSet_isIrreducible_aux X Y z w

example (z w : (𝟙_ (Over (Spec ↧ℂ))).left) :
    IsIrreducible (a1p_productSet (𝟙_ (Over (Spec ↧ℂ))) (𝟙_ (Over (Spec ↧ℂ))) z w) :=
  a1p_productSet_isIrreducible _ _ z w

/-- On prime cycles, `(f × g)_* [Z × W] = deg(Z/f(Z)) deg(W/g(W)) [f(Z) × g(W)]`.
Source: Fulton, *Intersection Theory*, second edition, §1.10, Proposition 1.10. -/
theorem a1p_pushforward_externalProduct_prime {X Y X' Y' : Over (Spec ↧ℂ)}
    (f : X ⟶ X') (g : Y ⟶ Y')
    [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    [LocallyOfFiniteType X'.hom] [LocallyOfFiniteType Y'.hom]
    [QuasiCompact f.left] [QuasiCompact g.left] {R : Type*} [Semiring R]
    (z : X.left) (w : Y.left) :
    a1p_pushforward (f ⊗ₘ g).left (a1p_externalProduct X Y z w R) =
      (a1p_externalProduct X' Y' (f.left z) (g.left w) R).mapRange
        (((a1p_degree f.left z * a1p_degree g.left w : ℕ) : R) * ·) (mul_zero _) :=
  a1p_pushforward_externalProduct_prime_aux f g z w

example (X : Over (Spec ↧ℂ)) [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    (z w : X.left) :
    haveI : QuasiCompact (CartesianMonoidalCategory.toUnit X).left :=
      inferInstanceAs (QuasiCompact X.hom)
    a1p_pushforward (CartesianMonoidalCategory.toUnit X ⊗ₘ CartesianMonoidalCategory.toUnit X).left
        (a1p_externalProduct X X z w ℤ) =
      (a1p_externalProduct _ _ ((CartesianMonoidalCategory.toUnit X).left z)
          ((CartesianMonoidalCategory.toUnit X).left w) ℤ).mapRange
        (((a1p_degree (CartesianMonoidalCategory.toUnit X).left z *
          a1p_degree (CartesianMonoidalCategory.toUnit X).left w : ℕ) : ℤ) * ·) (mul_zero _) :=
  haveI : QuasiCompact (CartesianMonoidalCategory.toUnit X).left :=
    inferInstanceAs (QuasiCompact X.hom)
  a1p_pushforward_externalProduct_prime _ _ z w

/-- `(f × g)_* (α × β) = f_* α × g_* β` for cycles on schemes of finite type over `ℂ`.
Source: Fulton, *Intersection Theory*, second edition, §1.10, Proposition 1.10. -/
theorem a1p_pushforward_externalProduct {X Y X' Y' : Over (Spec ↧ℂ)}
    (f : X ⟶ X') (g : Y ⟶ Y')
    [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    [LocallyOfFiniteType X'.hom] [LocallyOfFiniteType Y'.hom]
    [CompactSpace X.left] [CompactSpace Y.left]
    [QuasiCompact f.left] [QuasiCompact g.left] {R : Type*} [Semiring R]
    (α : AlgebraicCycle X.left R) (β : AlgebraicCycle Y.left R) :
    a1p_pushforward (f ⊗ₘ g).left (a1p_externalProductCycle α β) =
      a1p_externalProductCycle (a1p_pushforward f.left α) (a1p_pushforward g.left β) :=
  a1p_pushforward_externalProduct_aux f g α β

example (X Y : Over (Spec ↧ℂ)) [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    [CompactSpace X.left] [CompactSpace Y.left]
    (α : AlgebraicCycle X.left ℚ) (β : AlgebraicCycle Y.left ℚ) :
    a1p_pushforward (𝟙 X ⊗ₘ 𝟙 Y).left (a1p_externalProductCycle α β) =
      a1p_externalProductCycle (a1p_pushforward (Over.Hom.left (𝟙 X)) α)
        (a1p_pushforward (Over.Hom.left (𝟙 Y)) β) :=
  a1p_pushforward_externalProduct _ _ α β

end HodgeLean.Adapters
