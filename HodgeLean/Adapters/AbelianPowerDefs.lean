import HodgeLean.Adapters.AbelianCMDataDefs

/-! # The power `A^r`, stage G3 (part 1) of the Powers flagship: definitions (FROZEN)

Definitions for `AbelianPower`, stage G3 part 1 of formalizing PW v0.3, Theorem 4.2 (`thm:gen`).
For an object `A` of `Over (Spec ℂ)`:

* `g3_power A r`: the `r`-fold iterated cartesian product `A ⊗ (A ⊗ (⋯ ⊗ 𝟙_))` in
  `Over (Spec ℂ)`, for Mathlib's cartesian monoidal structure (`Over.cartesianMonoidalCategory`,
  made an instance in `Mathlib/AlgebraicGeometry/Pullbacks.lean`): the tensor product is the fibre
  product over `Spec ℂ` and the unit `𝟙_` is `Spec ℂ` itself, `Over.mk (𝟙 (Spec ℂ))`.
* `g3_grpObj A r`: the group-object structure on `g3_power A r`, Mathlib's `GrpObj` instances on
  `𝟙_` and on `G ⊗ H`, for a group object `A`.
* `g3_proj A r i : g3_power A r ⟶ A`: the `i`-th projection, `fst` at `i = 0` and `snd ≫ p_i`
  at `i + 1` (the shape of Mathlib's `Limits.extendFan`).
* `g3_incl A r i : A ⟶ g3_power A r`: the `i`-th inclusion, `lift (𝟙 A) 1` at `i = 0` and
  `lift 1 s_i` at `i + 1`, where `1` is the constant map to the identity point.

No definition asserts a group-homomorphism, biproduct, commutativity or scheme property; those
are the statements of `AbelianPower.lean`. HC no distance; AV milestone no distance.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry MonoidalCategory
open scoped CategoryTheory.MonObj

namespace HodgeLean.Adapters

variable (A : Over (Spec ↧ℂ))

/-- **The power `A^r`**: the `r`-fold iterated cartesian product in `Over (Spec ℂ)`,
`A^0 = 𝟙_ = Spec ℂ` and `A^(r+1) = A ⊗ A^r = A ×_ℂ A^r`.
Source: Mumford, *Abelian Varieties*, §4 (products of abelian varieties); Mathlib
`Over.cartesianMonoidalCategory`, `Over.tensorObj_left` (the tensor product in `Over X` is the
fibre product over `X`). -/
def g3_power : ℕ → Over (Spec ↧ℂ)
  | 0 => 𝟙_ (Over (Spec ↧ℂ))
  | n + 1 => A ⊗ g3_power n

/-- `A^0` is the point `Spec ℂ` over itself. -/
example : g3_power A 0 = Over.mk (𝟙 (Spec ↧ℂ)) := rfl

/-- `A^(r+1)` is the fibre product `A ×_ℂ A^r`. -/
example (n : ℕ) :
    (g3_power A (n + 1)).left = Limits.pullback A.hom (g3_power A n).hom := rfl

/-- **The group structure on `A^r`**: Mathlib's group objects `𝟙_` (`GrpObj.instTensorUnit`) and
`G ⊗ H` (`GrpObj.tensorObj.instTensorObj`, componentwise), by recursion on `r`.
Source: Mumford, *Abelian Varieties*, §4; Mathlib `GrpObj.instTensorUnit`,
`GrpObj.tensorObj.instTensorObj`. -/
instance g3_grpObj [GrpObj A] : ∀ n, GrpObj (g3_power A n)
  | 0 => GrpObj.instTensorUnit
  | n + 1 => letI := g3_grpObj n; GrpObj.tensorObj.instTensorObj

example [GrpObj A] (n : ℕ) :
    g3_grpObj A (n + 1) =
      (letI := g3_grpObj A n; GrpObj.tensorObj.instTensorObj (G := A) (H := g3_power A n)) :=
  rfl

/-- **The projections `p_i : A^r ⟶ A`**: `p_0 = fst` and `p_(i+1) = snd ≫ p_i` on
`A^(r+1) = A ⊗ A^r`.
Source: Mathlib `Limits.extendFan` (`Fin.cases c₂.fst (c₂.snd ≫ c₁.π i)`),
`CartesianMonoidalCategory.fst`, `CartesianMonoidalCategory.snd`. -/
def g3_proj : ∀ n, Fin n → (g3_power A n ⟶ A)
  | 0 => Fin.elim0
  | n + 1 => Fin.cases (CartesianMonoidalCategory.fst A (g3_power A n))
      fun i => CartesianMonoidalCategory.snd A (g3_power A n) ≫ g3_proj n i

example (n : ℕ) : g3_proj A (n + 1) 0 = CartesianMonoidalCategory.fst A (g3_power A n) := rfl

example (n : ℕ) (i : Fin n) :
    g3_proj A (n + 1) i.succ = CartesianMonoidalCategory.snd A (g3_power A n) ≫ g3_proj A n i :=
  rfl

/-- **The inclusions `s_i : A ⟶ A^r`**: `s_0 = (𝟙, 1)` and `s_(i+1) = (1, s_i)` into
`A^(r+1) = A ⊗ A^r`, where `1` is the constant map to the identity point (the unit of the monoid
`X ⟶ G`).
Source: Mac Lane, *Categories for the Working Mathematician*, §VIII.2 (biproduct inclusions);
Mathlib `CartesianMonoidalCategory.lift`, `MonObj.Hom.monoid`. -/
def g3_incl [GrpObj A] : ∀ n, Fin n → (A ⟶ g3_power A n)
  | 0 => Fin.elim0
  | n + 1 => Fin.cases (CartesianMonoidalCategory.lift (𝟙 A) 1)
      fun i => CartesianMonoidalCategory.lift 1 (g3_incl n i)

example [GrpObj A] (n : ℕ) :
    g3_incl A (n + 1) 0 = CartesianMonoidalCategory.lift (𝟙 A) (1 : A ⟶ g3_power A n) := rfl

example [GrpObj A] (n : ℕ) (i : Fin n) :
    g3_incl A (n + 1) i.succ = CartesianMonoidalCategory.lift (1 : A ⟶ A) (g3_incl A n i) := rfl

end HodgeLean.Adapters
