import Mathlib.CategoryTheory.Abelian.Exact
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.CategoryTheory.Limits.Shapes.BinaryBiproducts

/-! # Arrows of a positive normal presentation

The relation, quotient, free directions and divisor projection are actual
categorical constructions. They apply in particular to sheaves of modules.
Source: Fulton, Intersection Theory, §B.7; Hartshorne, II.8.
HC no distance; AV milestone no distance. -/

noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace HodgeLean.Foundations.NormalPresentation

variable {C : Type*} [Category* C] [Abelian C] {L A E N : C}

/-- Relation with its distinguished divisor coordinate and retained free directions.
Source: Fulton, Intersection Theory, §B.7, presentations by vector bundles. -/
def relation (a : L ⟶ A) (b : L ⟶ E) : L ⟶ A ⊞ E := biprod.lift a b

/-- The actual quotient by the relation, without a chosen splitting.
Source: Hartshorne, II.5, cokernels of module sheaves; Fulton, §B.7. -/
abbrev quotient (a : L ⟶ A) (b : L ⟶ E) : C := cokernel (relation a b)

/-- The quotient arrow from the positive ambient presentation.
Source: Hartshorne, II.5, cokernels of module sheaves. -/
def projection (a : L ⟶ A) (b : L ⟶ E) : A ⊞ E ⟶ quotient a b :=
  cokernel.π (relation a b)

/-- Inclusion of the retained free directions into the quotient.
Source: Fulton, §B.7, elementary presentations. -/
def freeArrow (a : L ⟶ A) (b : L ⟶ E) : E ⟶ quotient a b :=
  biprod.inr ≫ projection a b

/-- Projection to the cokernel of the distinguished coordinate; identified with the
pushed divisor structure module after the ideal-sequence comparison.
Source: Hartshorne, II.6, the ideal sequence of an effective Cartier divisor. -/
def divisorArrow (a : L ⟶ A) (b : L ⟶ E) : quotient a b ⟶ cokernel a :=
  cokernel.desc (relation a b) (biprod.fst ≫ cokernel.π a) (by
    simp [relation])

/-- The canonical positive sequence, retaining its relation arrow.
Source: Fulton, §B.7, resolutions by vector bundles. -/
def canonical (a : L ⟶ A) (b : L ⟶ E) : ShortComplex C :=
  ShortComplex.mk (relation a b) (projection a b) (cokernel.condition _)

/-- The elementary sequence with the specified free directions and divisor.
Source: Fulton, §B.7, elementary modification; Hartshorne, II.6. -/
def elementary (a : L ⟶ A) (b : L ⟶ E) : ShortComplex C :=
  ShortComplex.mk (freeArrow a b) (divisorArrow a b) (by
    dsimp only [freeArrow, divisorArrow, projection]
    rw [Category.assoc, cokernel.π_desc, ← Category.assoc, biprod.inr_fst, zero_comp])

/-- The unique quotient comparison induced by a map killing the actual relation.
Source: Hartshorne, II.5, universal property of a cokernel. -/
def comparison (a : L ⟶ A) (b : L ⟶ E) (q : A ⊞ E ⟶ N)
    (h : relation a b ≫ q = 0) : quotient a b ⟶ N :=
  cokernel.desc (relation a b) q h

end HodgeLean.Foundations.NormalPresentation
