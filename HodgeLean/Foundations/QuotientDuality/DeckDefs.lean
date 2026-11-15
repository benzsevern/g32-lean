import HodgeLean.Foundations.Topology.RationalSheafComparisonDefs
import Mathlib.Topology.Algebra.ConstMulAction
import Mathlib.RepresentationTheory.Invariants

/-! # Actual deck maps on rational singular cochains

Inverse action maps give covariant group actions after contravariant pullback.
The quotient is the orbit space with its quotient topology.
HC no distance; AV milestone no distance.
-/

noncomputable section
open CategoryTheory AlgebraicTopology.Singular
namespace HodgeLean.Foundations.QuotientDuality

/-- The topological orbit space of the specified action.
Source: Bredon, Introduction to Compact Transformation Groups, I.3. -/
abbrev orbitSpace (G : Type) [Group G] (X : TopCat.{0}) [MulAction G X] : TopCat.{0} :=
  TopCat.of (Quotient (MulAction.orbitRel G X))

example : orbitSpace Unit (TopCat.of Unit) = TopCat.of (Quotient (MulAction.orbitRel Unit Unit)) := rfl

/-- The actual continuous quotient map.
Source: Bredon, Introduction to Compact Transformation Groups, I.3. -/
def orbitMap (G : Type) [Group G] (X : TopCat.{0}) [MulAction G X] :
    X ⟶ orbitSpace G X :=
  TopCat.ofHom ⟨Quotient.mk _, continuous_quot_mk⟩

example : Function.Surjective (orbitMap Unit (TopCat.of Unit)) := Quotient.mk_surjective

/-- The inverse-action continuous map, fixing the pullback convention.
Source: Hatcher, Algebraic Topology, 3.1; Serre, Linear Representations, I.1. -/
def deckMap (G : Type) [Group G] (X : TopCat.{0}) [MulAction G X]
    [ContinuousConstSMul G X] (g : G) : X ⟶ X :=
  TopCat.ofHom ⟨fun x => g⁻¹ • x, continuous_const_smul _⟩

example : deckMap Unit (TopCat.of Unit) () () = () := rfl

/-- Pullback of actual rational singular cochains by the inverse action.
Source: Hatcher, Algebraic Topology, 3.1, singular cochains and functoriality. -/
def deckCochain (G : Type) [Group G] (X : TopCat.{0}) [MulAction G X]
    [ContinuousConstSMul G X] (g : G) :
    SingularCochainComplex ℚ X ⟶ SingularCochainComplex ℚ X :=
  singularCochainComplexMap ℚ (deckMap G X g)

example : deckCochain Unit (TopCat.of Unit) () =
    singularCochainComplexMap ℚ (𝟙 (TopCat.of Unit)) := rfl

/-- The induced action on actual rational singular cohomology.
Source: Hatcher, Algebraic Topology, 3.1; Serre, Linear Representations, I.1. -/
def deckRepresentation (G : Type) [Group G] (X : TopCat.{0}) [MulAction G X]
    [ContinuousConstSMul G X] (n : ℕ) : Representation ℚ G (Cohomology ℚ X n) where
  toFun g := cohomologyMap ℚ n (deckMap G X g)
  map_one' := by
    have h : deckMap G X 1 = 𝟙 X := by ext x; simp [deckMap]
    rw [h, cohomologyMap_id]; rfl
  map_mul' g h := by
    have he : deckMap G X (g * h) = deckMap G X g ≫ deckMap G X h := by
      ext x
      simp [deckMap, mul_smul]
    rw [he, cohomologyMap_comp]; rfl

example (v : Cohomology ℚ (TopCat.of Unit) 0) :
    deckRepresentation Unit (TopCat.of Unit) 0 1 v = v := by
  change cohomologyMap ℚ 0 (𝟙 (TopCat.of Unit)) v = v
  rw [cohomologyMap_id]; rfl

end HodgeLean.Foundations.QuotientDuality
