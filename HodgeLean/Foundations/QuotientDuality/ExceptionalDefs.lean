import HodgeLean.Foundations.QuotientDuality.OrientationDefs
import Mathlib.Algebra.Colimit.Module
import Mathlib.Topology.Maps.Proper.Basic

/-! # Exceptional preimages and neighborhood base change

The comparison starts from the directed limit of actual preimage cohomology.
HC no distance; AV milestone no distance.
-/

noncomputable section
open CategoryTheory AlgebraicTopology.Singular TopologicalSpace
namespace HodgeLean.Foundations.QuotientDuality

/-- Neighborhoods ordered by shrinking.
Source: Bredon, Sheaf Theory, II.10, continuity. -/
abbrev exceptionalIndex (Y : TopCat.{0}) (y : Y) :=
  OrderDual {U : Opens Y // y ∈ U}
example : Nonempty (exceptionalIndex (TopCat.of Unit) ()) := ⟨⟨⊤, trivial⟩⟩

/-- Actual inverse image of a subset, with its subspace topology.
Source: Bredon, Sheaf Theory, II.10. -/
abbrev exceptionalSpace {X Y : TopCat.{0}} (f : X ⟶ Y) (S : Set Y) :=
  TopCat.of {x : X // f x ∈ S}
example : exceptionalSpace (𝟙 (TopCat.of Unit)) {()} =
    TopCat.of {x : Unit // x ∈ ({()} : Set Unit)} := rfl

/-- Inclusion of nested actual preimages.
Source: Hatcher, Algebraic Topology, section 3.1, restriction. -/
def exceptionalInclusion {X Y : TopCat.{0}} (f : X ⟶ Y)
    {S T : Set Y} (h : S ⊆ T) : exceptionalSpace f S ⟶ exceptionalSpace f T :=
  TopCat.ofHom ⟨fun x => ⟨x.1, h x.2⟩, continuous_subtype_val.subtype_mk _⟩
example {X Y : TopCat.{0}} (f : X ⟶ Y) (S : Set Y) (x : exceptionalSpace f S) :
    exceptionalInclusion f (Set.Subset.refl S) x = x := rfl

/-- Restriction along shrinking neighborhoods.
Source: Bredon, Sheaf Theory, II.10. -/
def exceptionalRestriction {X Y : TopCat.{0}} (f : X ⟶ Y) (y : Y) (n : ℕ)
    (U V : exceptionalIndex Y y) (h : U ≤ V) :
    Cohomology ℚ (exceptionalSpace f U.val) n →ₗ[ℚ]
      Cohomology ℚ (exceptionalSpace f V.val) n :=
  cohomologyMap ℚ n (exceptionalInclusion f h)
example {X Y : TopCat.{0}} (f : X ⟶ Y) (y : Y) (n : ℕ)
    (U V : exceptionalIndex Y y) (h : U ≤ V) :
    exceptionalRestriction f y n U V h 0 = 0 := map_zero _

open Classical in
/-- Neighborhood cohomology germ in every natural degree.
Source: Bredon, Sheaf Theory, II.10, tautness. -/
abbrev exceptionalGerm {X Y : TopCat.{0}} (f : X ⟶ Y) (y : Y) (n : ℕ) :=
  Module.DirectLimit (fun U : exceptionalIndex Y y => Cohomology ℚ (exceptionalSpace f U.val) n)
    (exceptionalRestriction f y n)
example {X Y : TopCat.{0}} (f : X ⟶ Y) (y : Y) : Nonempty (exceptionalGerm f y 0) := ⟨0⟩

/-- The canonical comparison to the cohomology of the actual fibre.
Source: Bredon, Sheaf Theory, II.10, continuity and proper base change. -/
def exceptionalBaseChange {X Y : TopCat.{0}} (f : X ⟶ Y) (y : Y) (n : ℕ) :
    exceptionalGerm f y n →ₗ[ℚ] Cohomology ℚ (exceptionalSpace f {y}) n := by
  classical
  refine Module.DirectLimit.lift ℚ (exceptionalIndex Y y) _ _
    (fun U : exceptionalIndex Y y => cohomologyMap ℚ n (exceptionalInclusion f (by
      intro z hz; rcases hz with rfl; exact U.property))) ?_
  intro U V h a
  change (cohomologyMap ℚ n _).comp (cohomologyMap ℚ n _) a = _
  rw [← cohomologyMap_comp]
  rfl
example {X Y : TopCat.{0}} (f : X ⟶ Y) (y : Y) (n : ℕ) :
    exceptionalBaseChange f y n 0 = 0 := map_zero _

/-- Restriction of a map over the base to an exceptional preimage.
Source: Hatcher, Algebraic Topology, section 3.1, naturality. -/
def exceptionalDeck {X Y : TopCat.{0}} (f : X ⟶ Y) (e : X ⟶ X)
    (he : e ≫ f = f) (S : Set Y) : exceptionalSpace f S ⟶ exceptionalSpace f S :=
  TopCat.ofHom ⟨fun x => ⟨e x.1, by
    have h : f (e x.1) = f x.1 := congrArg (fun k : X ⟶ Y => k x.1) he
    rw [h]; exact x.2⟩,
    (e.hom.continuous.comp continuous_subtype_val).subtype_mk _⟩
example {X Y : TopCat.{0}} (f : X ⟶ Y) (S : Set Y) (x : exceptionalSpace f S) :
    exceptionalDeck f (𝟙 X) (by simp) S x = x := rfl

/-- The induced germ endomorphism of the actual map over the base.
Source: Bredon, Sheaf Theory, II.10, naturality of continuity. -/
def exceptionalGermDeck {X Y : TopCat.{0}} (f : X ⟶ Y) (y : Y) (n : ℕ)
    (e : X ⟶ X) (he : e ≫ f = f) : exceptionalGerm f y n →ₗ[ℚ] exceptionalGerm f y n := by
  classical
  refine Module.DirectLimit.map
    (fun U => cohomologyMap ℚ n (exceptionalDeck f e he U.val)) ?_
  intro U V h
  unfold exceptionalRestriction
  rw [← cohomologyMap_comp, ← cohomologyMap_comp]
  rfl
example {X Y : TopCat.{0}} (f : X ⟶ Y) (y : Y) (n : ℕ)
    (e : X ⟶ X) (he : e ≫ f = f) : exceptionalGermDeck f y n e he 0 = 0 := map_zero _

/-- Character averaging with inverse weights and rational normalization.
Source: Serre, Linear Representations of Finite Groups, Chapter 2, character projectors. -/
def exceptionalProjector (G : Type) [Group G] [Fintype G]
    {V : Type*} [AddCommGroup V] [Module ℚ V]
    (χ : G →* ℚˣ) (D : G → V →ₗ[ℚ] V) : V →ₗ[ℚ] V :=
  (Fintype.card G : ℚ)⁻¹ • ∑ g : G, ((χ g)⁻¹ : ℚˣ).val • D g
example : exceptionalProjector Unit (1 : Unit →* ℚˣ)
    (fun _ => LinearMap.id : Unit → ℚ →ₗ[ℚ] ℚ) (3 : ℚ) = (3 : ℚ) := by
  simp [exceptionalProjector]

end HodgeLean.Foundations.QuotientDuality
