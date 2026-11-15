import HodgeLean.Foundations.QuotientDuality.ExceptionalDefs
import HodgeLean.Foundations.QuotientDuality.Defs
import Other.AlgebraicTopology.Singular.SupportNaturality
import Other.AlgebraicTopology.Singular.EmptySubspace

/-! # Quotient duality and exceptional fibres

Actual singular groups, support pullbacks and neighborhood limits are retained.
HC no distance; AV milestone no distance.
-/

noncomputable section
open CategoryTheory TopologicalSpace AlgebraicTopology.Singular
namespace HodgeLean.Foundations.QuotientDuality

/-- Inverse-degree scaling of the actual invariant restriction.
Source: Serre, Linear Representations of Finite Groups, section 1.2 (averaging); Hatcher, section 3.3. -/
def normalizedFixedPairing {G V W : Type*} [Group G]
    [AddCommGroup V] [Module ℚ V] [AddCommGroup W] [Module ℚ W]
    (d : ℕ) (ρ : G →* (V ≃ₗ[ℚ] V)) (σ : G →* (W ≃ₗ[ℚ] W))
    (B : V →ₗ[ℚ] Module.Dual ℚ W) : fixed ρ →ₗ[ℚ] Module.Dual ℚ (fixed σ) :=
  (d : ℚ)⁻¹ • fixedPairing ρ σ B
example : normalizedFixedPairing (2 : ℕ) (1 : Unit →* (ℚ ≃ₗ[ℚ] ℚ))
    (1 : Unit →* (ℚ ≃ₗ[ℚ] ℚ)) (LinearMap.mul ℚ ℚ)
    ⟨(3 : ℚ), by intro g; rfl⟩ ⟨(4 : ℚ), by intro g; rfl⟩ = (6 : ℚ) := by
  norm_num [normalizedFixedPairing, fixedPairing]

/-- Ordinary restriction between actual chart preimages.
Source: Hatcher, section 3.1, contravariant functoriality. -/
def chartRestriction {X Y : TopCat.{0}} (f : X ⟶ Y) {S T : Set Y}
    (h : S ⊆ T) (n : ℕ) := cohomologyMap ℚ n (exceptionalInclusion f h)
example {X Y : TopCat.{0}} (f : X ⟶ Y) {S T : Set Y} (h : S ⊆ T) (n : ℕ) :
    chartRestriction f h n (0 : Cohomology ℚ (exceptionalSpace f T) n) = 0 := map_zero _

/-- Supported restriction retains the actual inverse-image support.
Source: Hatcher, section 3.1, relative singular cochains. -/
def chartSupportedRestriction {X Y : TopCat.{0}} (f : X ⟶ Y) {S T : Set Y}
    (h : S ⊆ T) (Z : Set (exceptionalSpace f T)) (n : ℕ) :=
  cohomologyWithSupportMap ℚ n (exceptionalInclusion f h) Z
example {X Y : TopCat.{0}} (f : X ⟶ Y) {S T : Set Y} (h : S ⊆ T)
    (Z : Set (exceptionalSpace f T)) (n : ℕ) :
    chartSupportedRestriction f h Z n (0 : CohomologyWithSupport ℚ _ Z n) = 0 := map_zero _

/-- Inclusion of the actual fibre into a neighborhood preimage.
Source: Bredon, Sheaf Theory, II.10. -/
def fibreInclusion {X Y : TopCat.{0}} (f : X ⟶ Y) (y : Y)
    (U : exceptionalIndex Y y) : exceptionalSpace f {y} ⟶ exceptionalSpace f U.val :=
  exceptionalInclusion f (by intro z hz; rcases hz with rfl; exact U.property)
example {X Y : TopCat.{0}} (f : X ⟶ Y) (y : Y)
    (U : exceptionalIndex Y y) (x : exceptionalSpace f {y}) :
    (fibreInclusion f y U x).val = x.val := rfl

/-- Restriction of the actual orbit map to a subset of its target.
Source: Bredon, Introduction to Compact Transformation Groups, I.3. -/
def orbitChartMap (G : Type) [Group G] (X : TopCat.{0}) [MulAction G X]
    (S : Set (orbitSpace G X)) :
    exceptionalSpace (orbitMap G X) S ⟶ TopCat.of S :=
  TopCat.ofHom ⟨fun x => ⟨orbitMap G X x.val, x.property⟩,
    ((orbitMap G X).hom.continuous.comp continuous_subtype_val).subtype_mk _⟩
example (G : Type) [Group G] (X : TopCat.{0}) [MulAction G X]
    (S : Set (orbitSpace G X)) (x : exceptionalSpace (orbitMap G X) S) :
    (orbitChartMap G X S x).val = orbitMap G X x.val := rfl

/-- Inclusion of actual target chart subspaces.
Source: Hatcher, Algebraic Topology, section 3.1, restriction. -/
def chartInclusion {Y : TopCat.{0}} {S T : Set Y} (h : S ⊆ T) :
    TopCat.of S ⟶ TopCat.of T :=
  TopCat.ofHom ⟨fun x => ⟨x.val, h x.property⟩, continuous_subtype_val.subtype_mk _⟩
example {Y : TopCat.{0}} {S T : Set Y} (h : S ⊆ T) (x : S) :
    (chartInclusion h x).val = x.val := rfl

end HodgeLean.Foundations.QuotientDuality
