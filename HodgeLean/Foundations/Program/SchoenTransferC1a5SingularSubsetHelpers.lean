import HodgeLean.Foundations.Program.SchoenTransferC1a5BinaryCoverHelpers

/-! Singular image subcomplexes of actual topological subspaces.
HC no distance; AV milestone no distance. -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits AlgebraicTopology.Singular
namespace HodgeLean.Foundations.Program

/-- Singular membership in a subspace image means containment of the continuous simplex image.
Source: the subspace topology and Mathlib TopCat.toSSetObjEquiv. -/
lemma c1a5_singular_subset_range_iff (X : TopCat.{0}) (U : Set X)
    (n : SimplexCategoryᵒᵖ) (x : (TopCat.toSSet.obj X).obj n) :
    x ∈ (SSet.Subcomplex.range
      (TopCat.toSSet.map (topologicalSubsetInclusion X U))).obj n ↔
      Set.range (X.toSSetObjEquiv n x) ⊆ U := by
  constructor
  · rintro ⟨y, rfl⟩ _ ⟨t, rfl⟩
    exact ((TopCat.of U).toSSetObjEquiv n y t).property
  · intro h
    let f : C(Convexity.StdSimplex ℝ (Fin (n.unop.len + 1)), TopCat.of U) :=
      ⟨fun t ↦ ⟨X.toSSetObjEquiv n x t, h ⟨t, rfl⟩⟩,
        (X.toSSetObjEquiv n x).continuous.subtype_mk _⟩
    refine ⟨((TopCat.of U).toSSetObjEquiv n).symm f, ?_⟩
    apply (X.toSSetObjEquiv n).injective
    ext t
    rfl

/-- Singular image subcomplexes preserve intersections of topological subspaces.
Source: the continuous simplex image characterization of subspace membership. -/
lemma c1a5_singular_subset_intersection (X : TopCat.{0}) (U V : Set X) :
    SSet.Subcomplex.range (TopCat.toSSet.map (topologicalSubsetInclusion X (U ∩ V))) =
      SSet.Subcomplex.range (TopCat.toSSet.map (topologicalSubsetInclusion X U)) ⊓
        SSet.Subcomplex.range (TopCat.toSSet.map (topologicalSubsetInclusion X V)) := by
  ext n x
  change x ∈ (SSet.Subcomplex.range
    (TopCat.toSSet.map (topologicalSubsetInclusion X (U ∩ V)))).obj n ↔
      x ∈ (SSet.Subcomplex.range
        (TopCat.toSSet.map (topologicalSubsetInclusion X U))).obj n ∧
      x ∈ (SSet.Subcomplex.range
        (TopCat.toSSet.map (topologicalSubsetInclusion X V))).obj n
  simp only [c1a5_singular_subset_range_iff, Set.subset_inter_iff]

/-- The actual singular simplicial set of a subspace identifies with its image subcomplex.
Source: Mathlib Subcomplex.toRange and preservation of monomorphisms by singular simplices. -/
def c1a5_singular_subset_iso (X : TopCat.{0}) (U : Set X) :
    TopCat.toSSet.obj (TopCat.of U) ≅
      SSet.Subcomplex.range (TopCat.toSSet.map (topologicalSubsetInclusion X U)) := by
  have : Mono (topologicalSubsetInclusion X U) :=
    (TopCat.mono_iff_injective _).2 Subtype.val_injective
  exact asIso (SSet.Subcomplex.toRange (TopCat.toSSet.map (topologicalSubsetInclusion X U)))

example (X : TopCat.{0}) (U : Set X) := c1a5_singular_subset_iso X U

/-- A specified topological subspace inclusion.
Source: the subspace topology. -/
def c1a5_subset_map (X : TopCat.{0}) {U V : Set X} (h : U ⊆ V) :
    TopCat.of U ⟶ TopCat.of V :=
  TopCat.ofHom ⟨fun x ↦ ⟨x.val, h x.property⟩, continuous_subtype_val.subtype_mk _⟩

example (X : TopCat.{0}) (U V : Set X) (h : U ⊆ V) := c1a5_subset_map X h

/-- Subspace image isomorphisms intertwine the actual subspace inclusions.
Source: Mathlib Subcomplex.toRange_ι and the subspace inclusion formula. -/
lemma c1a5_singular_subset_iso_naturality (X : TopCat.{0}) {U V : Set X} (h : U ⊆ V) :
    TopCat.toSSet.map (c1a5_subset_map X h) ≫ (c1a5_singular_subset_iso X V).hom =
      (c1a5_singular_subset_iso X U).hom ≫
        SSet.Subcomplex.homOfLE (show
          SSet.Subcomplex.range (TopCat.toSSet.map (topologicalSubsetInclusion X U)) ≤
          SSet.Subcomplex.range (TopCat.toSSet.map (topologicalSubsetInclusion X V)) from by
            intro n x hx
            rw [c1a5_singular_subset_range_iff] at hx ⊢
            exact hx.trans h) := by
  ext n x
  rfl

end HodgeLean.Foundations.Program
