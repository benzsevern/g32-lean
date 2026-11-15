import HodgeLean.Foundations.BundleThom.ProductMatrixPairHelpers

/-! # Base maps of actual product normal pairs

The normal coordinate and its nonzero support are retained exactly.
HC no distance; AV milestone no distance. -/

noncomputable section
open CategoryTheory TopologicalSpace AlgebraicTopology.Singular
namespace HodgeLean.Foundations.BundleThom

/-- A continuous base map induces the actual normal-coordinate-preserving map of product pairs.
Source: Hatcher, Algebraic Topology, §2.1, maps of product pairs. -/
def i1_productBaseMap {B C : Type} [TopologicalSpace B] [TopologicalSpace C]
    (k : ℕ) (f : B → C) (hf : Continuous f) :
    i1_productNormalPair B k ⟶ i1_productNormalPair C k :=
  TopPair.ofSubsetHom (TopCat.ofHom
    ⟨fun p => (f p.1, p.2), (hf.comp continuous_fst).prodMk continuous_snd⟩)
    (fun _ h => h)

/-- Actual product base maps preserve composition while fixing the normal coordinate.
Source: Hatcher, Algebraic Topology, §2.1, functoriality of product pairs. -/
theorem i1_productBaseMap_comp {B C D : Type} [TopologicalSpace B]
    [TopologicalSpace C] [TopologicalSpace D] (k : ℕ)
    (f : B → C) (hf : Continuous f) (g : C → D) (hg : Continuous g) :
    i1_productBaseMap k f hf ≫ i1_productBaseMap k g hg =
      i1_productBaseMap k (g ∘ f) (hg.comp hf) := by
  apply MorphismProperty.Arrow.Hom.ext <;> rfl

/-- The identity base map induces the identity of the actual product normal pair.
Source: Hatcher, Algebraic Topology, §2.1, functoriality of product pairs. -/
theorem i1_productBaseMap_id (B : Type) [TopologicalSpace B] (k : ℕ) :
    i1_productBaseMap k (id : B → B) continuous_id = 𝟙 (i1_productNormalPair B k) := by
  apply MorphismProperty.Arrow.Hom.ext <;> rfl

/-- Normal projection is unchanged by every actual product base map.
Source: Bott–Tu, Differential Forms in Algebraic Topology, §6, product normal coordinates. -/
theorem i1_productBaseMap_comp_projection {B C : Type} [TopologicalSpace B]
    [TopologicalSpace C] (k : ℕ) (f : B → C) (hf : Continuous f) :
    i1_productBaseMap k f hf ≫ i1_productNormalProjection C k =
      i1_productNormalProjection B k := by
  apply MorphismProperty.Arrow.Hom.ext <;> rfl

/-- Pulling a varying matrix normal map along an actual base map gives its actual composed matrix family.
Source: Bott–Tu, Differential Forms in Algebraic Topology, §6, naturality of frame changes. -/
theorem i1_productBaseMap_comp_matrixNormalMap {B C : Type} [TopologicalSpace B]
    [TopologicalSpace C] (k : ℕ) (f : B → C) (hf : Continuous f)
    (A : C → Matrix (Fin k) (Fin k) ℂ) (hA : Continuous A)
    (hd : ∀ c, (A c).det ≠ 0) :
    i1_productBaseMap k f hf ≫ i1_productMatrixNormalMap k A hA hd =
      i1_productMatrixNormalMap k (A ∘ f) (hA.comp hf) (fun b => hd (f b)) := by
  apply MorphismProperty.Arrow.Hom.ext <;> rfl

end HodgeLean.Foundations.BundleThom
