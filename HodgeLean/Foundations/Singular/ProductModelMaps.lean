import HodgeLean.Foundations.Singular.ProductNaturality

/-! Maps from the universal product models to the actual spaces. -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
open CategoryTheory AlgebraicTopology.Singular AlgebraicTopology.Simplicial
open scoped Simplicial TensorProduct
namespace HodgeLean.Foundations.Singular

/-- The actual product map of two continuous maps.
Source: Hatcher, Algebraic Topology, §3.2, naturality of products. -/
def topologicalProductMap {X X' Y Y' : TopCat.{0}} (f : X ⟶ X') (g : Y ⟶ Y') :
    TopCat.of (X × Y) ⟶ TopCat.of (X' × Y') :=
  TopCat.ofHom (f.hom.prodMap g.hom)

/-- A pair of singular simplices gives the actual map from its universal product model.
Source: Hatcher, Algebraic Topology, §3.2, acyclic product models. -/
def simplexPairMap (X Y : TopCat.{0}) (p q : ℕ)
    (σ : (TopCat.toSSet.obj X) _⦋p⦌) (τ : (TopCat.toSSet.obj Y) _⦋q⦌) :
    TopCat.of (simplexProductModel p q) ⟶ TopCat.of (X × Y) :=
  topologicalProductMap (singularSimplexTopCatMap X p σ) (singularSimplexTopCatMap Y q τ)

/-- Mapping both singular simplices postcomposes the actual product-model map.
Source: Hatcher, Algebraic Topology, §3.2, naturality of products. -/
theorem simplexPairMap_naturality
    {X X' Y Y' : TopCat.{0}} (f : X ⟶ X') (g : Y ⟶ Y') (p q : ℕ)
    (σ : (TopCat.toSSet.obj X) _⦋p⦌) (τ : (TopCat.toSSet.obj Y) _⦋q⦌) :
    simplexPairMap X' Y' p q ((TopCat.toSSet.map f).app _ σ) ((TopCat.toSSet.map g).app _ τ) =
      simplexPairMap X Y p q σ τ ≫ topologicalProductMap f g := by
  unfold simplexPairMap
  rw [singularSimplexTopCatMap_map f, singularSimplexTopCatMap_map g]
  ext z <;> rfl

/-- A face in the first singular simplex precomposes the product-model map with its actual coface.
Source: Hatcher, Algebraic Topology, §3.2, faces of product models. -/
theorem simplexPairMap_face_left
    (X Y : TopCat.{0}) (p q : ℕ)
    (σ : (TopCat.toSSet.obj X) _⦋p + 1⦌) (τ : (TopCat.toSSet.obj Y) _⦋q⦌)
    (i : Fin (p + 2)) :
    simplexPairMap X Y p q ((TopCat.toSSet.obj X).δ i σ) τ =
      topologicalProductMap (standardSimplexFaceTopCatMap p i)
        (𝟙 (TopCat.of (Convexity.StdSimplex ℝ (Fin (q + 1))))) ≫
          simplexPairMap X Y (p + 1) q σ τ := by
  unfold simplexPairMap
  rw [← singularSimplexTopCatMap_delta X p σ i]
  ext z <;> rfl

/-- A face in the second singular simplex precomposes the product-model map with its actual coface.
Source: Hatcher, Algebraic Topology, §3.2, faces of product models. -/
theorem simplexPairMap_face_right
    (X Y : TopCat.{0}) (p q : ℕ)
    (σ : (TopCat.toSSet.obj X) _⦋p⦌) (τ : (TopCat.toSSet.obj Y) _⦋q + 1⦌)
    (i : Fin (q + 2)) :
    simplexPairMap X Y p q σ ((TopCat.toSSet.obj Y).δ i τ) =
      topologicalProductMap (𝟙 (TopCat.of (Convexity.StdSimplex ℝ (Fin (p + 1)))))
        (standardSimplexFaceTopCatMap q i) ≫ simplexPairMap X Y p (q + 1) σ τ := by
  unfold simplexPairMap
  rw [← singularSimplexTopCatMap_delta Y q τ i]
  ext z <;> rfl

#print axioms simplexPairMap_face_right
#print axioms simplexPairMap_face_left
#print axioms topologicalProductMap
#print axioms simplexPairMap
#print axioms simplexPairMap_naturality
end HodgeLean.Foundations.Singular
