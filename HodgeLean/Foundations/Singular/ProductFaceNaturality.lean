import HodgeLean.Foundations.Singular.ProductFaces
import HodgeLean.Foundations.Singular.ProductModelMaps

/-! Naturality of the specified front/back-face tensor components. -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
open CategoryTheory AlgebraicTopology.Simplicial
open scoped Simplicial TensorProduct
namespace HodgeLean.Foundations.Singular

/-- The two product projections commute with the actual map of product spaces.
Source: Hatcher, Algebraic Topology, §3.2, naturality of the cross product. -/
theorem productProjections_naturality
    {X X' Y Y' : TopCat.{0}} (f : X ⟶ X') (g : Y ⟶ Y') :
    topologicalProductMap f g ≫ productFirst X' Y' = productFirst X Y ≫ f ∧
      topologicalProductMap f g ≫ productSecond X' Y' = productSecond X Y ≫ g := by
  constructor <;> ext z <;> rfl

/-- Front/back tensor components commute with actual maps on both product factors.
Source: Hatcher, Algebraic Topology, §3.2, naturality of the Alexander–Whitney map. -/
theorem productFaceComponent_naturality
    {X X' Y Y' : TopCat.{0}} (f : X ⟶ X') (g : Y ⟶ Y') (p q : ℕ) :
    (productFaceComponent X' Y' p q).comp
        (((rationalChainMap (topologicalProductMap f g)).f (p + q)).hom) =
      (TensorProduct.map ((rationalChainMap f).f p).hom ((rationalChainMap g).f q).hom).comp
        (productFaceComponent X Y p q) := by
  apply rationalChain_linearMap_ext (TopCat.of (X × Y)) (p + q)
  intro σ
  erw [LinearMap.comp_apply, rationalChainMap_simplex, productFaceComponent_simplex,
    LinearMap.comp_apply, productFaceComponent_simplex, TensorProduct.map_tmul,
    rationalChainMap_simplex, rationalChainMap_simplex]
  have hf : (TopCat.toSSet.map (productFirst X' Y')).app _
      ((TopCat.toSSet.map (topologicalProductMap f g)).app _ σ) =
      (TopCat.toSSet.map f).app _ ((TopCat.toSSet.map (productFirst X Y)).app _ σ) := by
    apply (TopCat.toSSetObjEquiv _ _).injective
    rfl
  have hg : (TopCat.toSSet.map (productSecond X' Y')).app _
      ((TopCat.toSSet.map (topologicalProductMap f g)).app _ σ) =
      (TopCat.toSSet.map g).app _ ((TopCat.toSSet.map (productSecond X Y)).app _ σ) := by
    apply (TopCat.toSSetObjEquiv _ _).injective
    rfl
  rw [hf, hg, frontFace_naturality, backFace_naturality]
  rfl

#print axioms productFaceComponent_naturality
#print axioms productProjections_naturality
end HodgeLean.Foundations.Singular
