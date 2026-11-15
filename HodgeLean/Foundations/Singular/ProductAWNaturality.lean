import HodgeLean.Foundations.Singular.ProductAWComponents
import HodgeLean.Foundations.Singular.ProductFaceNaturality
import HodgeLean.Foundations.Singular.ProductProjectionNaturality

/-! Naturality of the actual finite Alexander–Whitney degree maps. -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
open CategoryTheory CategoryTheory.MonoidalCategory
namespace HodgeLean.Foundations.Singular

/-- The finite Alexander–Whitney degree map is natural in both spaces.
Source: Hatcher, Algebraic Topology, §3.2, naturality of the Alexander–Whitney map. -/
theorem productAlexanderWhitneyDegree_naturality
    {X X' Y Y' : TopCat.{0}} (f : X ⟶ X') (g : Y ⟶ Y') (n : ℕ) :
    (rationalChainMap (topologicalProductMap f g)).f n ≫
        ModuleCat.ofHom (productAlexanderWhitneyDegree X' Y' n) =
      ModuleCat.ofHom (productAlexanderWhitneyDegree X Y n) ≫ (rationalTensorChainMap f g).f n := by
  apply tensorChainProjection_jointly_monic X' Y' n
  intro p q hpq
  subst n
  have hs := congrArg ModuleCat.ofHom (productAlexanderWhitneyDegree_projection_sum X Y p q)
  have ht := congrArg ModuleCat.ofHom (productAlexanderWhitneyDegree_projection_sum X' Y' p q)
  change ModuleCat.ofHom (productAlexanderWhitneyDegree X Y (p + q)) ≫
    tensorChainProjection X Y p q (p + q) = ModuleCat.ofHom (productFaceComponent X Y p q) at hs
  change ModuleCat.ofHom (productAlexanderWhitneyDegree X' Y' (p + q)) ≫
    tensorChainProjection X' Y' p q (p + q) = ModuleCat.ofHom (productFaceComponent X' Y' p q) at ht
  let a := ModuleCat.ofHom (productAlexanderWhitneyDegree X Y (p + q))
  let b := ModuleCat.ofHom (productAlexanderWhitneyDegree X' Y' (p + q))
  let c := (rationalChainMap (topologicalProductMap f g)).f (p + q)
  let t := (rationalTensorChainMap f g).f (p + q)
  let u := (rationalChainMap f).f p ⊗ₘ (rationalChainMap g).f q
  let π := tensorChainProjection X Y p q (p + q)
  let π' := tensorChainProjection X' Y' p q (p + q)
  have hn : c ≫ ModuleCat.ofHom (productFaceComponent X' Y' p q) =
      ModuleCat.ofHom (productFaceComponent X Y p q) ≫ u :=
    ModuleCat.hom_ext (productFaceComponent_naturality f g p q)
  change (c ≫ b) ≫ π' = (a ≫ t) ≫ π'
  calc
    (c ≫ b) ≫ π' = c ≫ (b ≫ π') := Category.assoc _ _ _
    _ = c ≫ ModuleCat.ofHom (productFaceComponent X' Y' p q) :=
      congrArg (fun k => c ≫ k) ht
    _ = ModuleCat.ofHom (productFaceComponent X Y p q) ≫ u := hn
    _ = (a ≫ π) ≫ u := congrArg (fun k => k ≫ u) hs.symm
    _ = a ≫ (π ≫ u) := Category.assoc _ _ _
    _ = a ≫ (t ≫ π') := congrArg (fun k => a ≫ k)
      (tensorChainProjection_naturality f g p q (p + q)).symm
    _ = (a ≫ t) ≫ π' := (Category.assoc _ _ _).symm

#print axioms productAlexanderWhitneyDegree_naturality
end HodgeLean.Foundations.Singular
