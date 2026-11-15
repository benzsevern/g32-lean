import HodgeLean.Foundations.Singular.ProductNaturality
import HodgeLean.Foundations.Singular.Cup
import HodgeLean.Foundations.Singular.TensorSeparation

/-! The bidegree front/back-face map on actual rational product chains. -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
open CategoryTheory CategoryTheory.MonoidalCategory AlgebraicTopology.Simplicial
open scoped Simplicial TensorProduct
namespace HodgeLean.Foundations.Singular

/-- The first continuous projection of the actual product space.
Source: Hatcher, Algebraic Topology, §3.2, the cross product. -/
def productFirst (X Y : TopCat.{0}) : TopCat.of (X × Y) ⟶ X :=
  TopCat.ofHom ContinuousMap.fst

/-- The second continuous projection of the actual product space.
Source: Hatcher, Algebraic Topology, §3.2, the cross product. -/
def productSecond (X Y : TopCat.{0}) : TopCat.of (X × Y) ⟶ Y :=
  TopCat.ofHom ContinuousMap.snd

/-- The specified front/back-face map in one tensor bidegree.
Source: Hatcher, Algebraic Topology, §3.2, the Alexander–Whitney formula. -/
def productFaceComponent (X Y : TopCat.{0}) (p q : ℕ) :
    (rationalChains (TopCat.of (X × Y))).X (p + q) →ₗ[ℚ]
      ((rationalChains X).X p ⊗[ℚ] (rationalChains Y).X q) :=
  rationalChainLift (TopCat.of (X × Y)) (p + q) (fun σ =>
    chainOfSimplex ℚ (frontFace (TopCat.toSSet.obj X)
      ((TopCat.toSSet.map (productFirst X Y)).app _ σ)) ⊗ₜ[ℚ]
    chainOfSimplex ℚ (backFace (TopCat.toSSet.obj Y)
      ((TopCat.toSSet.map (productSecond X Y)).app _ σ)))

/-- The face component evaluates on each actual singular simplex by its two projected faces.
Source: Hatcher, Algebraic Topology, §3.2, the Alexander–Whitney formula. -/
theorem productFaceComponent_simplex (X Y : TopCat.{0}) (p q : ℕ)
    (σ : (TopCat.toSSet.obj (TopCat.of (X × Y))) _⦋p + q⦌) :
    productFaceComponent X Y p q (chainOfSimplex ℚ σ) =
      chainOfSimplex ℚ (frontFace (TopCat.toSSet.obj X)
        ((TopCat.toSSet.map (productFirst X Y)).app _ σ)) ⊗ₜ[ℚ]
      chainOfSimplex ℚ (backFace (TopCat.toSSet.obj Y)
        ((TopCat.toSSet.map (productSecond X Y)).app _ σ)) := by
  unfold productFaceComponent
  exact rationalChainLift_simplex _ _ _ _

/-- Evaluation of a face component is the cup of the two projection pullbacks.
Source: Hatcher, Algebraic Topology, §3.2, the cochain cross product. -/
theorem productFaceComponent_pairing (X Y : TopCat.{0}) (p q : ℕ)
    (φ : (rationalChains X).X p →ₗ[ℚ] ℚ)
    (ψ : (rationalChains Y).X q →ₗ[ℚ] ℚ) :
    (tensorScalarPairing φ ψ).comp (productFaceComponent X Y p q) =
      cupCochain (TopCat.of (X × Y)) p q
        (cochainMap ℚ (TopCat.toSSet.map (productFirst X Y)) p φ)
        (cochainMap ℚ (TopCat.toSSet.map (productSecond X Y)) q ψ) := by
  apply rationalChain_linearMap_ext (TopCat.of (X × Y)) (p + q)
  intro σ
  erw [LinearMap.comp_apply, productFaceComponent_simplex,
    tensorScalarPairing_tmul, cupCochain_apply_simplex]
  rw [frontFace_naturality, backFace_naturality]
  change _ = φ (((rationalChainMap (productFirst X Y)).f p).hom
      (chainOfSimplex ℚ (frontFace (TopCat.toSSet.obj (TopCat.of (X × Y))) σ))) *
    ψ (((rationalChainMap (productSecond X Y)).f q).hom
      (chainOfSimplex ℚ (backFace (TopCat.toSSet.obj (TopCat.of (X × Y))) σ)))
  erw [rationalChainMap_simplex, rationalChainMap_simplex]

#print axioms productFaceComponent_pairing
#print axioms productFaceComponent
#print axioms productFaceComponent_simplex
end HodgeLean.Foundations.Singular
