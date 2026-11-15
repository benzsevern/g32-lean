import HodgeLean.Foundations.Singular.ProductSteps

/-! One degree of the chain comparison from actual universal model chains. -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
open CategoryTheory AlgebraicTopology.Singular AlgebraicTopology.Simplicial
open scoped Simplicial TensorProduct
namespace HodgeLean.Foundations.Singular

/-- Boundary compatibility on the universal identity pairs gives boundary
compatibility of the extended maps on all actual tensor chains.
Source: Hatcher, Algebraic Topology, §3.2, the acyclic-models construction. -/
theorem productModelExtension_boundary
    (n : ℕ)
    (a : ∀ X Y : TopCat.{0},
      (rationalTensorChains X Y).X n →ₗ[ℚ] (rationalChains (TopCat.of (X × Y))).X n)
    (ha : ∀ {X X' Y Y' : TopCat.{0}} (f : X ⟶ X') (g : Y ⟶ Y'),
      (a X' Y').comp ((rationalTensorChainMap f g).f n).hom =
        (((rationalChainMap (topologicalProductMap f g)).f n).hom).comp (a X Y))
    (c : ∀ (p q : ℕ), p + q = n + 1 →
      (rationalChains (TopCat.of (simplexProductModel p q))).X (n + 1))
    (hc : ∀ (p q : ℕ) (hpq : p + q = n + 1),
      ((rationalChains (TopCat.of (simplexProductModel p q))).d (n + 1) n).hom (c p q hpq) =
        a (TopCat.of (Convexity.StdSimplex ℝ (Fin (p + 1))))
          (TopCat.of (Convexity.StdSimplex ℝ (Fin (q + 1))))
          (((rationalTensorChains
            (TopCat.of (Convexity.StdSimplex ℝ (Fin (p + 1))))
            (TopCat.of (Convexity.StdSimplex ℝ (Fin (q + 1))))).d (n + 1) n).hom
              (universalTensorSimplex p q (n + 1) hpq)))
    (X Y : TopCat.{0}) :
    (((rationalChains (TopCat.of (X × Y))).d (n + 1) n).hom).comp
        (productModelExtension X Y (n + 1) c) =
      (a X Y).comp ((rationalTensorChains X Y).d (n + 1) n).hom := by
  apply rationalTotalTensor_linearMap_ext X Y (n + 1)
  intro p q hpq σ τ
  erw [LinearMap.comp_apply, productModelExtension_simplex, LinearMap.comp_apply,
    rationalChainMap_boundary, hc p q hpq]
  let f := singularSimplexTopCatMap X p σ
  let g := singularSimplexTopCatMap Y q τ
  let u := universalTensorSimplex p q (n + 1) hpq
  have hn := LinearMap.congr_fun (ha f g)
    (((rationalTensorChains
      (TopCat.of (Convexity.StdSimplex ℝ (Fin (p + 1))))
      (TopCat.of (Convexity.StdSimplex ℝ (Fin (q + 1))))).d (n + 1) n).hom u)
  simp only [LinearMap.comp_apply] at hn
  change ((rationalChainMap (topologicalProductMap f g)).f n).hom
      (a _ _ (((rationalTensorChains _ _).d (n + 1) n).hom u)) = _
  rw [← hn, ← rationalTensorChainMap_boundary,
    universalTensorSimplex_map X Y p q (n + 1) hpq σ τ]
  rfl

/-- Compatibility in the preceding degree supplies a filler for every next
positive-degree boundary obstruction on the actual product models.
Source: Hatcher, Algebraic Topology, §3.2, induction over acyclic product models. -/
theorem productModel_next_filler
    (n : ℕ)
    (a : ∀ X Y : TopCat.{0}, (rationalTensorChains X Y).X (n + 1) →ₗ[ℚ]
      (rationalChains (TopCat.of (X × Y))).X (n + 1))
    (b : ∀ X Y : TopCat.{0}, (rationalTensorChains X Y).X n →ₗ[ℚ]
      (rationalChains (TopCat.of (X × Y))).X n)
    (hab : ∀ X Y : TopCat.{0},
      (((rationalChains (TopCat.of (X × Y))).d (n + 1) n).hom).comp (a X Y) =
        (b X Y).comp ((rationalTensorChains X Y).d (n + 1) n).hom)
    (p q : ℕ) (hpq : p + q = n + 2) :
    ∃ w : (rationalChains (TopCat.of (simplexProductModel p q))).X (n + 2),
      ((rationalChains (TopCat.of (simplexProductModel p q))).d (n + 2) (n + 1)).hom w =
        a (TopCat.of (Convexity.StdSimplex ℝ (Fin (p + 1))))
          (TopCat.of (Convexity.StdSimplex ℝ (Fin (q + 1))))
          (((rationalTensorChains
            (TopCat.of (Convexity.StdSimplex ℝ (Fin (p + 1))))
            (TopCat.of (Convexity.StdSimplex ℝ (Fin (q + 1))))).d (n + 2) (n + 1)).hom
              (universalTensorSimplex p q (n + 2) hpq)) := by
  let X := TopCat.of (Convexity.StdSimplex ℝ (Fin (p + 1)))
  let Y := TopCat.of (Convexity.StdSimplex ℝ (Fin (q + 1)))
  let T := rationalTensorChains X Y
  let u := universalTensorSimplex p q (n + 2) hpq
  refine simplexProductModel_cycle_filler p q n _ ?_
  have hz := LinearMap.congr_fun (hab X Y) ((T.d (n + 2) (n + 1)).hom u)
  simp only [LinearMap.comp_apply] at hz
  have hd : (T.d (n + 1) n).hom ((T.d (n + 2) (n + 1)).hom u) = 0 :=
    congrArg (fun k => ModuleCat.Hom.hom k u) (T.d_comp_d (n + 2) (n + 1) n)
  erw [hz, hd, map_zero]

/-- A natural comparison in two preceding degrees extends through the next
positive degree by actual model-chain fillers.
Source: Hatcher, Algebraic Topology, §3.2, the acyclic-models induction. -/
theorem productModel_extend_positive
    (n : ℕ)
    (a : ∀ X Y : TopCat.{0}, (rationalTensorChains X Y).X (n + 1) →ₗ[ℚ]
      (rationalChains (TopCat.of (X × Y))).X (n + 1))
    (b : ∀ X Y : TopCat.{0}, (rationalTensorChains X Y).X n →ₗ[ℚ]
      (rationalChains (TopCat.of (X × Y))).X n)
    (ha : ∀ {X X' Y Y' : TopCat.{0}} (f : X ⟶ X') (g : Y ⟶ Y'),
      (a X' Y').comp ((rationalTensorChainMap f g).f (n + 1)).hom =
        (((rationalChainMap (topologicalProductMap f g)).f (n + 1)).hom).comp (a X Y))
    (hab : ∀ X Y : TopCat.{0},
      (((rationalChains (TopCat.of (X × Y))).d (n + 1) n).hom).comp (a X Y) =
        (b X Y).comp ((rationalTensorChains X Y).d (n + 1) n).hom) :
    ∃ c : ∀ X Y : TopCat.{0}, (rationalTensorChains X Y).X (n + 2) →ₗ[ℚ]
        (rationalChains (TopCat.of (X × Y))).X (n + 2),
      (∀ {X X' Y Y' : TopCat.{0}} (f : X ⟶ X') (g : Y ⟶ Y'),
        (c X' Y').comp ((rationalTensorChainMap f g).f (n + 2)).hom =
          (((rationalChainMap (topologicalProductMap f g)).f (n + 2)).hom).comp (c X Y)) ∧
      (∀ X Y : TopCat.{0},
        (((rationalChains (TopCat.of (X × Y))).d (n + 2) (n + 1)).hom).comp (c X Y) =
          (a X Y).comp ((rationalTensorChains X Y).d (n + 2) (n + 1)).hom) := by
  let c (p q : ℕ) (hpq : p + q = n + 2) :=
    Classical.choose (productModel_next_filler n a b hab p q hpq)
  have hc (p q : ℕ) (hpq : p + q = n + 2) :=
    Classical.choose_spec (productModel_next_filler n a b hab p q hpq)
  refine ⟨fun X Y => productModelExtension X Y (n + 2) c, ?_, ?_⟩
  · intro X X' Y Y' f g
    exact productModelExtension_naturality f g (n + 2) c
  · intro X Y
    exact productModelExtension_boundary (n + 1) a ha c hc X Y

#print axioms productModel_extend_positive
#print axioms productModel_next_filler
#print axioms productModelExtension_boundary
end HodgeLean.Foundations.Singular
