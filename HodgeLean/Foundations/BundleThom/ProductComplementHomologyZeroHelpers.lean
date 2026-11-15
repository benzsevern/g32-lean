import HodgeLean.Foundations.BundleThom.ProductHomologyZeroHelpers
import HodgeLean.Foundations.BundleThom.ProductComplementHomologyHelpers

/-! # Degree-zero homology of the actual product complement inclusion

The arbitrary base remains fixed while the path-connected normal factors are projected away.
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
open CategoryTheory TopologicalSpace AlgebraicTopology.Singular
namespace HodgeLean.Foundations.BundleThom

/-- Separating the base coordinate identifies the actual product complement with the product of the punctured normal fibre.
Source: Hatcher, Algebraic Topology, §2.1, product pairs. -/
def i1_productComplementHomeomorph (B : Type) [TopologicalSpace B] (k : ℕ) :
    (i1_productNormalPair B k).snd ≃ₜ B × (puncturedPair ℂ k).snd where
  toFun p := (p.1.1, ⟨p.1.2, p.2⟩)
  invFun p := ⟨(p.1, p.2.1), p.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := continuous_subtype_val.fst.prodMk
    (continuous_subtype_val.snd.subtype_mk _)
  continuous_invFun := (continuous_fst.prodMk continuous_snd.subtype_val).subtype_mk _

/-- The actual product complement inclusion is invertible on degree-zero rational homology in positive complex rank, for every base.
Source: Hatcher, Algebraic Topology, §2.1, path components of products and punctured complex spaces. -/
theorem i1_productComplementHomologyZero_isIso {B : Type} [TopologicalSpace B]
    (k : ℕ) (hk : 0 < k) :
    IsIso (HomologicalComplex.homologyMap
      ((chainPairFunctor ℚ).obj (i1_productNormalPair B k)).hom 0) := by
  let w : Fin k → ℂ := fun _ => 1
  have hw : w ≠ 0 := by
    intro h
    exact one_ne_zero (congrFun h ⟨0, hk⟩)
  letI := i1_complexPunctured_pathConnectedSpace k hk
  let p : (i1_productNormalPair B k).fst ⟶ TopCat.of B :=
    TopCat.ofHom ⟨Prod.fst, continuous_fst⟩
  let q : (i1_productNormalPair B k).snd ⟶ TopCat.of B :=
    TopCat.ofHom ⟨fun z => z.1.1, continuous_subtype_val.fst⟩
  let e := TopCat.isoOfHomeo (X := (i1_productNormalPair B k).snd)
    (Y := TopCat.of (B × (puncturedPair ℂ k).snd)) (i1_productComplementHomeomorph B k)
  let r : TopCat.of (B × (puncturedPair ℂ k).snd) ⟶ TopCat.of B :=
    TopCat.ofHom ⟨Prod.fst, continuous_fst⟩
  let H := fun {X Y : TopCat} (f : X ⟶ Y) =>
    HomologicalComplex.homologyMap (singularChainComplexMap ℚ f) 0
  have comp {X Y Z : TopCat} (f : X ⟶ Y) (g : Y ⟶ Z) :
      H (f ≫ g) = H f ≫ H g := by
    dsimp [H, singularChainComplexMap]
    rw [Functor.map_comp, HomologicalComplex.homologyMap_comp]
  haveI : IsIso (H p) := (i1_productHomologyZeroIso (B := B) w).isIso_hom
  haveI : IsIso (H r) :=
    (i1_productHomologyZeroIso (B := B) (F := (puncturedPair ℂ k).snd) (⟨w, hw⟩ : (puncturedPair ℂ k).snd)).isIso_hom
  haveI : IsIso (H e.hom) := by
    dsimp [H, singularChainComplexMap]
    infer_instance
  have hq : q = e.hom ≫ r := rfl
  haveI : IsIso (H q) := by rw [hq, comp]; infer_instance
  have hi : (i1_productNormalPair B k).map ≫ p = q := rfl
  haveI : IsIso (H (i1_productNormalPair B k).map ≫ H p) := by
    rw [← comp, hi]
    infer_instance
  exact IsIso.of_isIso_comp_right (H (i1_productNormalPair B k).map) (H p)

end HodgeLean.Foundations.BundleThom
