import HodgeLean.Foundations.BundleThom.RealPuncturedProductProjectionHelpers
import HodgeLean.Foundations.BundleThom.RelativeHomologySuccessorVanishingHelpers

/-! # Homology of actual real product complement inclusions

HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Limits AlgebraicTopology AlgebraicTopology.Singular
namespace HodgeLean.Foundations.BundleThom

/-- Inclusion of the real product complement is surjective on homology in every degree when a nonzero normal vector is specified.
Source: Hatcher, Algebraic Topology, §2.1, normal contraction and homotopy invariance. -/
theorem i1_realProductComplementHomology_epi (B : Type) [TopologicalSpace B]
    (d : ℕ) (w : Fin d → ℝ) (hw : w ≠ 0) (n : ℕ) :
    Epi (HomologicalComplex.homologyMap
      ((chainPairFunctor ℚ).obj (i1_realProductNormalPair B d)).hom n) := by
  let X := i1_realProductNormalPair B d
  let F := (singularChainComplexFunctor (ModuleCat.{0} ℚ)).obj (ModuleCat.of ℚ ℚ)
  let s : X.fst ⟶ X.snd := TopCat.ofHom
    ⟨fun p => ⟨(p.1, w), hw⟩, (continuous_fst.prodMk continuous_const).subtype_mk _⟩
  let H : TopCat.Homotopy (s ≫ X.map) (𝟙 X.fst) := {
    toFun := fun p => ((p.2 : B × (Fin d → ℝ)).1,
      (1 - (p.1 : ℝ)) • w + (p.1 : ℝ) • (p.2 : B × (Fin d → ℝ)).2)
    continuous_toFun := by
      change Continuous (fun p : unitInterval × (B × (Fin d → ℝ)) =>
        (p.2.1, (1 - (p.1 : ℝ)) • w + (p.1 : ℝ) • p.2.2))
      fun_prop
    map_zero_left := fun p => by
      change (p.1, (1 - (0 : ℝ)) • w + (0 : ℝ) • p.2) = (p.1, w)
      simp
    map_one_left := fun p => by
      change (p.1, (1 - (1 : ℝ)) • w + (1 : ℝ) • p.2) = p
      simp <;> rfl }
  have he : HomologicalComplex.homologyMap (F.map s) n ≫
      HomologicalComplex.homologyMap (F.map X.map) n = 𝟙 _ := by
    rw [← HomologicalComplex.homologyMap_comp, ← F.map_comp,
      H.congr_homologyMap_singularChainComplexFunctor (ModuleCat.of ℚ ℚ) n,
      F.map_id, HomologicalComplex.homologyMap_id]
  change Epi (HomologicalComplex.homologyMap (F.map X.map) n)
  exact epi_of_epi_fac he

/-- Real product complement projection is invertible on rational homology below the sphere degree over any base.
Source: Hatcher, Algebraic Topology, §2.2, punctured-product coordinates. -/
theorem i1_realProductComplementProjection_homology_isIso
    (B : Type) [TopologicalSpace B] (d n : ℕ) (hn : n + 1 < d) :
    IsIso (HomologicalComplex.homologyMap
      (((singularChainComplexFunctor (ModuleCat.{0} ℚ)).obj (ModuleCat.of ℚ ℚ)).map
        ((i1_realProductNormalPair B d).map ≫
          TopCat.ofHom (⟨Prod.fst, continuous_fst⟩ : ContinuousMap (B × (Fin d → ℝ)) B))) n) := by
  let F := (singularChainComplexFunctor (ModuleCat.{0} ℚ)).obj (ModuleCat.of ℚ ℚ)
  let e := TopCat.isoOfHomeo
    (X := (i1_realProductNormalPair B d).snd)
    (Y := TopCat.of (B × {x : Fin d → ℝ | x ≠ 0}))
    (i1_productSecondSubsetHomeomorph B (Fin d → ℝ) {x | x ≠ 0})
  let p : TopCat.of (B × {x : Fin d → ℝ | x ≠ 0}) ⟶ TopCat.of B :=
    TopCat.ofHom ⟨Prod.fst, continuous_fst⟩
  haveI : IsIso (HomologicalComplex.homologyMap (F.map p) n) :=
    i1_realPuncturedProductProjection_homology_isIso B d n hn
  change IsIso (HomologicalComplex.homologyMap (F.map (e.hom ≫ p)) n)
  rw [F.map_comp, HomologicalComplex.homologyMap_comp]
  infer_instance

/-- Actual real product complement inclusion is invertible on rational homology below the sphere degree over every base.
Source: Hatcher, Algebraic Topology, §2.1 and §2.2, projection comparison for the product pair. -/
theorem i1_realProductComplementHomology_isIso
    (B : Type) [TopologicalSpace B] (d n : ℕ) (hn : n + 1 < d) :
    IsIso (HomologicalComplex.homologyMap
      ((chainPairFunctor ℚ).obj (i1_realProductNormalPair B d)).hom n) := by
  let F := (singularChainComplexFunctor (ModuleCat.{0} ℚ)).obj (ModuleCat.of ℚ ℚ)
  let q : (i1_realProductNormalPair B d).fst ⟶ TopCat.of B :=
    TopCat.ofHom ⟨Prod.fst, continuous_fst⟩
  haveI : QuasiIso (F.map q) := i1_productContractibleProjection_quasiIso B (Fin d → ℝ)
  have h := i1_realProductComplementProjection_homology_isIso B d n hn
  change IsIso (HomologicalComplex.homologyMap
    (F.map ((i1_realProductNormalPair B d).map ≫ q)) n) at h
  rw [F.map_comp, HomologicalComplex.homologyMap_comp] at h
  exact (isIso_comp_right_iff _ _).mp h

end HodgeLean.Foundations.BundleThom
