import HodgeLean.Foundations.BundleThom.SubsetChainProjectionHelpers
import HodgeLean.Foundations.BundleThom.BinarySmallSingularCoverHelpers

/-! # Projection comparison on actual binary open covers

HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicTopology AlgebraicTopology.Singular HomologicalComplex
namespace HodgeLean.Foundations.BundleThom

/-- Projection from an actual binary open cover is equivalent on homology from equivalences on its two domains and adjacent-degree control on its actual intersection.
Source: Hatcher, Algebraic Topology, §2.2, the small-chain Mayer–Vietoris comparison argument. -/
theorem i1_topologicalBinaryProjection_homology_isIso
    (X Y : TopCat) (p : X ⟶ Y) (U V : Set X)
    (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = Set.univ)
    (hu : QuasiIso (((singularChainComplexFunctor (ModuleCat.{0} ℚ)).obj
      (ModuleCat.of ℚ ℚ)).map (topologicalSubsetInclusion X U ≫ p)))
    (hv : QuasiIso (((singularChainComplexFunctor (ModuleCat.{0} ℚ)).obj
      (ModuleCat.of ℚ ℚ)).map (topologicalSubsetInclusion X V ≫ p)))
    (n : ℕ)
    (ha : Epi (HomologicalComplex.homologyMap (((singularChainComplexFunctor (ModuleCat.{0} ℚ)).obj
      (ModuleCat.of ℚ ℚ)).map (topologicalSubsetInclusion X (U ∩ V) ≫ p)) n))
    (hl : ∀ m, (ComplexShape.down ℕ).Rel n m →
      IsIso (HomologicalComplex.homologyMap (((singularChainComplexFunctor (ModuleCat.{0} ℚ)).obj
        (ModuleCat.of ℚ ℚ)).map (topologicalSubsetInclusion X (U ∩ V) ≫ p)) m)) :
    IsIso (HomologicalComplex.homologyMap (((singularChainComplexFunctor (ModuleCat.{0} ℚ)).obj
      (ModuleCat.of ℚ ℚ)).map p) n) := by
  let F := (singularChainComplexFunctor (ModuleCat.{0} ℚ)).obj (ModuleCat.of ℚ ℚ)
  let A := i1_singularSubsetRange X U
  let B := i1_singularSubsetRange X V
  haveI : QuasiIso (i1_subcomplexChainProjection (TopCat.toSSet.map p) A) :=
    (i1_subsetChainProjection_quasiIso_iff X Y p U).mpr hu
  haveI : QuasiIso (i1_subcomplexChainProjection (TopCat.toSSet.map p) B) :=
    (i1_subsetChainProjection_quasiIso_iff X Y p V).mpr hv
  have hs : IsIso (HomologicalComplex.homologyMap
      (i1_subcomplexChainProjection (TopCat.toSSet.map p) (A ⊔ B)) n) := by
    apply i1_subcomplexProjection_sup_homology_isIso
    · change Epi (HomologicalComplex.homologyMap (i1_subcomplexChainProjection (TopCat.toSSet.map p)
        (i1_singularSubsetRange X U ⊓ i1_singularSubsetRange X V)) n)
      rw [← i1_singularSubsetRange_inter]
      exact (i1_subsetChainProjection_homology_epi_iff X Y p (U ∩ V) n).mpr ha
    · intro m hm
      change IsIso (HomologicalComplex.homologyMap (i1_subcomplexChainProjection (TopCat.toSSet.map p)
        (i1_singularSubsetRange X U ⊓ i1_singularSubsetRange X V)) m)
      rw [← i1_singularSubsetRange_inter]
      exact (i1_subsetChainProjection_homology_isIso_iff X Y p (U ∩ V) m).mpr (hl m hm)
  let s := SSet.chainComplexMap (A ⊔ B).ι (ModuleCat.of ℚ ℚ)
  haveI : QuasiIso s := i1_binarySmallChainInclusion_quasiIso X U V hU hV hcover
  have he : s ≫ F.map p =
      i1_subcomplexChainProjection (TopCat.toSSet.map p) (A ⊔ B) := by
    let G : SSet ⥤ ChainComplex (ModuleCat ℚ) ℕ :=
      (SSet.chainComplexFunctor.{0,0,1} (ModuleCat ℚ)).obj (ModuleCat.of ℚ ℚ)
    change G.map (A ⊔ B).ι ≫ G.map (TopCat.toSSet.map p) =
      G.map ((A ⊔ B).ι ≫ TopCat.toSSet.map p)
    rw [G.map_comp]
  rw [← he, HomologicalComplex.homologyMap_comp] at hs
  exact (isIso_comp_left_iff (HomologicalComplex.homologyMap s n) (HomologicalComplex.homologyMap (F.map p) n)).mp hs

end HodgeLean.Foundations.BundleThom
