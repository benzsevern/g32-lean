import HodgeLean.Foundations.BundleThom.RealNormalPuncturedEquatorHelpers
import HodgeLean.Foundations.BundleThom.ProductProjectionHomologyHelpers

/-! # Actual equator projection on rational homology

HC no distance; AV milestone no distance. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicTopology HomologicalComplex
namespace HodgeLean.Foundations.BundleThom

/-- Projection invertibility on the actual equator is exactly invertibility for the lower-dimensional punctured product.
Source: Hatcher, Algebraic Topology, §2.2, the equatorial reduction in Mayer–Vietoris. -/
theorem i1_realNormalEquatorProjection_homology_isIso_iff
    (B : Type) [TopologicalSpace B] (d n : ℕ) :
    IsIso (homologyMap
      (((singularChainComplexFunctor (ModuleCat.{0} ℚ)).obj (ModuleCat.of ℚ ℚ)).map
        (TopCat.ofHom ⟨fun z : {p : B × {x : Fin (d + 1) → ℝ | x ≠ 0} |
          Fin.tail p.2.1 ≠ 0} => z.1.1,
          continuous_fst.comp continuous_subtype_val⟩)) n) ↔
    IsIso (homologyMap
      (((singularChainComplexFunctor (ModuleCat.{0} ℚ)).obj (ModuleCat.of ℚ ℚ)).map
        (TopCat.ofHom (⟨Prod.fst, continuous_fst⟩ :
          ContinuousMap (B × {x : Fin d → ℝ | x ≠ 0}) B))) n) := by
  let F := (singularChainComplexFunctor (ModuleCat.{0} ℚ)).obj (ModuleCat.of ℚ ℚ)
  let e := TopCat.isoOfHomeo
    (X := TopCat.of {p : B × {x : Fin (d + 1) → ℝ | x ≠ 0} | Fin.tail p.2.1 ≠ 0})
    (Y := TopCat.of ((B × {x : Fin d → ℝ | x ≠ 0}) × ℝ))
    (i1_realNormalProductEquatorHomeomorph B d)
  let r : TopCat.of ((B × {x : Fin d → ℝ | x ≠ 0}) × ℝ) ⟶
      TopCat.of (B × {x : Fin d → ℝ | x ≠ 0}) := TopCat.ofHom ⟨Prod.fst, continuous_fst⟩
  let p : TopCat.of (B × {x : Fin d → ℝ | x ≠ 0}) ⟶ TopCat.of B :=
    TopCat.ofHom ⟨Prod.fst, continuous_fst⟩
  haveI : QuasiIso (F.map r) := i1_productContractibleProjection_quasiIso _ ℝ
  change IsIso (homologyMap (F.map (e.hom ≫ r ≫ p)) n) ↔
    IsIso (homologyMap (F.map p) n)
  simp only [F.map_comp, homologyMap_comp, isIso_comp_left_iff]

/-- Projection surjectivity on the actual equator is exactly surjectivity for the lower-dimensional punctured product.
Source: Hatcher, Algebraic Topology, §2.2, the equatorial reduction in Mayer–Vietoris. -/
theorem i1_realNormalEquatorProjection_homology_epi_iff
    (B : Type) [TopologicalSpace B] (d n : ℕ) :
    Epi (homologyMap
      (((singularChainComplexFunctor (ModuleCat.{0} ℚ)).obj (ModuleCat.of ℚ ℚ)).map
        (TopCat.ofHom ⟨fun z : {p : B × {x : Fin (d + 1) → ℝ | x ≠ 0} |
          Fin.tail p.2.1 ≠ 0} => z.1.1,
          continuous_fst.comp continuous_subtype_val⟩)) n) ↔
    Epi (homologyMap
      (((singularChainComplexFunctor (ModuleCat.{0} ℚ)).obj (ModuleCat.of ℚ ℚ)).map
        (TopCat.ofHom (⟨Prod.fst, continuous_fst⟩ :
          ContinuousMap (B × {x : Fin d → ℝ | x ≠ 0}) B))) n) := by
  let F := (singularChainComplexFunctor (ModuleCat.{0} ℚ)).obj (ModuleCat.of ℚ ℚ)
  let e := TopCat.isoOfHomeo
    (X := TopCat.of {p : B × {x : Fin (d + 1) → ℝ | x ≠ 0} | Fin.tail p.2.1 ≠ 0})
    (Y := TopCat.of ((B × {x : Fin d → ℝ | x ≠ 0}) × ℝ))
    (i1_realNormalProductEquatorHomeomorph B d)
  let r : TopCat.of ((B × {x : Fin d → ℝ | x ≠ 0}) × ℝ) ⟶
      TopCat.of (B × {x : Fin d → ℝ | x ≠ 0}) := TopCat.ofHom ⟨Prod.fst, continuous_fst⟩
  let p : TopCat.of (B × {x : Fin d → ℝ | x ≠ 0}) ⟶ TopCat.of B :=
    TopCat.ofHom ⟨Prod.fst, continuous_fst⟩
  haveI : QuasiIso (F.map r) := i1_productContractibleProjection_quasiIso _ ℝ
  change Epi (homologyMap (F.map (e.hom ≫ r ≫ p)) n) ↔
    Epi (homologyMap (F.map p) n)
  simp only [F.map_comp, homologyMap_comp, epi_comp_iff_of_epi]

end HodgeLean.Foundations.BundleThom
