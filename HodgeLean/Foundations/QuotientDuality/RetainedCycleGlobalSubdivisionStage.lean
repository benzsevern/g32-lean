import HodgeLean.Foundations.QuotientDuality.RetainedCycleCompactSectionHomology
import HodgeLean.Foundations.RationalHomologyManifold.GlobalSubdivisionComplexComparison
import HodgeLean.Foundations.RationalHomologyManifold.SubdivisionLimitHomology
import HodgeLean.Foundations.RationalHomologyManifold.SubdivisionGlobalSections
import HodgeConjecture.Mathlib.Algebra.Homology.MapExtend
import Other.AlgebraicTopology.Singular.EmptySubspace

/-! # The actual global stage-zero subdivision comparison -/

noncomputable section
open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite AlgebraicTopology.Singular
open HodgeLean.Foundations.RationalHomologyManifold
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace HodgeLean.Foundations.QuotientDuality

/-- Global sheafification of each original relative-chain presheaf is invertible on a compact space. -/
lemma retained_raw_global_chain_sheafification_isIso
    (X : TopCat.{0}) [CompactSpace X] [T2Space X] (n : ℕ) :
    IsIso ((toSheafify (Opens.grothendieckTopology X)
      (singularChainPresheaf ℚ X n)).app (op ⊤)) := by
  let J := forget₂ (ModuleCat ℚ) AddCommGrpCat
  let q := J.map ((relativeChainProjection ℚ
    (TopPair.ofSubset (X := X) ((⊤ : Opens X) : Set X)ᶜ)).f n)
  haveI : IsIso q := by
    change IsIso (J.map ((relativeChainProjection ℚ
      (TopPair.ofSubset (X := X) ((Set.univ : Set X)ᶜ))).f n))
    rw [Set.compl_univ]
    infer_instance
  haveI := retained_global_chain_sheaf_section_isIso X
  let t := (toSheafify (Opens.grothendieckTopology X)
    (singularChainPresheaf ℚ X n)).app (op ⊤)
  haveI : IsIso (q ≫ t) := by
    rw [show q ≫ t = (retainedChainSheafSectionMap X ⊤).f n from
      (retained_chain_sheaf_section_component X ⊤ n).symm]
    infer_instance
  exact IsIso.of_isIso_comp_left q t

/-- The canonical global chain-sheafification unit is an isomorphism of actual complexes. -/
lemma retained_raw_global_chain_sheafification_complex_isIso
    (X : TopCat.{0}) [CompactSpace X] [T2Space X] :
    IsIso ((((evaluation (Opens X)ᵒᵖ AddCommGrpCat).obj (op ⊤)).mapHomologicalComplex
      (.down ℕ)).map (singularChainSheafificationUnit ℚ X)) := by
  letI (n : ℕ) : IsIso
      (((((evaluation (Opens X)ᵒᵖ AddCommGrpCat).obj (op ⊤)).mapHomologicalComplex
        (.down ℕ)).map (singularChainSheafificationUnit ℚ X)).f n) :=
    retained_raw_global_chain_sheafification_isIso X n
  exact HomologicalComplex.Hom.isIso_of_components _

/-- The literal global stage-zero subdivision map retains ordinary chain homology. -/
lemma retained_global_subdivision_stage_quasiIso
    (X : TopCat.{0}) [CompactSpace X] [T2Space X] :
    QuasiIso (((subdivisionGlobalSectionsFunctor X).mapHomologicalComplex (.down ℕ)).map
      (subdivisionSheafStage X 0)) := by
  let E := (evaluation (Opens X)ᵒᵖ AddCommGrpCat).obj (op ⊤)
  let U := E.mapHomologicalComplex (.down ℕ)
  let G := (subdivisionGlobalSectionsFunctor X).mapHomologicalComplex (.down ℕ)
  let a := colimit.ι (presheafSubdivisionDiagram X) 0
  let r := U.map (singularChainSheafificationUnit ℚ X)
  let s := G.map (subdivisionSheafStage X 0)
  let t := U.map a
  have h : r ≫ s = t ≫ subdivisionGlobalSheafificationMap X := by
    ext n : 1
    exact (congrArg (fun f => f.app (op ⊤))
      (toSheafify_naturality (Opens.grothendieckTopology X) (a.f n))).symm
  letI := retained_raw_global_chain_sheafification_complex_isIso X
  letI := subdivisionPresheafStage_zero_quasiIso X
  letI : QuasiIso t := by dsimp only [t]; infer_instance
  letI := subdivisionGlobalSheafificationMap_isIso X
  haveI : QuasiIso (r ≫ s) := by rw [h]; infer_instance
  exact quasiIso_of_comp_left r s

/-- The actual global stage-zero comparison retains homology in the original negative grading. -/
lemma retained_global_subdivision_cochain_stage_quasiIso
    (X : TopCat.{0}) [CompactSpace X] [T2Space X] :
    QuasiIso (((subdivisionGlobalSectionsFunctor X).mapHomologicalComplex (.up ℤ)).map
      (subdivisionSheafCochainStage X 0)) := by
  let F := subdivisionGlobalSectionsFunctor X
  let φ := subdivisionSheafStage X 0
  let g := (F.mapHomologicalComplex (.up ℤ)).map
    (HomologicalComplex.extendMap φ ComplexShape.embeddingDownNat)
  let eL := HomologicalComplex.mapExtendCanonicalIso F
    (subdivisionLimitSheafComplex X) ComplexShape.embeddingDownNat
  letI : QuasiIso ((F.mapHomologicalComplex (.down ℕ)).map φ) :=
    retained_global_subdivision_stage_quasiIso X
  have h := HomologicalComplex.mapExtendCanonicalIso_naturality F
    (singularChainSheafComplex ℚ X) ComplexShape.embeddingDownNat φ
  haveI : QuasiIso (g ≫ eL.hom) := by
    dsimp only [g, eL]
    rw [h]
    infer_instance
  exact quasiIso_of_comp_right g eL.hom

end HodgeLean.Foundations.QuotientDuality
