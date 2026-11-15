import HodgeLean.Foundations.QuotientDuality.ProperCycleProductSupport
import HodgeLean.Adapters.NormalConeB4aClassSheaf
import HodgeLean.Adapters.NormalConeB4aClassLocalGlobal
import HodgeLean.Adapters.NormalConeB4aClassExtension

/-! # Local purity from actual product charts and normal homology -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory Limits AlgebraicTopology.Singular TopologicalSpace Opposite
open HodgeLean.Adapters
namespace HodgeLean.Foundations.QuotientDuality

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- A product chart transfers actual normal-point homology vanishing to local supported cohomology.
Source: Bredon, Sheaf Theory, second edition, V.9, local product support calculations;
Hatcher, Algebraic Topology, sections 2.1 and 3.1.
HC no distance; AV milestone no distance. -/
lemma properCycle_product_chart_support_subsingleton
    (X : TopCat.{0}) (A : Set X) (W : Opens X)
    (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E]
    (Y : TopCat.{0}) (y : Y) (e : W ≃ₜ (E × Y))
    (he : ∀ w : W, (w : X) ∈ A ↔ (e w).2 = y)
    (n : ℕ) (hvan : Subsingleton (orientationGroup Y n y)) :
    Subsingleton (RelativeCohomology ℚ
      (neighborhoodSupportComplementPair (W : Set X) A) n) := by
  let p : neighborhoodSupportComplementPair (W : Set X) A ≅
      TopPair.ofSubset (X := TopCat.of (E × Y)) (Prod.snd ⁻¹' ({y} : Set Y)ᶜ) :=
    TopPair.isoOfSubset e (fun w => not_congr (he w).symm)
  let C := (HomologicalComplex.homologyFunctor (ModuleCat.{0} ℚ)
    (ComplexShape.up ℕ) n).mapIso
      (HomologicalComplex.linearDualIso ((relativeChainFunctor ℚ).mapIso p))
  letI : Subsingleton (RelativeCohomology ℚ
      (TopPair.ofSubset (X := TopCat.of (E × Y)) (Prod.snd ⁻¹' ({y} : Set Y)ᶜ)) n) :=
    properCycle_product_point_support_subsingleton E Y y n hvan
  exact @Function.Injective.subsingleton _ _ C.toLinearEquiv.symm
    C.toLinearEquiv.symm.injective
    (properCycle_product_point_support_subsingleton E Y y n hvan)

/-- Cofinal actual product charts with vanishing normal homology give a zero supported cohomology sheaf.
Source: Bredon, Sheaf Theory, second edition, I.6 and V.9, stalk detection and local product models.
HC no distance; AV milestone no distance. -/
lemma properCycle_product_charts_sheaf_vanishes
    (X : TopCat.{0}) (A : Set X) (hA : IsClosed A) (n : ℕ)
    (hcharts : ∀ x ∈ A, ∀ U : Opens X, x ∈ U →
      ∃ W : Opens X, W ≤ U ∧ x ∈ W ∧
        ∃ (r : ℕ) (Y : TopCat.{0}) (y : Y) (e : W ≃ₜ ((Fin r → ℂ) × Y)),
          (∀ w : W, (w : X) ∈ A ↔ (e w).2 = y) ∧
          Subsingleton (orientationGroup Y n y)) :
    IsZero (supportRelativeCohomologySheaf X A n) := by
  apply (TopCat.Sheaf.isZero_iff_stalkFunctor_obj_isZero _).mpr
  intro x
  let P := supportRelativeCohomologyPresheaf X A n
  have hP : IsZero (P.stalk x) := by
    apply TopCat.Presheaf.isZero_stalk_of_cofinal_sections
    intro U hxU
    by_cases hxA : x ∈ A
    · obtain ⟨W, hWU, hxW, r, Y, y, e, he, hvan⟩ := hcharts x hxA U hxU
      refine ⟨W, hWU, hxW, ?_⟩
      letI : Subsingleton (P.obj (op W)) :=
        properCycle_product_chart_support_subsingleton X A W (Fin r → ℂ) Y y e he n hvan
      exact AddCommGrpCat.isZero_of_subsingleton _
    · let W : Opens X := U ⊓ ⟨Aᶜ, hA.isOpen_compl⟩
      refine ⟨W, inf_le_left, ⟨hxU, hxA⟩, ?_⟩
      letI : Subsingleton (P.obj (op W)) :=
        neighborhoodSupportRelativeCohomology_subsingleton X A n W (fun _ hy => hy.2)
      exact AddCommGrpCat.isZero_of_subsingleton _
  let η := supportRelativeCohomologyToSheaf X A n
  letI : IsIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map η) :=
    TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso x AddCommGrpCat P
  exact hP.of_iso (asIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map η)).symm

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- Cofinal product normal models through a degree give supported vanishing on every analytic open.
Source: Bredon, Sheaf Theory, second edition, II.10 and V.9, supported localization and product models;
a3b4a_classRelative_vanishing_of_cofinal_local_vanishing.
HC no distance; AV milestone no distance. -/
lemma properCycle_product_charts_relative_vanishes
    (X : TopCat.{0}) [T2Space X] [∀ V : Opens X, ParacompactSpace V]
    (S : Closeds X) (n : ℕ)
    (hcharts : ∀ j : ℕ, j ≤ n → ∀ x ∈ S, ∀ V : Opens X, x ∈ V →
      ∃ W : Opens X, W ≤ V ∧ x ∈ W ∧
        ∃ (r : ℕ) (Y : TopCat.{0}) (y : Y) (e : W ≃ₜ ((Fin r → ℂ) × Y)),
          (∀ w : W, (w : X) ∈ S ↔ (e w).2 = y) ∧
          Subsingleton (orientationGroup Y j y))
    (U : Opens X) :
    IsZero (RelativeCohomology ℚ
      (neighborhoodSupportComplementPair (U : Set X) (S : Set X)) n) := by
  apply a3b4a_classRelative_vanishing_of_cofinal_local_vanishing X S U n
  intro j hj x hxU V hxV
  by_cases hxS : x ∈ S
  · obtain ⟨W, hWV, hxW, r, Y, y, e, he, hvan⟩ := hcharts j hj x hxS V hxV
    refine ⟨W, hWV, hxW, ?_⟩
    exact ModuleCat.isZero_iff_subsingleton.mpr
      (properCycle_product_chart_support_subsingleton X S W (Fin r → ℂ) Y y e he j hvan)
  · let W : Opens X := V ⊓ S.compl
    refine ⟨W, inf_le_left, ⟨hxV, hxS⟩, ?_⟩
    exact ModuleCat.isZero_iff_subsingleton.mpr
      (neighborhoodSupportRelativeCohomology_subsingleton X S j W (fun _ hy => hy.2))

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- Supported restriction across a boundary with cofinal normal product models is bijective.
Source: Bredon, Sheaf Theory, second edition, II.10 and V.9, localization for nested supports.
HC no distance; AV milestone no distance. -/
lemma properCycle_restrict_off_product_boundary_bijective
    (X : TopCat.{0}) [T2Space X] [∀ V : Opens X, ParacompactSpace V]
    (S B : Closeds X) (hBS : B ≤ S) (n : ℕ)
    (hcharts : ∀ j : ℕ, j ≤ n + 1 → ∀ x ∈ B, ∀ V : Opens X, x ∈ V →
      ∃ W : Opens X, W ≤ V ∧ x ∈ W ∧
        ∃ (r : ℕ) (Y : TopCat.{0}) (y : Y) (e : W ≃ₜ ((Fin r → ℂ) × Y)),
          (∀ w : W, (w : X) ∈ B ↔ (e w).2 = y) ∧
          Subsingleton (orientationGroup Y j y)) :
    Function.Bijective (relativeCohomologyMap ℚ n
      (a3b4_neighborhoodPairMap (B.compl : Set X) (S : Set X))) := by
  let r := relativeCohomologyMap ℚ n
    (neighborhoodSupportInclusionPairMap
      (show (B.compl : Set X) ⊆ Set.univ from Set.subset_univ _) (S : Set X))
  have hr : Function.Bijective r := by
    apply a3b4a_classRelative_restriction_bijective_of_boundary_vanishing X S B hBS n
    intro j hj
    have hjbound : j ≤ n + 1 := by
      simp only [Finset.mem_insert, Finset.mem_singleton] at hj
      rcases hj with rfl | rfl <;> omega
    exact properCycle_product_charts_relative_vanishes X B j
      (fun l hl => hcharts l (hl.trans hjbound)) ⊤
  let e : TopPair.ofSubset (X := X) (S : Set X)ᶜ ≅
      neighborhoodSupportComplementPair (Set.univ : Set X) (S : Set X) :=
    TopPair.isoOfSubset (Homeomorph.Set.univ X).symm (fun _ => Iff.rfl)
  let E := (HomologicalComplex.homologyFunctor (ModuleCat.{0} ℚ)
    (ComplexShape.up ℕ) n).mapIso
      (HomologicalComplex.linearDualIso ((relativeChainFunctor ℚ).mapIso e.symm))
  have he : Function.Bijective (relativeCohomologyMap ℚ n e.inv) :=
    E.toLinearEquiv.bijective
  have hcomp : r.comp (relativeCohomologyMap ℚ n e.inv) =
      relativeCohomologyMap ℚ n
        (a3b4_neighborhoodPairMap (B.compl : Set X) (S : Set X)) := by
    dsimp only [r]
    rw [← relativeCohomologyMap_comp]
    rfl
  rw [← hcomp]
  exact hr.comp he

end HodgeLean.Foundations.QuotientDuality
