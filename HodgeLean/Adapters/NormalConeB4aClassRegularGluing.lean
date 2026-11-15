import HodgeLean.Adapters.NormalConeB4aClassConstantChart
import HodgeLean.Adapters.NormalConeB4aClassHolomorphicOverlap
import HodgeLean.Adapters.NormalConeB4aClassGluingOnOpen
import HodgeLean.Adapters.NormalConeB4aClassCycleExtension

/-! # Gluing weighted normal coclasses away from the regular boundary

Route: choose constant multiplicity normal charts, compare their weighted
germs on overlaps, and glue using lower support purity.
-/
noncomputable section
namespace HodgeLean.Adapters
open CategoryTheory Limits AlgebraicGeometry AlgebraicTopology.Singular TopologicalSpace
open HodgeLean.Foundations.Analytic

set_option maxHeartbeats 400000 in
set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- On the regular boundary complement, weighted normal coclasses glue and
have the prescribed normalization in every holomorphic normal chart. -/
theorem a3b4a_classRegular_normalCoclass_glue
    {Z : Scheme.{0}} (q : Z ⟶ Spec (CommRingCat.of ℂ)) [Smooth q]
    [QuasiCompact q] [IsSeparated q] (γ : AlgebraicCycle Z ℚ) (c : ℕ)
    (hc : ∀ ξ ∈ γ.support, (c : ℕ∞) ≤ Order.coheight ξ) :
    let U : Opens (a3b4_an q) := ((a3b4a_classRegularBoundary q γ c).preimage
      (ComplexPoint.continuous_underlying_to_zariski (Over.mk q))).compl
    ∃ b : RelativeCohomology ℚ
      (neighborhoodSupportComplementPair (U : Set (a3b4_an q)) (a3b4_cycleSupport q γ)) (2 * c),
      ∀ (x : ComplexPoint (Over.mk q)), x ∈ a3b4_cycleSupport q γ → x ∈ U →
      ∀ (r : ℕ) (e : OpenPartialHomeomorph (ComplexPoint (Over.mk q))
        ((Fin r → ℂ) × (Fin c → ℂ))) (he : a3b4_IsHolChart q e)
        (hS : ∀ y ∈ e.source, y ∈ a3b4_cycleSupport q γ ↔ (e y).2 = 0),
        x ∈ e.source → ∃ (W : Opens (a3b4_an q)) (hWU : W ≤ U)
          (hWe : (W : Set (a3b4_an q)) ⊆ e.source), x ∈ W ∧
          relativeCohomologyMap ℚ (2 * c)
            (neighborhoodSupportInclusionPairMap hWU (a3b4_cycleSupport q γ)) b =
          a3b4_multiplicity q γ x •
            chartNormalProjectionCoclass (Fin r → ℂ) c e (a3b4_cycleSupport q γ) hS W hWe := by
  classical
  letI : Smooth (Over.mk q).hom := ‹Smooth q›
  letI : QuasiCompact (Over.mk q).hom := ‹QuasiCompact q›
  letI : IsSeparated (Over.mk q).hom := ‹IsSeparated q›
  letI : T2Space (ComplexPoint (Over.mk q)) := f4_t2Space (Over.mk q)
  letI (V : Opens (ComplexPoint (Over.mk q))) : ParacompactSpace V :=
    a3b4a_class_openParacompact q V
  dsimp only
  let X := a3b4_an q
  let S : Closeds X := ⟨a3b4_cycleSupport q γ, a3b4a_classSupport_isClosed q γ⟩
  let U : Opens X := ((a3b4a_classRegularBoundary q γ c).preimage
    (ComplexPoint.continuous_underlying_to_zariski (Over.mk q))).compl
  let I := {x : X // x ∈ S ∧ x ∈ U}
  have hcharts (x : I) := a3b4a_classRegularBoundary_constantChart q γ c hc x.1 x.2.1 x.2.2
  choose r e hxe he hflat hB hmult using hcharts
  let V (i : I) : Opens X := ⟨(e i).source, (e i).open_source⟩
  have hVU (i : I) : V i ≤ U := hB i
  let a (i : I) : RelativeCohomology ℚ
      (neighborhoodSupportComplementPair (V i : Set X) S) (2 * c) :=
    a3b4_multiplicity q γ i.1 •
      chartNormalProjectionCoclass (Fin (r i) → ℂ) c (e i) S (hflat i) (V i) (le_refl _)
  have hcover : ∀ x ∈ U, x ∈ S → ∃ i, x ∈ V i := by
    intro x hxU hxS
    exact ⟨⟨x, hxS, hxU⟩, hxe ⟨x, hxS, hxU⟩⟩
  have hcompat : ∀ i j x (hi : x ∈ V i) (hj : x ∈ V j), x ∈ S →
      supportRelativeCohomologyGerm X S (2 * c) (V i) x hi (a i) =
        supportRelativeCohomologyGerm X S (2 * c) (V j) x hj (a j) := by
    intro i j x hi hj hxS
    obtain ⟨W, hWi, hWj, hxW, heq⟩ :=
      a3b4a_classHolomorphicChart_normalCoclass_overlap (Over.mk q) (e i) (e j)
        (he i) (he j) S (hflat i) (hflat j) x hi hj hxS
    apply supportRelativeCohomologyGerm_eq_of_restrict_eq X S (2 * c) hWi hWj x hxW
    dsimp only [a]
    rw [map_smul, map_smul, chartNormalProjectionCoclass_restrict,
      chartNormalProjectionCoclass_restrict, heq]
    rw [← hmult i x hi hxS, ← hmult j x hj hxS]
  have hlower (j : ℕ) (hj : j < 2 * c) :
      IsZero (supportRelativeCohomologySheaf X S j) :=
    a3b4a_classSheaf_purity_vanishing q (a3b4a_classAlgebraicSupport q γ) c
      (a3b4a_classAlgebraicSupport_coheight q γ c hc) j hj
  obtain ⟨b, hb⟩ := a3b4a_classRelative_glue_onOpen X S (2 * c) hlower U V hVU a hcover hcompat
  refine ⟨b, ?_⟩
  intro x hxS hxU s e' he' hS' hx'
  let i : I := ⟨x, hxS, hxU⟩
  obtain ⟨W, hWi, hW', hxW, heq⟩ :=
    a3b4a_classHolomorphicChart_normalCoclass_overlap (Over.mk q) (e i) e'
      (he i) he' S (hflat i) hS' x (hxe i) hx' hxS
  change W ≤ V i at hWi
  have hWU : W ≤ U := hWi.trans (hVU i)
  refine ⟨W, hWU, hW', hxW, ?_⟩
  change relativeCohomologyMap ℚ (2 * c)
    (neighborhoodSupportInclusionPairMap (W := (W : Set X)) (V := (U : Set X)) hWU (S : Set X)) b =
    a3b4_multiplicity q γ x • chartNormalProjectionCoclass (Fin s → ℂ) c e' S hS' W hW'
  have hb' : relativeCohomologyMap ℚ (2 * c)
      (neighborhoodSupportInclusionPairMap (hVU i) (S : Set X)) b = a i := hb i
  have hcomp : relativeCohomologyMap ℚ (2 * c)
      (neighborhoodSupportInclusionPairMap hWU (S : Set X)) b =
      relativeCohomologyMap ℚ (2 * c)
        (neighborhoodSupportInclusionPairMap hWi (S : Set X))
        (relativeCohomologyMap ℚ (2 * c)
          (neighborhoodSupportInclusionPairMap (hVU i) (S : Set X)) b) := by
    rw [← LinearMap.comp_apply, ← relativeCohomologyMap_comp]
    rfl
  rw [hcomp, hb']
  dsimp only [a]
  rw [map_smul, chartNormalProjectionCoclass_restrict, heq]

end HodgeLean.Adapters
