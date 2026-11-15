import HodgeLean.Foundations.Program.SchoenTransferE1CurveAction
import HodgeLean.RealDefs.Port.AlgebraicGeometry.ComplexPoint.CoclassSchemeIso

/-! Top-degree action through the exact complex local orientation. -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
set_option maxRecDepth 4000

open CategoryTheory TopologicalSpace AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open AlgebraicTopology.Singular
open HodgeLean.RealDefs HodgeLean.Adapters HodgeLean.Foundations

namespace HodgeLean.Foundations.Program

/-- The actual morphism on the pair with empty removed support.
Source: Hatcher, Algebraic Topology, §2.1, functoriality of relative homology. -/
def s4_e1_fullPairMap (Y : Over (Spec ↧ℂ)) (δ : Y ⟶ Y) :
    TopPair.ofSubset (((⊤ : Opens (ComplexPoint Y)) : Set (ComplexPoint Y))ᶜ :
      Set (TopCat.of (ComplexPoint Y))) ⟶
    TopPair.ofSubset (((⊤ : Opens (ComplexPoint Y)) : Set (ComplexPoint Y))ᶜ :
      Set (TopCat.of (ComplexPoint Y))) :=
  TopPair.ofSubsetHom (TopCat.ofHom (Point.continuousMap δ)) (by
    intro x hx
    exact False.elim (by simpa only [Opens.coe_top, Set.compl_univ,
      Set.mem_empty_iff_false] using hx))

/-- Complex scheme automorphisms act identically on top homology.
Source: Hatcher, Algebraic Topology, Theorem 3.26; preservation of complex local orientation. -/
theorem s4_e1_top_homology_action
    (Y : Over (Spec ↧ℂ)) [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]
    (d : ℕ) [SmoothOfRelativeDimension d Y.hom] (e : Y ≅ Y)
    (v : RelativeHomology ℚ (TopPair.ofSubset
      (((⊤ : Opens (ComplexPoint Y)) : Set (ComplexPoint Y))ᶜ :
        Set (TopCat.of (ComplexPoint Y)))) (2 * d)) :
    relativeHomologyMap ℚ (2 * d) (s4_e1_fullPairMap Y e.hom) v = v := by
  letI := pathConnectedSpace_complexPoint Y
  obtain ⟨q, hq⟩ := exists_relativeHomologyMap_eq_smul_complexLocalOrientation Y d v
  suffices heq : relativeHomologyMap ℚ (2 * d) (s4_e1_fullPairMap Y e.hom) v =
      (1 : ℚ) • v by simpa only [one_smul] using heq
  apply j5d_eq_smul_of_pointValues (E := Fin d → ℂ)
    (finrank_real_complexCoordinates d)
    (relativeHomologyMap ℚ (2 * d) (s4_e1_fullPairMap Y e.hom) v) v 1
  intro y
  obtain ⟨z, rfl⟩ := (Point.isoMapHomeomorph e).surjective y
  have hs : s4_e1_fullPairMap Y e.hom ≫
      supportInclusionPairMap (TopCat.of (ComplexPoint Y))
        (Set.singleton_subset_iff.mpr (Opens.mem_top (Point.map e.hom z))) =
      supportInclusionPairMap (TopCat.of (ComplexPoint Y))
        (Set.singleton_subset_iff.mpr (Opens.mem_top z)) ≫
        complexSchemeIsoPointPairMap Y Y e z := by
    apply MorphismProperty.Arrow.Hom.ext <;> ext x <;> rfl
  change relativeHomologyMap ℚ (2 * d)
    (supportInclusionPairMap (TopCat.of (ComplexPoint Y))
      (Set.singleton_subset_iff.mpr (Opens.mem_top (Point.map e.hom z))))
    (relativeHomologyMap ℚ (2 * d) (s4_e1_fullPairMap Y e.hom) v) =
    (1 : ℚ) • relativeHomologyMap ℚ (2 * d)
      (supportInclusionPairMap (TopCat.of (ComplexPoint Y))
        (Set.singleton_subset_iff.mpr (Opens.mem_top (Point.map e.hom z)))) v
  rw [relativeHomologyMap_apply_apply, hs, ← relativeHomologyMap_apply_apply,
    hq z, map_smul, hq (Point.map e.hom z), one_smul]
  congr 1
  exact complexSchemeIsoPointPairMap_localClass Y Y e d z

/-- Complex scheme automorphisms act identically on top singular cohomology.
Source: Hatcher, Algebraic Topology, Theorem 3.26 and the universal coefficient theorem. -/
theorem s4_e1_top_cohomology_action
    (Y : Over (Spec ↧ℂ)) [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]
    (d : ℕ) [SmoothOfRelativeDimension d Y.hom] (e : Y ≅ Y) :
    cohomologyMap ℚ (2 * d) (TopCat.ofHom (Point.continuousMap e.hom)) =
      LinearMap.id := by
  let P := TopPair.ofSubset
    (((⊤ : Opens (ComplexPoint Y)) : Set (ComplexPoint Y))ᶜ :
      Set (TopCat.of (ComplexPoint Y)))
  letI : IsIso (relativeChainProjection ℚ P) := by
    change IsIso (relativeChainProjection ℚ
      (TopPair.ofSubset ((Set.univ : Set (TopCat.of (ComplexPoint Y)))ᶜ)))
    rw [Set.compl_univ]
    exact CategoryTheory.Limits.cokernel.π_of_zero
      (j5d_emptyPair_chainMap_eq_zero (TopCat.of (ComplexPoint Y)))
  let ei := HomologicalComplex.homologyMapIso
    (asIso (relativeChainProjection ℚ P)) (2 * d)
  have hi := ((ConcreteCategory.isIso_iff_bijective ei.hom).mp ei.isIso_hom).1
  apply LinearMap.ext
  intro α
  apply (cohomologyEquivDualHomology ℚ (TopCat.of (ComplexPoint Y)) (2 * d)).injective
  apply LinearMap.ext
  intro z
  rw [cohomologyEquivDualHomology_cohomologyMap, LinearMap.id_apply]
  have hz : homologyMap ℚ (2 * d) (TopCat.ofHom (Point.continuousMap e.hom)) z = z := by
    apply hi
    have ht := congrArg (fun k => HomologicalComplex.homologyMap k (2 * d))
      (TopPair.Homotopy.relativeChainProjection_naturality (R := ℚ)
        (s4_e1_fullPairMap Y e.hom))
    simp only [HomologicalComplex.homologyMap_comp] at ht
    have hh := ConcreteCategory.congr_hom ht z
    change relativeHomologyMap ℚ (2 * d) (s4_e1_fullPairMap Y e.hom)
      ((relativeHomologyProjection ℚ P (2 * d)).hom z) =
      (relativeHomologyProjection ℚ P (2 * d)).hom
        (homologyMap ℚ (2 * d) (TopCat.ofHom (Point.continuousMap e.hom)) z) at hh
    rw [s4_e1_top_homology_action] at hh
    exact hh.symm
  exact congrArg (cohomologyEquivDualHomology ℚ (TopCat.of (ComplexPoint Y)) (2 * d) α) hz

/-- The specified rational pullback has the same top-degree action.
Source: Hatcher, Algebraic Topology, Theorem 3.26; the definition of `homPullback`. -/
theorem s4_e1_top_rational_action
    (Y : Over (Spec ↧ℂ)) [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]
    (d : ℕ) [SmoothOfRelativeDimension d Y.hom] (e : Y ≅ Y) :
    homPullback e.hom (2 * d) = LinearMap.id := by
  apply LinearMap.ext
  intro x
  apply (cupComparison Y (2 * d)).injective
  simp only [homPullback, LinearMap.comp_apply, LinearEquiv.coe_toLinearMap,
    LinearEquiv.apply_symm_apply, LinearMap.id_apply]
  rw [s4_e1_top_cohomology_action, LinearMap.id_apply]

#print axioms s4_e1_top_homology_action
#print axioms s4_e1_top_cohomology_action
#print axioms s4_e1_top_rational_action
end HodgeLean.Foundations.Program
