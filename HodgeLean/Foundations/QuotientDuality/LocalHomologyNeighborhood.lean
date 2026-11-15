import HodgeLean.RealDefs.Port.AlgebraicTopology.Singular.Sheaf.ChainStalk
import HodgeLean.Foundations.QuotientDuality.LocalChainSupport
import HodgeLean.RealDefs.ComplexFundamentalClassParts.B_HomologyMaps

/-! Pointwise vanishing of supported singular classes persists on a smaller neighborhood. -/
noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits TopologicalSpace AlgebraicTopology.Singular
open HodgeLean.RealDefs
namespace HodgeLean.Foundations.QuotientDuality

/-- A supported class whose value at a point is zero vanishes on a neighborhood of that point.
Source: Hatcher, Algebraic Topology, proof of Lemma 3.27. -/
theorem relative_class_zero_on_neighborhood (X : TopCat.{0}) [T2Space X]
    (n : ℕ) (U : Opens X) (x : X) (hx : x ∈ U)
    (α : RelativeHomology ℚ (TopPair.ofSubset (X := X) (U : Set X)ᶜ) n)
    (hα : relativeHomologyMap ℚ n
      (supportInclusionPairMap X (Set.singleton_subset_iff.mpr hx)) α = 0) :
    ∃ (V : Opens X) (hxV : x ∈ V) (hVU : V ≤ U),
      relativeHomologyMap ℚ n (supportInclusionPairMap X hVU) α = 0 := by
  let P := TopPair.ofSubset (X := X) (U : Set X)ᶜ
  let Q := pointComplementPair x
  let C := SingularChainComplex ℚ (TopCat.of X)
  let CP := (relativeChainFunctor ℚ).obj P
  let CQ := (relativeChainFunctor ℚ).obj Q
  let πP : C ⟶ CP := relativeChainProjection ℚ P
  let πQ : C ⟶ CQ := relativeChainProjection ℚ Q
  let f := (relativeChainFunctor ℚ).map
    (supportInclusionPairMap X (Set.singleton_subset_iff.mpr hx))
  obtain ⟨a, rfl⟩ := (ModuleCat.epi_iff_surjective (CP.homologyπ n)).mp inferInstance α
  let aQ := (HomologicalComplex.cyclesMap f n).hom a
  have haQ : (CQ.homologyπ n).hom aQ = 0 := by
    have h := congrArg (fun g => g.hom a) (HomologicalComplex.homologyπ_naturality f n)
    exact h.symm.trans hα
  obtain ⟨bQ, hbQ⟩ := cycle_boundary_of_homology_zero CQ n aQ haQ
  obtain ⟨b, hb⟩ := C_relativeChainProjection_surjective Q (n + 1) bQ
  obtain ⟨z, hz⟩ := C_relativeChainProjection_surjective P n ((CP.iCycles n).hom a)
  change C.X (n + 1) at b
  change C.X n at z
  change (πP.f n).hom z = (CP.iCycles n).hom a at hz
  change (πQ.f (n + 1)).hom b = bQ at hb
  have hπ : πP ≫ f = πQ := by
    exact relativeChainProjection_supportInclusion ℚ X
      (Set.singleton_subset_iff.mpr hx)
  have hzQ : (πQ.f n).hom z = (CQ.iCycles n).hom aQ := by
    rw [← hπ]
    change (f.f n).hom ((πP.f n).hom z) = _
    rw [hz]
    exact congrArg (fun g => g.hom a) (HomologicalComplex.cyclesMap_i f n).symm
  have hd : (πQ.f n).hom (z - (C.d (n + 1) n).hom b) = 0 := by
    rw [map_sub, hzQ]
    have h := congrArg (fun g => g.hom b) (πQ.comm (n + 1) n).symm
    change (πQ.f n).hom ((C.d (n + 1) n).hom b) =
      (CQ.d (n + 1) n).hom ((πQ.f (n + 1)).hom b) at h
    rw [h, hb, hbQ, sub_self]
  obtain ⟨c, hc⟩ := C_relativeChainProjection_exact Q n _ hd
  obtain ⟨W, hxW, hW⟩ := complement_chain_vanishes_near_point X x n c
  let V := U ⊓ W
  have hVU : V ≤ U := inf_le_left
  have hVW : V ≤ W := inf_le_right
  let PV := TopPair.ofSubset (X := X) (V : Set X)ᶜ
  let CV := (relativeChainFunctor ℚ).obj PV
  let πV := relativeChainProjection ℚ PV
  let g := (relativeChainFunctor ℚ).map (supportInclusionPairMap X hVU)
  have hdiff : (πV.f n).hom (z - (C.d (n + 1) n).hom b) = 0 := by
    rw [← hc]
    have hp := relativeChainProjection_supportInclusion ℚ X hVW
    have hh := congrArg (fun q => (q.f n).hom
      (((((chainPairFunctor ℚ).obj Q).hom).f n).hom c)) hp
    change _ = (πV.f n).hom _ at hh
    rw [← hh]
    change (relativeChainFunctor ℚ |>.map (supportInclusionPairMap X hVW) |>.f n).hom
      (((relativeChainProjection ℚ (TopPair.ofSubset (X := X) (W : Set X)ᶜ)).f n).hom
        (((((chainPairFunctor ℚ).obj Q).hom).f n).hom c)) = 0
    rw [hW, map_zero]
  have hzV : (πV.f n).hom z = (CV.d (n + 1) n).hom ((πV.f (n + 1)).hom b) := by
    have h := congrArg (fun q => q.hom b) (πV.comm (n + 1) n)
    rw [map_sub, sub_eq_zero] at hdiff
    exact hdiff.trans h.symm
  let aV := (HomologicalComplex.cyclesMap g n).hom a
  have hiV : (CV.iCycles n).hom aV = (πV.f n).hom z := by
    have hg := relativeChainProjection_supportInclusion ℚ X hVU
    have hn := congrArg (fun q => q.hom a) (HomologicalComplex.cyclesMap_i g n)
    change _ = (g.f n).hom ((CP.iCycles n).hom a) at hn
    rw [← hz] at hn
    exact hn.trans (congrArg (fun q => (q.f n).hom z) hg)
  have haV : (CV.toCycles (n + 1) n).hom ((πV.f (n + 1)).hom b) = aV := by
    apply (ModuleCat.mono_iff_injective (CV.iCycles n)).mp inferInstance
    change ((CV.toCycles (n + 1) n ≫ CV.iCycles n).hom _) = _
    rw [CV.toCycles_i, hiV, hzV]
  refine ⟨V, ⟨hx, hxW⟩, hVU, ?_⟩
  have hn := congrArg (fun q => q.hom a) (HomologicalComplex.homologyπ_naturality g n)
  change (HomologicalComplex.homologyMap g n).hom ((CP.homologyπ n).hom a) =
    (CV.homologyπ n).hom aV at hn
  change (HomologicalComplex.homologyMap g n).hom ((CP.homologyπ n).hom a) = 0
  rw [hn, ← haV]
  exact congrArg (fun q => q.hom ((πV.f (n + 1)).hom b))
    (CV.toCycles_comp_homologyπ (n + 1) n)

#print axioms relative_class_zero_on_neighborhood
end HodgeLean.Foundations.QuotientDuality
