import HodgeLean.Foundations.BundleThom.SubcomplexFiniteDistributivityHelpers
import HodgeLean.Foundations.BundleThom.RelativeFinsetUnionLowHomologyHelpers
import HodgeLean.Foundations.BundleThom.BinaryChainCoclassDetectionHelpers

/-! # Degree-two coclass detection on finite actual relative chain unions

Pairwise degree-one and triple degree-zero calculations supply the finite induction.
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Limits AlgebraicTopology
namespace HodgeLean.Foundations.BundleThom

/-- Actual finite-domain restrictions detect relative degree-two coclasses when pairwise degree-one and triple degree-zero intersection homology vanish.
Source: Hatcher, Algebraic Topology, §2.2 and §3.1, finite relative Mayer–Vietoris induction. -/
theorem i1_relativeSubcomplexFinsetCoclass_ext {ι : Type}
    (X : SSet) (Z : X.Subcomplex) (U : ι → X.Subcomplex) (s : Finset ι) :
    s.Nonempty →
    (∀ i ∈ s, ∀ j ∈ s,
      IsZero (((i1_relativeSubcomplexChainFunctor X Z).obj (U i ⊓ U j)).homology 1)) →
    (∀ i ∈ s, ∀ j ∈ s, ∀ t ∈ s,
      IsZero (((i1_relativeSubcomplexChainFunctor X Z).obj (U i ⊓ U j ⊓ U t)).homology 0)) →
    ∀ (u v : ((i1_relativeSubcomplexChainFunctor X Z).obj (s.sup U)).linearDualCochainComplex.homology 2),
      (∀ (i : ι) (_ : i ∈ s) (hUi : U i ≤ s.sup U), i1_chainDualPullback 2
          ((i1_relativeSubcomplexChainFunctor X Z).map (homOfLE hUi)) u =
        i1_chainDualPullback 2
          ((i1_relativeSubcomplexChainFunctor X Z).map (homOfLE hUi)) v) → u = v := by
  classical
  let F := i1_relativeSubcomplexChainFunctor X Z
  induction s using Finset.induction_on with
  | empty =>
    intro hs
    exact False.elim (Finset.not_nonempty_empty hs)
  | @insert a s ha ih =>
    intro hs hp ht
    by_cases hsn : s.Nonempty
    · have hz : IsZero ((F.obj (U a ⊓ s.sup U)).homology 1) := by
        rw [i1_subcomplex_inf_finsetSup X (U a) U s]
        apply i1_relativeSubcomplexFinsetSupHomologyOne_isZero X Z (fun i => U a ⊓ U i) s hsn
        · intro i hi
          exact hp a (Finset.mem_insert_self _ _) i (Finset.mem_insert_of_mem hi)
        · intro i hi j hj
          simpa only [inf_assoc, inf_left_comm, inf_idem, inf_left_idem] using
            ht a (Finset.mem_insert_self _ _) i (Finset.mem_insert_of_mem hi)
              j (Finset.mem_insert_of_mem hj)
      rw [Finset.sup_insert]
      intro u v h
      haveI := i1_relativeSubcomplexChainMap_mono X Z (U a ⊓ s.sup U) (U a) inf_le_left
      apply i1_binaryChainCoclass_ext (i1_relativeSubcomplexChains_isPushout X Z (U a) (s.sup U))
        1 hz u v
      · exact h a (Finset.mem_insert_self _ _) le_sup_left
      · apply ih hsn
          (fun i hi j hj => hp i (Finset.mem_insert_of_mem hi) j (Finset.mem_insert_of_mem hj))
          (fun i hi j hj t htm => ht i (Finset.mem_insert_of_mem hi)
            j (Finset.mem_insert_of_mem hj) t (Finset.mem_insert_of_mem htm))
        intro i hi hUi
        rw [← LinearMap.comp_apply, ← i1_chainDualPullback_comp, ← F.map_comp,
          ← LinearMap.comp_apply, ← i1_chainDualPullback_comp, ← F.map_comp]
        exact h i (Finset.mem_insert_of_mem hi) (hUi.trans le_sup_right)
    · have hse : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hsn
      subst s
      rw [Finset.sup_insert, Finset.sup_empty, sup_bot_eq]
      intro u v h
      have hh := h a (Finset.mem_insert_self _ _) le_rfl
      change i1_chainDualPullback 2 (F.map (𝟙 (U a))) u =
        i1_chainDualPullback 2 (F.map (𝟙 (U a))) v at hh
      simpa only [F.map_id, i1_chainDualPullback_id, LinearMap.id_apply] using hh

end HodgeLean.Foundations.BundleThom
