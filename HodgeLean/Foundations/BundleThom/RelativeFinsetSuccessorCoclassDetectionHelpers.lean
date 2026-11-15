import HodgeLean.Foundations.BundleThom.SubcomplexFiniteDistributivityHelpers
import HodgeLean.Foundations.BundleThom.RelativeFiniteIntersectionVanishingHelpers
import HodgeLean.Foundations.BundleThom.BinaryChainCoclassDetectionHelpers

/-! # Successor-degree coclass detection on finite actual relative chain unions

Vanishing on every actual finite intersection supplies the degree induction.
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Limits AlgebraicTopology
namespace HodgeLean.Foundations.BundleThom

/-- Actual finite-domain restrictions detect relative successor-degree coclasses when all finite intersections vanish in the preceding and lower degrees.
Source: Hatcher, Algebraic Topology, §2.2 and §3.1, finite relative Mayer–Vietoris induction. -/
theorem i1_relativeSubcomplexFinsetSuccessorCoclass_ext {ι : Type}
    (X : SSet) (Z : X.Subcomplex) (n : ℕ) (U : ι → X.Subcomplex) (s : Finset ι) :
    s.Nonempty →
    (∀ t : Finset ι, t.Nonempty → ∀ m, m ≤ n →
      IsZero (((i1_relativeSubcomplexChainFunctor X Z).obj (t.inf U)).homology m)) →
    ∀ (u v : ((i1_relativeSubcomplexChainFunctor X Z).obj (s.sup U)).linearDualCochainComplex.homology (n + 1)),
      (∀ (i : ι) (_ : i ∈ s) (hUi : U i ≤ s.sup U), i1_chainDualPullback (n + 1)
          ((i1_relativeSubcomplexChainFunctor X Z).map (homOfLE hUi)) u =
        i1_chainDualPullback (n + 1)
          ((i1_relativeSubcomplexChainFunctor X Z).map (homOfLE hUi)) v) → u = v := by
  classical
  let F := i1_relativeSubcomplexChainFunctor X Z
  induction s using Finset.induction_on with
  | empty =>
    intro hs
    exact False.elim (Finset.not_nonempty_empty hs)
  | @insert a s ha ih =>
    intro hs hh
    by_cases hsn : s.Nonempty
    · have hz : IsZero ((F.obj (U a ⊓ s.sup U)).homology n) := by
        rw [i1_subcomplex_inf_finsetSup X (U a) U s]
        apply i1_relativeSubcomplexFinsetSupHomology_isZero_of_intersections X Z n
          (fun i => U a ⊓ U i) s hsn
        intro t ht m hm
        rw [i1_subcomplex_finsetInf_restrict X U a t ht]
        exact hh (insert a t) (Finset.insert_nonempty a t) m hm
      rw [Finset.sup_insert]
      intro u v h
      haveI := i1_relativeSubcomplexChainMap_mono X Z (U a ⊓ s.sup U) (U a) inf_le_left
      apply i1_binaryChainCoclass_ext (i1_relativeSubcomplexChains_isPushout X Z (U a) (s.sup U))
        n hz u v
      · exact h a (Finset.mem_insert_self _ _) le_sup_left
      · apply ih hsn hh
        intro i hi hUi
        rw [← LinearMap.comp_apply, ← i1_chainDualPullback_comp, ← F.map_comp,
          ← LinearMap.comp_apply, ← i1_chainDualPullback_comp, ← F.map_comp]
        exact h i (Finset.mem_insert_of_mem hi) (hUi.trans le_sup_right)
    · have hse : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hsn
      subst s
      rw [Finset.sup_insert, Finset.sup_empty, sup_bot_eq]
      intro u v h
      have hh := h a (Finset.mem_insert_self _ _) le_rfl
      change i1_chainDualPullback (n + 1) (F.map (𝟙 (U a))) u =
        i1_chainDualPullback (n + 1) (F.map (𝟙 (U a))) v at hh
      simpa only [F.map_id, i1_chainDualPullback_id, LinearMap.id_apply] using hh

end HodgeLean.Foundations.BundleThom
