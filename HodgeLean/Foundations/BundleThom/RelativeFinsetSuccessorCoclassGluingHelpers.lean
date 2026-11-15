import HodgeLean.Foundations.BundleThom.RelativeFinsetSuccessorCoclassDetectionHelpers
import HodgeLean.Foundations.BundleThom.BinaryRelativeCoclassGluingHelpers
import HodgeLean.Foundations.BundleThom.ChainDualQuasiIsoHelpers

/-! # Finite gluing of actual relative successor-degree coclasses

Actual finite intersection vanishing supplies the overlap detection needed by the induction.
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Limits AlgebraicTopology
namespace HodgeLean.Foundations.BundleThom

/-- Compatible relative successor-degree coclasses on a nonempty finite family glue when actual finite intersections vanish in the preceding and lower degrees.
Source: Hatcher, Algebraic Topology, §2.2 and §3.1, finite relative Mayer–Vietoris gluing. -/
theorem i1_relativeSubcomplexFinsetSuccessorCoclass_gluing {ι : Type}
    (X : SSet) (Z : X.Subcomplex) (n : ℕ) (U : ι → X.Subcomplex)
    (w : ∀ i, ((i1_relativeSubcomplexChainFunctor X Z).obj (U i)).linearDualCochainComplex.homology (n + 1))
    (s : Finset ι) :
    s.Nonempty →
    (∀ t : Finset ι, t.Nonempty → ∀ m, m ≤ n →
      IsZero (((i1_relativeSubcomplexChainFunctor X Z).obj (t.inf U)).homology m)) →
    (∀ i ∈ s, ∀ j ∈ s, i1_chainDualPullback (n + 1)
        ((i1_relativeSubcomplexChainFunctor X Z).map (homOfLE (inf_le_left : U i ⊓ U j ≤ U i))) (w i) =
      i1_chainDualPullback (n + 1)
        ((i1_relativeSubcomplexChainFunctor X Z).map (homOfLE (inf_le_right : U i ⊓ U j ≤ U j))) (w j)) →
    ∃ z : ((i1_relativeSubcomplexChainFunctor X Z).obj (s.sup U)).linearDualCochainComplex.homology (n + 1),
      ∀ (i : ι) (_ : i ∈ s) (hUi : U i ≤ s.sup U),
        i1_chainDualPullback (n + 1) ((i1_relativeSubcomplexChainFunctor X Z).map (homOfLE hUi)) z = w i := by
  classical
  let F := i1_relativeSubcomplexChainFunctor X Z
  have hm {A B : X.Subcomplex} (f g : A ⟶ B) :
      i1_chainDualPullback (n + 1) (F.map f) = i1_chainDualPullback (n + 1) (F.map g) :=
    congrArg (fun h => i1_chainDualPullback (n + 1) (F.map h)) (Subsingleton.elim f g)
  induction s using Finset.induction_on with
  | empty =>
    intro hs
    exact False.elim (Finset.not_nonempty_empty hs)
  | @insert a s ha ih =>
    intro hs hh hc
    by_cases hsn : s.Nonempty
    · obtain ⟨z, hz⟩ := ih hsn hh
        (fun i hi j hj => hc i (Finset.mem_insert_of_mem hi) j (Finset.mem_insert_of_mem hj))
      have heq := i1_subcomplex_inf_finsetSup X (U a) U s
      let q : F.obj (s.sup (fun i => U a ⊓ U i)) ⟶ F.obj (U a ⊓ s.sup U) :=
        F.map (eqToHom heq.symm)
      haveI : QuasiIso q := by
        dsimp [q]
        infer_instance
      have hcompat : i1_chainDualPullback (n + 1)
            (F.map (homOfLE (inf_le_left : U a ⊓ s.sup U ≤ U a))) (w a) =
          i1_chainDualPullback (n + 1)
            (F.map (homOfLE (inf_le_right : U a ⊓ s.sup U ≤ s.sup U))) z := by
        apply (i1_chainDualPullback_bijective (n + 1) q).1
        apply i1_relativeSubcomplexFinsetSuccessorCoclass_ext X Z n
          (fun i => U a ⊓ U i) s hsn
        · intro t ht m hm
          rw [i1_subcomplex_finsetInf_restrict X U a t ht]
          exact hh (insert a t) (Finset.insert_nonempty a t) m hm
        · intro i hi hUi
          change i1_chainDualPullback (n + 1) (F.map (homOfLE hUi))
              (i1_chainDualPullback (n + 1) q (i1_chainDualPullback (n + 1)
                (F.map (homOfLE (inf_le_left : U a ⊓ s.sup U ≤ U a))) (w a))) =
            i1_chainDualPullback (n + 1) (F.map (homOfLE hUi))
              (i1_chainDualPullback (n + 1) q (i1_chainDualPullback (n + 1)
                (F.map (homOfLE (inf_le_right : U a ⊓ s.sup U ≤ s.sup U))) z))
          dsimp only [q]
          simp only [← LinearMap.comp_apply, ← i1_chainDualPullback_comp, ← F.map_comp]
          rw [hm _ (homOfLE (inf_le_left : U a ⊓ U i ≤ U a)),
            hm _ (homOfLE ((inf_le_right : U a ⊓ U i ≤ U i).trans (Finset.le_sup hi)))]
          have hr := congrArg (i1_chainDualPullback (n + 1)
            (F.map (homOfLE (inf_le_right : U a ⊓ U i ≤ U i)))) (hz i hi (Finset.le_sup hi))
          change i1_chainDualPullback (n + 1) (F.map (homOfLE (inf_le_right : U a ⊓ U i ≤ U i)))
              (i1_chainDualPullback (n + 1) (F.map (homOfLE (Finset.le_sup hi))) z) =
            i1_chainDualPullback (n + 1) (F.map (homOfLE (inf_le_right : U a ⊓ U i ≤ U i))) (w i) at hr
          simp only [← LinearMap.comp_apply, ← i1_chainDualPullback_comp, ← F.map_comp] at hr
          exact (hc a (Finset.mem_insert_self _ _) i (Finset.mem_insert_of_mem hi)).trans hr.symm
      obtain ⟨v, hva, hvz⟩ := i1_binaryRelativeSubcomplexCoclass_gluing X Z (U a) (s.sup U) (n + 1)
        (w a) z hcompat
      rw [Finset.sup_insert]
      refine ⟨v, ?_⟩
      intro i hi hUi
      rcases Finset.mem_insert.mp hi with hi | hi
      · subst i
        exact hva
      · have hr := congrArg (i1_chainDualPullback (n + 1)
          (F.map (homOfLE (Finset.le_sup hi)))) hvz
        change i1_chainDualPullback (n + 1) (F.map (homOfLE (Finset.le_sup hi)))
            (i1_chainDualPullback (n + 1) (F.map (homOfLE (le_sup_right : s.sup U ≤ U a ⊔ s.sup U))) v) =
          i1_chainDualPullback (n + 1) (F.map (homOfLE (Finset.le_sup hi))) z at hr
        simp only [← LinearMap.comp_apply, ← i1_chainDualPullback_comp, ← F.map_comp] at hr
        exact hr.trans (hz i hi (Finset.le_sup hi))
    · have hse : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hsn
      subst s
      rw [Finset.sup_insert, Finset.sup_empty, sup_bot_eq]
      refine ⟨w a, ?_⟩
      intro i hi hUi
      have hi' : i = a := by simpa only [Finset.mem_insert, Finset.notMem_empty, or_false] using hi
      subst i
      rw [hm _ (𝟙 (U a)), F.map_id, i1_chainDualPullback_id, LinearMap.id_apply]

end HodgeLean.Foundations.BundleThom
