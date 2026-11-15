import HodgeLean.Foundations.BundleThom.RelativeFinsetCoclassDetectionHelpers
import HodgeLean.Foundations.BundleThom.BinaryRelativeCoclassGluingHelpers
import HodgeLean.Foundations.BundleThom.ChainDualQuasiIsoHelpers

/-! # Finite gluing of actual relative degree-two coclasses

Triple degree-one and quadruple degree-zero calculations supply the overlap detection needed by the induction.
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Limits AlgebraicTopology
namespace HodgeLean.Foundations.BundleThom

/-- Compatible relative degree-two coclasses on a nonempty finite family glue when triple degree-one and quadruple degree-zero intersection homology vanish.
Source: Hatcher, Algebraic Topology, §2.2 and §3.1, finite relative Mayer–Vietoris gluing. -/
theorem i1_relativeSubcomplexFinsetCoclass_gluing {ι : Type}
    (X : SSet) (Z : X.Subcomplex) (U : ι → X.Subcomplex)
    (w : ∀ i, ((i1_relativeSubcomplexChainFunctor X Z).obj (U i)).linearDualCochainComplex.homology 2)
    (s : Finset ι) :
    s.Nonempty →
    (∀ i ∈ s, ∀ j ∈ s, ∀ t ∈ s,
      IsZero (((i1_relativeSubcomplexChainFunctor X Z).obj (U i ⊓ U j ⊓ U t)).homology 1)) →
    (∀ i ∈ s, ∀ j ∈ s, ∀ t ∈ s, ∀ r ∈ s,
      IsZero (((i1_relativeSubcomplexChainFunctor X Z).obj (U i ⊓ U j ⊓ U t ⊓ U r)).homology 0)) →
    (∀ i ∈ s, ∀ j ∈ s, i1_chainDualPullback 2
        ((i1_relativeSubcomplexChainFunctor X Z).map (homOfLE (inf_le_left : U i ⊓ U j ≤ U i))) (w i) =
      i1_chainDualPullback 2
        ((i1_relativeSubcomplexChainFunctor X Z).map (homOfLE (inf_le_right : U i ⊓ U j ≤ U j))) (w j)) →
    ∃ z : ((i1_relativeSubcomplexChainFunctor X Z).obj (s.sup U)).linearDualCochainComplex.homology 2,
      ∀ (i : ι) (_ : i ∈ s) (hUi : U i ≤ s.sup U),
        i1_chainDualPullback 2 ((i1_relativeSubcomplexChainFunctor X Z).map (homOfLE hUi)) z = w i := by
  classical
  let F := i1_relativeSubcomplexChainFunctor X Z
  have hm {A B : X.Subcomplex} (f g : A ⟶ B) :
      i1_chainDualPullback 2 (F.map f) = i1_chainDualPullback 2 (F.map g) :=
    congrArg (fun h => i1_chainDualPullback 2 (F.map h)) (Subsingleton.elim f g)
  induction s using Finset.induction_on with
  | empty =>
    intro hs
    exact False.elim (Finset.not_nonempty_empty hs)
  | @insert a s ha ih =>
    intro hs ht hq hc
    by_cases hsn : s.Nonempty
    · obtain ⟨z, hz⟩ := ih hsn
        (fun i hi j hj t htm => ht i (Finset.mem_insert_of_mem hi)
          j (Finset.mem_insert_of_mem hj) t (Finset.mem_insert_of_mem htm))
        (fun i hi j hj t htm r hr => hq i (Finset.mem_insert_of_mem hi)
          j (Finset.mem_insert_of_mem hj) t (Finset.mem_insert_of_mem htm) r (Finset.mem_insert_of_mem hr))
        (fun i hi j hj => hc i (Finset.mem_insert_of_mem hi) j (Finset.mem_insert_of_mem hj))
      have heq := i1_subcomplex_inf_finsetSup X (U a) U s
      let q : F.obj (s.sup (fun i => U a ⊓ U i)) ⟶ F.obj (U a ⊓ s.sup U) :=
        F.map (eqToHom heq.symm)
      haveI : QuasiIso q := by
        dsimp [q]
        infer_instance
      have hcompat : i1_chainDualPullback 2
            (F.map (homOfLE (inf_le_left : U a ⊓ s.sup U ≤ U a))) (w a) =
          i1_chainDualPullback 2
            (F.map (homOfLE (inf_le_right : U a ⊓ s.sup U ≤ s.sup U))) z := by
        apply (i1_chainDualPullback_bijective 2 q).1
        apply i1_relativeSubcomplexFinsetCoclass_ext X Z (fun i => U a ⊓ U i) s hsn
        · intro i hi j hj
          simpa only [inf_assoc, inf_left_comm, inf_idem, inf_left_idem] using
            ht a (Finset.mem_insert_self _ _) i (Finset.mem_insert_of_mem hi)
              j (Finset.mem_insert_of_mem hj)
        · intro i hi j hj t htm
          simpa only [inf_assoc, inf_left_comm, inf_idem, inf_left_idem] using
            hq a (Finset.mem_insert_self _ _) i (Finset.mem_insert_of_mem hi)
              j (Finset.mem_insert_of_mem hj) t (Finset.mem_insert_of_mem htm)
        · intro i hi hUi
          change i1_chainDualPullback 2 (F.map (homOfLE hUi))
              (i1_chainDualPullback 2 q (i1_chainDualPullback 2
                (F.map (homOfLE (inf_le_left : U a ⊓ s.sup U ≤ U a))) (w a))) =
            i1_chainDualPullback 2 (F.map (homOfLE hUi))
              (i1_chainDualPullback 2 q (i1_chainDualPullback 2
                (F.map (homOfLE (inf_le_right : U a ⊓ s.sup U ≤ s.sup U))) z))
          dsimp only [q]
          simp only [← LinearMap.comp_apply, ← i1_chainDualPullback_comp, ← F.map_comp]
          rw [hm _ (homOfLE (inf_le_left : U a ⊓ U i ≤ U a)),
            hm _ (homOfLE ((inf_le_right : U a ⊓ U i ≤ U i).trans (Finset.le_sup hi)))]
          have hr := congrArg (i1_chainDualPullback 2
            (F.map (homOfLE (inf_le_right : U a ⊓ U i ≤ U i)))) (hz i hi (Finset.le_sup hi))
          change i1_chainDualPullback 2 (F.map (homOfLE (inf_le_right : U a ⊓ U i ≤ U i)))
              (i1_chainDualPullback 2 (F.map (homOfLE (Finset.le_sup hi))) z) =
            i1_chainDualPullback 2 (F.map (homOfLE (inf_le_right : U a ⊓ U i ≤ U i))) (w i) at hr
          simp only [← LinearMap.comp_apply, ← i1_chainDualPullback_comp, ← F.map_comp] at hr
          exact (hc a (Finset.mem_insert_self _ _) i (Finset.mem_insert_of_mem hi)).trans hr.symm
      obtain ⟨v, hva, hvz⟩ := i1_binaryRelativeSubcomplexCoclass_gluing X Z (U a) (s.sup U) 2
        (w a) z hcompat
      rw [Finset.sup_insert]
      refine ⟨v, ?_⟩
      intro i hi hUi
      rcases Finset.mem_insert.mp hi with hi | hi
      · subst i
        exact hva
      · have hr := congrArg (i1_chainDualPullback 2
          (F.map (homOfLE (Finset.le_sup hi)))) hvz
        change i1_chainDualPullback 2 (F.map (homOfLE (Finset.le_sup hi)))
            (i1_chainDualPullback 2 (F.map (homOfLE (le_sup_right : s.sup U ≤ U a ⊔ s.sup U))) v) =
          i1_chainDualPullback 2 (F.map (homOfLE (Finset.le_sup hi))) z at hr
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
