import HodgeLean.Foundations.BundleThom.ProductBinaryCoclassDetectionHelpers

/-! # Degree-two product coclass detection by finite open base covers

Every intersection in the induction is an actual product pair over its inherited base topology.
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Limits TopologicalSpace AlgebraicTopology.Singular
namespace HodgeLean.Foundations.BundleThom

/-- A nonempty finite open base cover detects rational degree-two coclasses of every positive-rank complex product normal pair.
Source: Hatcher, Algebraic Topology, §2.2 and §3.1, finite-cover relative Mayer–Vietoris. -/
theorem i1_productFiniteCoverCoclass_ext {ι : Type} (k : ℕ) (hk : 0 < k) (s : Finset ι) :
    ∀ {B : Type} [TopologicalSpace B] (U : ι → Set B)
      (hU : ∀ i ∈ s, IsOpen (U i)) (hs : s.Nonempty)
      (hcover : ∀ b : B, ∃ i ∈ s, b ∈ U i)
      (u v : RelativeCohomology ℚ (i1_productNormalPair B k) 2),
      (∀ i ∈ s, relativeCohomologyMap ℚ 2
        (i1_productBaseMap k (Subtype.val : U i → B) continuous_subtype_val) u =
      relativeCohomologyMap ℚ 2
        (i1_productBaseMap k (Subtype.val : U i → B) continuous_subtype_val) v) → u = v := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    intro B inst U hU hs
    exact False.elim (Finset.not_nonempty_empty hs)
  | @insert a s ha ih =>
    intro B inst U hU hs hcover u v hr
    by_cases hsn : s.Nonempty
    · let V : Set B := ⋃ i ∈ s, U i
      have hV : IsOpen V := isOpen_iUnion fun i => isOpen_iUnion fun hi =>
        hU i (Finset.mem_insert_of_mem hi)
      have hc : U a ∪ V = Set.univ := by
        apply Set.eq_univ_of_forall
        intro b
        obtain ⟨i, hi, hb⟩ := hcover b
        rcases Finset.mem_insert.mp hi with hi | hi
        · subst i
          exact Or.inl hb
        · exact Or.inr (Set.mem_iUnion₂.mpr ⟨i, hi, hb⟩)
      apply i1_productBinaryCoclass_ext k (U a) V
        (hU a (Finset.mem_insert_self _ _)) hV hc 1
        (i1_productNormalRelativeHomologyOne_isZero k hk) u v
        (hr a (Finset.mem_insert_self _ _))
      let U' : ι → Set V := fun i => Subtype.val ⁻¹' U i
      apply ih U' (fun i hi => (hU i (Finset.mem_insert_of_mem hi)).preimage
        continuous_subtype_val) hsn
        (fun b => by
          obtain ⟨i, hi, hb⟩ := Set.mem_iUnion₂.mp b.2
          exact ⟨i, hi, hb⟩)
      intro i hi
      let g : U' i → U i := fun x => ⟨x.1.1, x.2⟩
      have hg : Continuous g :=
        (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
      have h := congrArg (relativeCohomologyMap ℚ 2 (i1_productBaseMap k g hg))
        (hr i (Finset.mem_insert_of_mem hi))
      simpa only [← LinearMap.comp_apply, ← relativeCohomologyMap_comp,
        i1_productBaseMap_comp, Function.comp_def] using h
    · have haU : ∀ b : B, b ∈ U a := by
        intro b
        obtain ⟨i, hi, hb⟩ := hcover b
        rcases Finset.mem_insert.mp hi with hi | hi
        · subst i
          exact hb
        · exact False.elim (hsn ⟨i, hi⟩)
      let f : B → U a := fun b => ⟨b, haU b⟩
      have hf : Continuous f := continuous_id.subtype_mk _
      have h := congrArg (relativeCohomologyMap ℚ 2 (i1_productBaseMap k f hf))
        (hr a (Finset.mem_insert_self _ _))
      simpa only [← LinearMap.comp_apply, ← relativeCohomologyMap_comp,
        i1_productBaseMap_comp, show (Subtype.val : U a → B) ∘ f = id from rfl,
        i1_productBaseMap_id, relativeCohomologyMap_id, LinearMap.id_apply] using h

end HodgeLean.Foundations.BundleThom
