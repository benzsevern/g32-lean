import HodgeLean.Foundations.Program.SchoenTransferC1a5AttachmentNeighborhoodHelpers
import HodgeLean.Foundations.Program.SchoenTransferC1a5AttachedChainsHelpers

/-! Singular excision for an actual attachment with specified collar deformation.
HC no distance; AV milestone no distance. -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits AlgebraicTopology.Singular
namespace HodgeLean.Foundations.Program

/-- The actual attachment map gives integral relative comparison from explicit boundary collar data.
Source: Hatcher §2.1, Theorem 2.20, neighborhood excision and deformation retraction. -/
lemma c1a5_collar_attachment_singular_excision {A B U C D : TopCat.{0}}
    {t : A ⟶ B} {j : A ⟶ U} {k : U ⟶ C} {r : B ⟶ D} {b : C ⟶ D}
    (sq : IsPushout t (j ≫ k) r b) (hk : Topology.IsOpenEmbedding k)
    (hl : Function.Injective (j ≫ k)) (hc : IsClosed (Set.range (j ≫ k)))
    (q : U ⟶ A) (hq : j ≫ q = 𝟙 A) (H : TopCat.Homotopy (𝟙 U) (q ≫ j))
    (hfixed : ∀ (s : unitInterval) (a : A), H (s, j a) = j a) :
    QuasiIso (c1a5RelativeMap c1a5Chains
      (TopCat.toSSet.map (j ≫ k)) (TopCat.toSSet.map r)
      (TopCat.toSSet.map t) (TopCat.toSSet.map b) (by
        rw [← TopCat.toSSet.map_comp, ← TopCat.toSSet.map_comp]
        exact congrArg TopCat.toSSet.map sq.w.symm)) := by
  let P := pushout t j
  let m := c1a5_attached_collar_map sq
  let N := TopCat.of (Set.range k)
  let N' := TopCat.of (Set.range m)
  let ek : U ≅ N := TopCat.isoOfHomeo hk.toIsEmbedding.toHomeomorph
  have hm := c1a5_attached_collar_isOpenEmbedding sq hk
  let em : P ≅ N' := TopCat.isoOfHomeo hm.toIsEmbedding.toHomeomorph
  let u := j ≫ ek.hom
  let s := pushout.inl t j ≫ em.hom
  let i := topologicalSubsetInclusion C (Set.range k)
  let i' := topologicalSubsetInclusion D (Set.range m)
  have hn : ∀ x ∈ Set.range k, b x ∈ Set.range m := by
    intro x hx
    exact (Set.ext_iff.mp (c1a5_attached_collar_preimage sq hk.injective) x).mpr hx
  let a := c1a5_map_subspace b (Set.range k) (Set.range m) hn
  have wu : (j ≫ k) ≫ 𝟙 C = u ≫ i := by rfl
  have ws : r ≫ 𝟙 D = s ≫ i' := by
    change r ≫ 𝟙 D = pushout.inl t j ≫ m
    exact ((IsPushout.of_hasPushout t j).inl_desc r (k ≫ b) _).symm.trans
      (Category.comp_id _).symm
  have him' : Mono i' := (TopCat.mono_iff_injective _).2 Subtype.val_injective
  have wa : t ≫ s = u ≫ a := by
    apply (cancel_mono i').1
    rw [Category.assoc, ← ws]
    change t ≫ r ≫ 𝟙 D = j ≫ ek.hom ≫ a ≫ i'
    rw [Category.comp_id, sq.w]
    rfl
  have wb : b ≫ 𝟙 D = 𝟙 C ≫ b := by simp only [Category.comp_id, Category.id_comp]
  have w : (j ≫ k) ≫ b = t ≫ r := sq.w.symm
  have w' : i ≫ b = a ≫ i' := by rfl
  have hj : QuasiIso (c1a5Chains.map (TopCat.toSSet.map j)) :=
    (c1a5_retraction_chain_equiv j q hq H).quasiIso_hom
  have hu : QuasiIso (c1a5Chains.map (TopCat.toSSet.map u)) := by
    dsimp only [u]
    rw [TopCat.toSSet.map_comp, c1a5Chains.map_comp]
    have := hj
    infer_instance
  have hs : QuasiIso (c1a5Chains.map (TopCat.toSSet.map s)) := by
    have hh := c1a5_attached_collar_chains_quasiIso t j q hq H hfixed
    dsimp only [s]
    rw [TopCat.toSSet.map_comp, c1a5Chains.map_comp]
    change QuasiIso (c1a5Chains.map (TopCat.toSSet.map (pushout.inl t j))) at hh
    have := hh
    infer_instance
  have hlm : Mono (j ≫ k) := (TopCat.mono_iff_injective _).2 hl
  have hrm : Mono r := by
    let FF := forget TopCat.{0}
    have hl' : Mono (FF.map (j ≫ k)) := (mono_iff_injective _).2 hl
    have hr' : Mono (FF.map r) :=
      (MorphismProperty.monomorphisms (Type)).of_isPushout (sq.map FF) hl'
    exact (TopCat.mono_iff_injective _).2 ((mono_iff_injective _).1 hr')
  have him : Mono i := (TopCat.mono_iff_injective _).2 Subtype.val_injective
  let F := TopCat.toSSet
  have wF : F.map (j ≫ k) ≫ F.map b = F.map t ≫ F.map r := by
    rw [← F.map_comp, ← F.map_comp, w]
  have wF' : F.map i ≫ F.map b = F.map a ≫ F.map i' := by
    rw [← F.map_comp, ← F.map_comp, w']
  have wuF : F.map (j ≫ k) ≫ F.map (𝟙 C) = F.map u ≫ F.map i := by
    rw [← F.map_comp, ← F.map_comp, wu]
  have wsF : F.map r ≫ F.map (𝟙 D) = F.map s ≫ F.map i' := by
    rw [← F.map_comp, ← F.map_comp, ws]
  have waF : F.map t ≫ F.map s = F.map u ≫ F.map a := by
    rw [← F.map_comp, ← F.map_comp, wa]
  have wbF : F.map b ≫ F.map (𝟙 D) = F.map (𝟙 C) ≫ F.map b := by
    rw [← F.map_comp, ← F.map_comp, wb]
  have huRel : QuasiIso (c1a5RelativeMap c1a5Chains (F.map (j ≫ k)) (F.map i)
      (F.map u) (F.map (𝟙 C)) wuF) := by
    have := c1a5_chains_map_mono (F.map (j ≫ k))
    have := c1a5_chains_map_mono (F.map i)
    exact c1a5_cokernel_comparison _ _ (c1a5Chains.map (F.map u))
      (c1a5Chains.map (F.map (𝟙 C)))
      (by rw [← c1a5Chains.map_comp, ← c1a5Chains.map_comp, wuF]) hu inferInstance
  have hsRel : QuasiIso (c1a5RelativeMap c1a5Chains (F.map r) (F.map i')
      (F.map s) (F.map (𝟙 D)) wsF) := by
    have := c1a5_chains_map_mono (F.map r)
    have := c1a5_chains_map_mono (F.map i')
    exact c1a5_cokernel_comparison _ _ (c1a5Chains.map (F.map s))
      (c1a5Chains.map (F.map (𝟙 D)))
      (by rw [← c1a5Chains.map_comp, ← c1a5Chains.map_comp, wsF]) hs inferInstance
  have hnRel : QuasiIso (c1a5RelativeMap c1a5Chains (F.map i) (F.map i')
      (F.map a) (F.map b) wF') := c1a5_attachment_neighborhood_relative_comparison sq hk hl hc
  have hh := c1a5_relative_cube_naturality c1a5Chains
    (F.map (j ≫ k)) (F.map r) (F.map t) (F.map b)
    (F.map i) (F.map i') (F.map a) (F.map b)
    (F.map u) (F.map (𝟙 C)) (F.map s) (F.map (𝟙 D))
    wF wF' wuF wsF waF wbF
  have hcomp : QuasiIso
      (c1a5RelativeMap c1a5Chains (F.map (j ≫ k)) (F.map r) (F.map t) (F.map b) wF ≫
        c1a5RelativeMap c1a5Chains (F.map r) (F.map i') (F.map s) (F.map (𝟙 D)) wsF) := by
    rw [hh]
    have := huRel
    have := hnRel
    infer_instance
  have := hsRel
  have := hcomp
  exact quasiIso_of_comp_right _
    (c1a5RelativeMap c1a5Chains (F.map r) (F.map i') (F.map s) (F.map (𝟙 D)) wsF)

end HodgeLean.Foundations.Program
