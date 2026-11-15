import HodgeLean.Foundations.Program.SchoenTowerI1aDescentAssembly

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Topology
namespace HodgeLean.Foundations.Program

lemma s2v_i1ahi_glue_open_factors
    {Q T : Scheme} {ι : Type} (W : ι → Q.Opens) (hW : (⨆ i, W i) = ⊤)
    (v : ∀ i, (W i).toScheme ⟶ T)
    (hv : ∀ i j, Q.homOfLE (inf_le_left : W i ⊓ W j ≤ W i) ≫ v i =
      Q.homOfLE (inf_le_right : W i ⊓ W j ≤ W j) ≫ v j) :
    ∃! g : Q ⟶ T, ∀ i, (W i).ι ≫ g = v i := by
  let C := Q.openCoverOfIsOpenCover W hW
  have hc : ∀ i j, pullback.fst (C.f i) (C.f j) ≫ v i =
      pullback.snd (C.f i) (C.f j) ≫ v j := by
    intro i j
    change pullback.fst (W i).ι (W j).ι ≫ v i = pullback.snd (W i).ι (W j).ι ≫ v j
    apply (cancel_epi (isPullback_opens_inf (W i) (W j)).isoPullback.hom).mp
    simpa only [← Category.assoc, IsPullback.isoPullback_hom_fst,
      IsPullback.isoPullback_hom_snd] using hv i j
  refine ⟨C.glueMorphisms v hc, fun i => C.ι_glueMorphisms v hc i, ?_⟩
  intro g hg
  exact C.hom_ext _ _ (fun i => (hg i).trans (C.ι_glueMorphisms v hc i).symm)

lemma s2v_i1ahi_assemble_descended_factors
    {S Q T : Scheme} (q : S ⟶ Q) [Surjective q] [QuasiCompact q]
    [IsSchemeTheoreticallyDominant q] (f : S ⟶ T)
    {ι : Type} (W : ι → Q.Opens) (hW : (⨆ i, W i) = ⊤)
    (v : ∀ i, (W i).toScheme ⟶ T)
    (hv : ∀ i, (q ∣_ W i) ≫ v i = (q ⁻¹ᵁ W i).ι ≫ f) :
    ∃! g : Q ⟶ T, q ≫ g = f := by
  obtain ⟨g, hg, _⟩ := s2v_i1ahi_glue_open_factors W hW v
    (fun i j => s2v_i1ahi_local_factors_compatible q f (W i) (W j) (v i) (v j) (hv i) (hv j))
  have hgf : q ≫ g = f := by
    apply (S.openCoverOfIsOpenCover (fun i => q ⁻¹ᵁ W i)
      (Scheme.Hom.iSup_preimage_eq_top q hW)).hom_ext
    intro i
    change (q ⁻¹ᵁ W i).ι ≫ q ≫ g = (q ⁻¹ᵁ W i).ι ≫ f
    rw [← morphismRestrict_ι_assoc, hg, hv]
  letI := s2v_i1ahi_scheme_epi_of_schematic_dominance q
  exact ⟨g, hgf, fun u hu => (cancel_epi q).mp (hu.trans hgf.symm)⟩

end HodgeLean.Foundations.Program
