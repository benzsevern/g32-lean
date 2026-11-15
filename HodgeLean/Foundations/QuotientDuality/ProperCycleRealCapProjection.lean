import HodgeLean.Foundations.QuotientDuality.ProperCycleRealCapLowerComparison

/-! # Actual normal cocycle pullback and lower cap projection
HC no distance; AV milestone no distance. -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicTopology.Singular
namespace HodgeLean.Foundations.QuotientDuality

/-- Pull back the original normal relative cocycle by the literal real-product base projection.
Source: Hatcher, Algebraic Topology, section 3.1; properCycle_relative_coboundary_naturality.
HC no distance; AV milestone no distance. -/
def properCycle_real_normal_cocycle (Y : TopCat.{0}) (S : Set Y) (p : ℕ)
    (α : RelativeCocycle ℚ (TopPair.ofSubset (X := Y) Sᶜ) p) :
    RelativeCocycle ℚ (TopPair.ofSubset (X := TopCat.of (ℝ × Y)) (Prod.snd ⁻¹' Sᶜ)) p :=
  ⟨(((relativeChainFunctor ℚ).map (properCycle_product_support_projection ℝ Y S)).f p).hom.dualMap α.1,
    by
      change relativeCoboundary ℚ _ p _ = 0
      rw [properCycle_relative_coboundary_naturality, α.2, map_zero]⟩

/-- The original relative normal cocycle pulled back from the base gives its literal ambient simplicial cocycle.
Source: Hatcher, Algebraic Topology, section 3.1; relativeCochainToAbsolute_coboundary.
HC no distance; AV milestone no distance. -/
def properCycle_real_absolute_normal_cocycle (Y : TopCat.{0}) (S : Set Y) (p : ℕ)
    (α : RelativeCocycle ℚ (TopPair.ofSubset (X := Y) Sᶜ) p) :
    AlgebraicTopology.Simplicial.Cocycle ℚ (TopCat.toSSet.obj (TopCat.of (ℝ × Y))) p := by
  let P := TopPair.ofSubset (X := TopCat.of (ℝ × Y)) (Prod.snd ⁻¹' Sᶜ)
  let ψ := properCycle_real_normal_cocycle Y S p α
  refine ⟨relativeCochainToAbsolute ℚ P p ψ.1, ?_⟩
  change AlgebraicTopology.Simplicial.coboundary ℚ p _ = 0
  exact (relativeCochainToAbsolute_coboundary ℚ P p ψ.1).symm.trans
    ((congrArg (relativeCochainToAbsolute ℚ P (p+1)) ψ.2).trans (map_zero _))

/-- The actual pulled-back ambient normal cocycle vanishes on the literal inverse-image support-complement subcomplex.
Source: properCycle_relative_cochain_subcomplex_zero.
HC no distance; AV milestone no distance. -/
theorem properCycle_real_absolute_normal_cocycle_support
    (Y : TopCat.{0}) (S : Set Y) (p : ℕ)
    (α : RelativeCocycle ℚ (TopPair.ofSubset (X := Y) Sᶜ) p) :
    AlgebraicTopology.Simplicial.cochainMap ℚ
      (subsetSingularSubcomplex (TopCat.of (ℝ × Y)) (Prod.snd ⁻¹' Sᶜ)).ι p
      (properCycle_real_absolute_normal_cocycle Y S p α).1 = 0 :=
  properCycle_relative_cochain_subcomplex_zero (TopCat.of (ℝ × Y)) (Prod.snd ⁻¹' Sᶜ)
    p (properCycle_real_normal_cocycle Y S p α).1

/-- For an actual normal cocycle pulled back by base projection, the lower transported cap is exactly the original base triad cap through the literal union-relative source comparison.
Source: Hatcher, Algebraic Topology, section 3.3; properCycle_real_cap_lower_source_base_triad; properCycle_real_lower_triad_cap_homology; properCycle_triad_cap_cocycle_naturality.
HC no distance; AV milestone no distance. -/
theorem properCycle_real_lower_support_cap_projection
    (Y : TopCat.{0}) (S T : Set Y) (hS : IsClosed S) (hT : IsClosed T)
    (p q : ℕ) (hp : Even p)
    (α : RelativeCocycle ℚ (TopPair.ofSubset (X := Y) Sᶜ) p) :
    let χ := properCycle_real_absolute_normal_cocycle Y S p α
    HomologicalComplex.homologyMap (triadToUnionRelativeChainMap ℚ Y Sᶜ Tᶜ) (p+q) ≫
        HomologicalComplex.homologyMap ((relativeChainFunctor ℚ).map
          (properCycle_support_complement_union_iso Y S T).hom) (p+q) ≫
        properCycle_real_lower_support_cap Y S T hS hT p q hp χ.1
          (properCycle_real_absolute_normal_cocycle_support Y S p α) χ.2 =
      ModuleCat.ofHom (triadCapHomologyMap ℚ Y Sᶜ Tᶜ p q α.1 α.2) := by
  dsimp only
  letI := properCycle_real_cap_refinement_left_isIso Y S T hS hT (p+q)
  let X := TopCat.of (ℝ × Y)
  let f : X ⟶ Y := TopCat.ofHom ⟨Prod.snd, continuous_snd⟩
  let H := HomologicalComplex.homologyFunctor (ModuleCat.{0} ℚ) (ComplexShape.down ℕ)
  let J := (H (p+q)).mapIso (properCycle_real_cap_lower_triad_iso Y S T)
  let F := HomologicalComplex.homologyMap
    (properCycle_triad_relative_chain_map f (Prod.snd ⁻¹' Sᶜ) (Prod.snd ⁻¹' Tᶜ)
      Sᶜ Tᶜ (fun _ h => h) (fun _ h => h)) (p+q)
  letI : IsIso F := (ConcreteCategory.isIso_iff_bijective F).mpr
    (properCycle_product_triad_projection_bijective ℝ Y Sᶜ Tᶜ
      hS.isOpen_compl hT.isOpen_compl (p+q))
  let E := HomologicalComplex.homologyMap (triadToUnionRelativeChainMap ℚ Y Sᶜ Tᶜ) (p+q) ≫
    HomologicalComplex.homologyMap ((relativeChainFunctor ℚ).map
      (properCycle_support_complement_union_iso Y S T).hom) (p+q)
  let Ls := (H (p+q)).mapIso (properCycle_real_support_left_iso Y (S ∩ T))
  let Lt := (H q).mapIso (properCycle_real_support_left_iso Y T)
  let Ps := properCycle_product_support_homology_iso ℝ Y (S ∩ T) (p+q)
  let Pt := properCycle_product_support_homology_iso ℝ Y T q
  let l := HomologicalComplex.homologyMap (properCycle_real_cap_source_refinement Y S T).τ₁ (p+q)
  let ψ := properCycle_real_normal_cocycle Y S p α
  let χ := properCycle_real_absolute_normal_cocycle Y S p α
  let A := subsetSingularSubcomplex X (Prod.snd ⁻¹' Sᶜ)
  let P := subsetSingularSubcomplex X {z | 0 ≤ z.1 ∧ z.2 ∈ T}ᶜ
  let Q := subsetSingularSubcomplex X {z | z.1 ≤ 0 ∧ z.2 ∈ T}ᶜ
  let K := properCycle_subcomplex_cap_homology_map A (P ⊓ Q) p q hp χ.1
    (properCycle_real_absolute_normal_cocycle_support Y S p α) χ.2
  let Bcap := ModuleCat.ofHom (triadCapHomologyMap ℚ Y Sᶜ Tᶜ p q α.1 α.2)
  let Pcap := ModuleCat.ofHom (triadCapHomologyMap ℚ X
    (Prod.snd ⁻¹' Sᶜ) (Prod.snd ⁻¹' Tᶜ) p q ψ.1 ψ.2)
  have hs := congrArg (fun m => HomologicalComplex.homologyMap m (p+q))
    (properCycle_real_cap_lower_source_base_triad Y S T)
  simp only [HomologicalComplex.homologyMap_comp] at hs
  change l ≫ Ls.hom ≫ Ps.hom = J.hom ≫ F ≫ E at hs
  have ho := properCycle_real_lower_triad_cap_homology Y S T p q hp ψ.1 ψ.2
  change J.inv ≫ K ≫ Lt.hom = Pcap at ho
  have hn : Pcap ≫ Pt.hom = F ≫ Bcap := by
    apply ModuleCat.hom_ext
    ext z
    exact properCycle_triad_cap_cocycle_naturality f (Prod.snd ⁻¹' Sᶜ) (Prod.snd ⁻¹' Tᶜ)
      Sᶜ Tᶜ (fun _ h => h) (fun _ h => h) p q α.1 α.2 z
  change E ≫ (Ps.inv ≫ Ls.inv ≫ inv l ≫ K ≫ Lt.hom ≫ Pt.hom) = Bcap
  apply (cancel_epi F).mp
  apply (cancel_epi J.hom).mp
  calc
    _ = (J.hom ≫ F ≫ E) ≫ (Ps.inv ≫ Ls.inv ≫ inv l ≫ K ≫ Lt.hom ≫ Pt.hom) := by
      simp only [Category.assoc]
    _ = (l ≫ Ls.hom ≫ Ps.hom) ≫
        (Ps.inv ≫ Ls.inv ≫ inv l ≫ K ≫ Lt.hom ≫ Pt.hom) := by rw [← hs]
    _ = K ≫ Lt.hom ≫ Pt.hom := by
      simp only [Category.assoc, Iso.hom_inv_id_assoc, IsIso.hom_inv_id_assoc]
    _ = J.hom ≫ (J.inv ≫ K ≫ Lt.hom) ≫ Pt.hom := by
      simp only [Category.assoc, Iso.hom_inv_id_assoc]
    _ = J.hom ≫ Pcap ≫ Pt.hom := by rw [ho]
    _ = J.hom ≫ F ≫ Bcap := by rw [hn]
    _ = _ := by simp only [Category.assoc]

end HodgeLean.Foundations.QuotientDuality
