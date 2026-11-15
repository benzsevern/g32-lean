import HodgeLean.Foundations.QuotientDuality.ProperCycleRealCapUpperComparison

/-! # Original triad cap recurrence through actual signed support suspension
HC no distance; AV milestone no distance. -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicTopology.Singular
namespace HodgeLean.Foundations.QuotientDuality

/-- The original triad caps of a normal cocycle and its literal product pullback commute with the actual signed support suspensions through the specified original excision maps.
Source: Hatcher, Algebraic Topology, sections 2.2 and 3.3; properCycle_real_support_cap_suspension; properCycle_real_lower_support_cap_projection; properCycle_real_upper_support_cap_comparison.
HC no distance; AV milestone no distance. -/
theorem properCycle_original_triad_support_cap_recurrence
    (Y : TopCat.{0}) (S T : Set Y) (hS : IsClosed S) (hT : IsClosed T)
    (p q : ℕ) (hp : Even p)
    (α : RelativeCocycle ℚ (TopPair.ofSubset (X := Y) Sᶜ) p) :
    letI := triadToUnionRelativeChainMap_quasiIso_of_isOpen Y Sᶜ Tᶜ hS.isOpen_compl hT.isOpen_compl
    let EB := asIso (HomologicalComplex.homologyMap
      (triadToUnionRelativeChainMap ℚ Y Sᶜ Tᶜ) (p+q)) ≪≫
      (HomologicalComplex.homologyFunctor (ModuleCat.{0} ℚ) (ComplexShape.down ℕ) (p+q)).mapIso
        ((relativeChainFunctor ℚ).mapIso (properCycle_support_complement_union_iso Y S T))
    let X := TopCat.of (ℝ × Y)
    let ψ := properCycle_real_normal_cocycle Y S p α
    ModuleCat.ofHom (triadCapHomologyMap ℚ X (Prod.snd ⁻¹' Sᶜ)
        {z | z.1 = 0 ∧ z.2 ∈ T}ᶜ p (q+1) ψ.1 ψ.2) ≫
        (properCycle_real_support_suspension_iso Y T hT q).hom =
      HomologicalComplex.homologyMap (triadToUnionRelativeChainMap ℚ X (Prod.snd ⁻¹' Sᶜ)
        {z | z.1 = 0 ∧ z.2 ∈ T}ᶜ) (p+q+1) ≫
        HomologicalComplex.homologyMap ((relativeChainFunctor ℚ).map
          (properCycle_real_cap_upper_union_iso Y S T).hom) (p+q+1) ≫
        (properCycle_real_support_suspension_iso Y (S ∩ T) (hS.inter hT) (p+q)).hom ≫
        EB.inv ≫ ModuleCat.ofHom (triadCapHomologyMap ℚ Y Sᶜ Tᶜ p q α.1 α.2) := by
  letI := triadToUnionRelativeChainMap_quasiIso_of_isOpen Y Sᶜ Tᶜ hS.isOpen_compl hT.isOpen_compl
  let H := HomologicalComplex.homologyFunctor (ModuleCat.{0} ℚ) (ComplexShape.down ℕ)
  let EB := asIso (HomologicalComplex.homologyMap
    (triadToUnionRelativeChainMap ℚ Y Sᶜ Tᶜ) (p+q)) ≪≫
      (H (p+q)).mapIso ((relativeChainFunctor ℚ).mapIso (properCycle_support_complement_union_iso Y S T))
  let X := TopCat.of (ℝ × Y)
  let ψ := properCycle_real_normal_cocycle Y S p α
  let χ := properCycle_real_absolute_normal_cocycle Y S p α
  let hA := properCycle_real_absolute_normal_cocycle_support Y S p α
  let KU := properCycle_real_upper_support_cap Y S T hS hT p q hp χ.1 hA χ.2
  let KL := properCycle_real_lower_support_cap Y S T hS hT p q hp χ.1 hA χ.2
  let UP := ModuleCat.ofHom (triadCapHomologyMap ℚ X (Prod.snd ⁻¹' Sᶜ)
    {z | z.1 = 0 ∧ z.2 ∈ T}ᶜ p (q+1) ψ.1 ψ.2)
  let BP := ModuleCat.ofHom (triadCapHomologyMap ℚ Y Sᶜ Tᶜ p q α.1 α.2)
  let EU := HomologicalComplex.homologyMap (triadToUnionRelativeChainMap ℚ X (Prod.snd ⁻¹' Sᶜ)
    {z | z.1 = 0 ∧ z.2 ∈ T}ᶜ) (p+q+1) ≫
      HomologicalComplex.homologyMap ((relativeChainFunctor ℚ).map
        (properCycle_real_cap_upper_union_iso Y S T).hom) (p+q+1)
  let sT := properCycle_real_support_suspension_iso Y T hT q
  let sS := properCycle_real_support_suspension_iso Y (S ∩ T) (hS.inter hT) (p+q)
  have hu := properCycle_real_upper_support_cap_comparison Y S T hS hT p q hp ψ.1 ψ.2
  change EU ≫ KU = UP at hu
  have hl := properCycle_real_lower_support_cap_projection Y S T hS hT p q hp α
  change EB.hom ≫ KL = BP at hl
  have hs := properCycle_real_support_cap_suspension Y S T hS hT p q hp χ.1 hA χ.2
  change KU ≫ sT.hom = sS.hom ≫ KL at hs
  have hi : KL = EB.inv ≫ BP := by
    apply (cancel_epi EB.hom).mp
    simpa only [Iso.hom_inv_id_assoc] using hl
  change UP ≫ sT.hom = EU ≫ sS.hom ≫ EB.inv ≫ BP
  calc
    _ = (EU ≫ KU) ≫ sT.hom := by rw [hu]
    _ = EU ≫ (sS.hom ≫ KL) := by rw [Category.assoc, hs]
    _ = _ := by simpa only [Category.assoc] using congrArg (fun m => EU ≫ sS.hom ≫ m) hi

end HodgeLean.Foundations.QuotientDuality
