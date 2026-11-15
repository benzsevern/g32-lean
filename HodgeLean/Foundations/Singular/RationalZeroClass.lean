import HodgeLean.Foundations.Singular.RationalZeroHomology
import HodgeConjecture.Lemmas.Algebra.Homology.LinearDualNaturality

/-! Cycle normalization for homology of zero-differential rational short complexes. -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
open CategoryTheory CategoryTheory.Limits
namespace HodgeLean.Foundations.Singular

set_option backward.isDefEq.respectTransparency false in
/-- The zero-differential homology identification sends the class of a cycle to its actual vector.
Source: Hatcher, Algebraic Topology, §2.1, homology of a zero differential. -/
theorem rationalZeroShortHomology_class (S : ShortComplex (ModuleCat ℚ))
    (hf : S.f = 0) (hg : S.g = 0) (z : LinearMap.ker S.g.hom) :
    ((ShortComplex.HomologyData.ofZeros S hf hg).left.homologyIso.hom).hom
      (S.moduleCatHomologyClass z) = (z : S.X₂) := by
  let h := (ShortComplex.HomologyData.ofZeros S hf hg).left
  have hc : ModuleCat.ofHom S.moduleCatHomologyClass =
      S.moduleCatCyclesIso.inv ≫ S.homologyπ :=
    (S.moduleCatCyclesIso_inv_π).symm
  have hi : h.cyclesIso.hom = S.iCycles := by
    have hh := h.cyclesIso_hom_comp_i
    change h.cyclesIso.hom ≫ 𝟙 S.X₂ = S.iCycles at hh
    exact (Category.comp_id (h.cyclesIso.hom : S.cycles ⟶ S.X₂)).symm.trans hh
  have he : ModuleCat.ofHom S.moduleCatHomologyClass ≫ h.homologyIso.hom =
      ModuleCat.ofHom (LinearMap.ker S.g.hom).subtype := by
    calc
      _ = (S.moduleCatCyclesIso.inv ≫ S.homologyπ) ≫ h.homologyIso.hom :=
        congrArg (fun k => k ≫ h.homologyIso.hom) hc
      _ = S.moduleCatCyclesIso.inv ≫ (S.homologyπ ≫ h.homologyIso.hom) := Category.assoc _ _ _
      _ = S.moduleCatCyclesIso.inv ≫ (h.cyclesIso.hom ≫ h.π) :=
        congrArg (fun k => S.moduleCatCyclesIso.inv ≫ k) h.homologyπ_comp_homologyIso_hom
      _ = S.moduleCatCyclesIso.inv ≫ S.iCycles := by
        change S.moduleCatCyclesIso.inv ≫ (h.cyclesIso.hom ≫ 𝟙 _) = _
        erw [Category.comp_id, hi]
      _ = _ := S.moduleCatCyclesIso_inv_iCycles
  exact congrArg (fun k => ModuleCat.Hom.hom k z) he

#print axioms rationalZeroShortHomology_class
end HodgeLean.Foundations.Singular
