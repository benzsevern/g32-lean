import HodgeLean.Foundations.Program.PrymVariationCentreFiniteFormula
import HodgeLean.Foundations.Program.PrymVariationCentreRootWeights

noncomputable section
open HodgeLean.Papers
open scoped Manifold ContDiff
namespace HodgeLean.Foundations.Program
attribute [local instance] b4cov_sphChartedSpace b4cov_sph_isManifold

section Cover
variable (C : Type) [TopologicalSpace C] [ChartedSpace ℂ C]
  [IsManifold 𝓘(ℂ, ℂ) ω C] [T2Space C] [CompactSpace C] [ConnectedSpace C]
  [MulAction b4b_Group C] [FaithfulSMul b4b_Group C]
  (hG : ∀ g : b4b_Group, ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω (fun x : C ↦ g • x))
  (p : C → OnePoint ℂ) (hp : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω p)
  (hs : Function.Surjective p) (hgal : b4_IsGaloisCover b4b_Group p)
  (q : Fin 13 → OnePoint ℂ) (hq : Function.Injective q)
  (hbranch : b4_branchSet ℂ ℂ p = Set.range q)
  (hrot : ∀ i, ∃ x : C, p x = q i ∧ b4_IsRotGen ℂ x (b4b_root i))
include hG hp hs hgal hq hbranch hrot

theorem b63d_natural_top_multiplicity :
    Module.finrank ℂ (b4_HomG b63d_naturalRep
      (fun g ↦ b4_cplxAct ℂ (C := C) g) ⊤) = 6 := by
  have h := b63d_finite_topCW C hG p hp hs hgal q hq b4b_root hbranch hrot
    b63d_naturalRep b63d_naturalRep_nontrivial
  simp only [b63d_naturalRep_rank, b63d_naturalRep_finrank] at h
  rw [b63d_root_rank_sum] at h
  norm_num at h
  exact_mod_cast h

theorem b63d_natural_holo_multiplicity :
    Module.finrank ℂ (b4_HomG b63d_naturalRep
      (fun g ↦ b4_formAct ℂ (C := C) g) (b3_HolForm ℂ C)) = 3 := by
  have h := b63d_finite_holoCW C hG p hp hs hgal q hq b4b_root hbranch hrot
    b63d_naturalRep b63d_naturalRep_nontrivial
  rw [b63d_root_natural_age_sum, b63d_naturalRep_finrank] at h
  norm_num at h
  exact_mod_cast h

theorem b63d_conjugate_holo_multiplicity :
    Module.finrank ℂ (b4_HomG (HurwitzPrymRex_barRep b63d_naturalRep)
      (fun g ↦ b4_formAct ℂ (C := C) g) (b3_HolForm ℂ C)) = 3 := by
  have h := b63d_finite_holoCW C hG p hp hs hgal q hq b4b_root hbranch hrot
    (HurwitzPrymRex_barRep b63d_naturalRep) b63d_conjugateRep_nontrivial
  rw [b63d_root_conjugate_age_sum, b63d_conjugateRep_finrank] at h
  norm_num at h
  exact_mod_cast h

theorem b63d_period_multiplicities :
    Module.finrank ℂ (b4_HomG b63d_naturalRep
      (fun g ↦ b4_cplxAct ℂ (C := C) g) (b3_periodF ℂ C)) = 3 ∧
    Module.finrank ℂ (b4_HomG (HurwitzPrymRex_barRep b63d_naturalRep)
      (fun g ↦ b4_cplxAct ℂ (C := C) g) (b3_periodF ℂ C)) = 3 := by
  rw [b4_hodge_eq_holo (by simp) hG, b4_hodge_eq_holo (by simp) hG]
  exact ⟨b63d_natural_holo_multiplicity C hG p hp hs hgal q hq hbranch hrot,
    b63d_conjugate_holo_multiplicity C hG p hp hs hgal q hq hbranch hrot⟩

end Cover
end HodgeLean.Foundations.Program
