import HodgeLean.Foundations.Program.PrymVariationCentreBranchOrbits
import HodgeLean.Foundations.Program.PrymVariationCentreCharacters

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
  {n : ℕ} (q : Fin n → OnePoint ℂ) (hq : Function.Injective q) (r : Fin n → b4b_Group)
  (hbranch : b4_branchSet ℂ ℂ p = Set.range q)
  (hrot : ∀ i, ∃ x : C, p x = q i ∧ b4_IsRotGen ℂ x (r i))
  {W : Type} [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
  (ρ : Representation ℂ b4b_Group W) [ρ.IsIrreducible]
  (hρ : ∃ (g : b4b_Group) (v : W), ρ g v ≠ v)
include hG hp hs hgal hq hbranch hrot hρ

theorem b63d_finite_holoCW :
    (Module.finrank ℂ (b4_HomG ρ (fun g ↦ b4_formAct ℂ (C := C) g)
      (b3_HolForm ℂ C)) : ℝ) = ∑ i, b4_age (ρ (r i)) - Module.finrank ℂ W := by
  rw [b4_chevalleyWeil_holo (by simp) hG
    (b63d_invariantForms_eq_bot C hG p hp hs hgal)
    (b63d_rotationGenerator C hG) (b63d_rotationGenerator_isRotGen C hG) ρ hρ]
  rw [b63d_branch_weighted_sum C hG p hp hgal q hq r hbranch hrot
    (fun g ↦ b4_age (ρ g)) (HurwitzPrymRex_age_one ρ).1
    (b63d_rep_age_conjugate ρ)]

theorem b63d_finite_topCW :
    (Module.finrank ℂ (b4_HomG ρ (fun g ↦ b4_cplxAct ℂ (C := C) g) ⊤) : ℝ) =
      (∑ i, (Module.finrank ℂ (LinearMap.range (ρ (r i) - LinearMap.id)) : ℝ)) -
        2 * Module.finrank ℂ W := by
  rw [b4_chevalleyWeil_top (by simp) hG
    (b63d_invariantForms_eq_bot C hG p hp hs hgal)
    (b63d_rotationGenerator C hG) (b63d_rotationGenerator_isRotGen C hG) ρ hρ]
  apply congrArg (fun z : ℝ ↦ z - 2 * Module.finrank ℂ W)
  refine b63d_branch_weighted_sum C hG p hp hgal q hq r hbranch hrot
    (fun g ↦ (Module.finrank ℂ (LinearMap.range (ρ g - LinearMap.id)) : ℝ)) ?_ ?_
  · change (Module.finrank ℂ (LinearMap.range (ρ 1 - LinearMap.id)) : ℝ) = 0
    have he : ρ 1 - LinearMap.id = 0 := by rw [map_one]; exact sub_self _
    have hz := congrArg (fun f : W →ₗ[ℂ] W ↦ (Module.finrank ℂ (LinearMap.range f) : ℝ)) he
    exact hz.trans (by simp)
  · intro g h
    rw [b63d_rep_rank_conjugate]

end Cover
end HodgeLean.Foundations.Program
