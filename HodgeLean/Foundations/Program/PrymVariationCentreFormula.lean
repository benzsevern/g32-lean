import HodgeLean.Foundations.Program.PrymVariationCentreIrreducible

noncomputable section
open HodgeLean.Papers
open scoped Manifold ContDiff
namespace HodgeLean.Foundations.Program
attribute [local instance] b4cov_sphChartedSpace b4cov_sph_isManifold

theorem b63d_naturalRep_age (g : b4b_Group) :
    b4_age (b63d_naturalRep g) = g32h_age (b4b_toMatrix g) := by
  change (Multiset.map g32h_angle (Matrix.toLin' (b4b_toMatrix g)).charpoly.roots).sum = _
  rw [Matrix.charpoly_toLin']
  rfl

theorem b63d_naturalRep_rank (g : b4b_Group) :
    Module.finrank ℂ (LinearMap.range (b63d_naturalRep g - LinearMap.id)) =
      (b4b_toMatrix g - 1).rank := by
  have he : b63d_naturalRep g - LinearMap.id = Matrix.toLin' (b4b_toMatrix g - 1) := by
    change Matrix.toLin' (b4b_toMatrix g) - LinearMap.id = _
    rw [map_sub, Matrix.toLin'_one]
  exact congrArg (fun f : (Fin 4 → ℂ) →ₗ[ℂ] (Fin 4 → ℂ) ↦
    Module.finrank ℂ (LinearMap.range f)) he

section Cover
variable (C : Type) [TopologicalSpace C] [ChartedSpace ℂ C]
  [IsManifold 𝓘(ℂ, ℂ) ω C] [T2Space C] [CompactSpace C] [ConnectedSpace C]
  [MulAction b4b_Group C] [FaithfulSMul b4b_Group C]
  (hG : ∀ g : b4b_Group, ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω (fun x : C ↦ g • x))
  (p : C → OnePoint ℂ) (hp : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω p)
  (hs : Function.Surjective p) (hgal : b4_IsGaloisCover b4b_Group p)

include p hp hs hgal

theorem b63d_cover_natural_holoCW :
    (Module.finrank ℂ (b4_HomG b63d_naturalRep
      (fun g ↦ b4_formAct ℂ (C := C) g) (b3_HolForm ℂ C)) : ℝ) =
      ∑ᶠ x : C, (Nat.card (MulAction.stabilizer b4b_Group x) : ℝ) /
        Fintype.card b4b_Group * g32h_age
          (b4b_toMatrix (b63d_rotationGenerator C hG x)) - 4 := by
  have h := b4_chevalleyWeil_holo (by simp : Module.finrank ℂ ℂ = 1) hG
    (b63d_invariantForms_eq_bot C hG p hp hs hgal)
    (b63d_rotationGenerator C hG) (b63d_rotationGenerator_isRotGen C hG)
    b63d_naturalRep b63d_naturalRep_nontrivial
  simpa only [b63d_naturalRep_age, b63d_naturalRep_finrank, Nat.cast_ofNat] using h

theorem b63d_cover_natural_topCW :
    (Module.finrank ℂ (b4_HomG b63d_naturalRep
      (fun g ↦ b4_cplxAct ℂ (C := C) g) ⊤) : ℝ) =
      ∑ᶠ x : C, (Nat.card (MulAction.stabilizer b4b_Group x) : ℝ) /
        Fintype.card b4b_Group * ((b4b_toMatrix (b63d_rotationGenerator C hG x) - 1).rank : ℝ)
        - 8 := by
  have h := b4_chevalleyWeil_top (by simp : Module.finrank ℂ ℂ = 1) hG
    (b63d_invariantForms_eq_bot C hG p hp hs hgal)
    (b63d_rotationGenerator C hG) (b63d_rotationGenerator_isRotGen C hG)
    b63d_naturalRep b63d_naturalRep_nontrivial
  simpa only [b63d_naturalRep_rank, b63d_naturalRep_finrank, Nat.cast_ofNat,
    show (2 : ℝ) * 4 = 8 by norm_num] using h

theorem b63d_cover_conjugate_holoCW :
    (Module.finrank ℂ (b4_HomG (HurwitzPrymRex_barRep b63d_naturalRep)
      (fun g ↦ b4_formAct ℂ (C := C) g) (b3_HolForm ℂ C)) : ℝ) =
      ∑ᶠ x : C, (Nat.card (MulAction.stabilizer b4b_Group x) : ℝ) /
        Fintype.card b4b_Group * b4_age
          (HurwitzPrymRex_barRep b63d_naturalRep (b63d_rotationGenerator C hG x)) - 4 := by
  have h := b4_chevalleyWeil_holo (by simp : Module.finrank ℂ ℂ = 1) hG
    (b63d_invariantForms_eq_bot C hG p hp hs hgal)
    (b63d_rotationGenerator C hG) (b63d_rotationGenerator_isRotGen C hG)
    (HurwitzPrymRex_barRep b63d_naturalRep) b63d_conjugateRep_nontrivial
  simpa only [b63d_conjugateRep_finrank, Nat.cast_ofNat] using h

end Cover
end HodgeLean.Foundations.Program
