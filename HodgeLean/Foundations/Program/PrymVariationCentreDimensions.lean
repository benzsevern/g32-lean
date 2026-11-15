import HodgeLean.Foundations.Program.PrymVariationCentreSaturatedFiltration

noncomputable section
open scoped Manifold ContDiff TensorProduct
namespace HodgeLean.Foundations.Program

theorem b63d_saturated_dimensions (C : Type) [TopologicalSpace C] [ChartedSpace ℂ C]
    [IsManifold 𝓘(ℂ, ℂ) ω C] [T2Space C] [CompactSpace C] [ConnectedSpace C]
    [MulAction b4b_Group C]
    (hG : ∀ g : b4b_Group, ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω (fun x : C ↦ g • x))
    (hm : Module.finrank ℂ (b4_HomG b63d_naturalRep
      (fun g ↦ b4_cplxAct ℂ (C := C) g) (b3_periodF ℂ C)) = 3 ∧
      Module.finrank ℂ (b4_HomG (HurwitzPrymRex_barRep b63d_naturalRep)
        (fun g ↦ b4_cplxAct ℂ (C := C) g) (b3_periodF ℂ C)) = 3) :
    Module.finrank ℤ (b63l_periodLattice C) = 12 ∧
    Module.finrank ℂ (b63l_periodF C) = 6 ∧
    Module.finrank ℂ ((ℂ ⊗[ℤ] b63l_periodLattice C) ⧸ b63l_periodF C) = 6 := by
  letI : Module.Finite ℤ (b3_periodLattice ℂ C) := b3_periodLattice_finite (by simp)
  letI : Module.Free ℤ (b3_periodLattice ℂ C) := b3_periodLattice_free
  letI : Module.Finite ℤ (b63l_periodLattice C) := inferInstance
  letI : Module.Free ℤ (b63l_periodLattice C) := inferInstance
  have hsat := b63d_saturated_image_filtration_rank
    (b4_groupEnd ℂ (C := C) b4b_projectorCoeff) (b3_periodF ℂ C)
  have hF : Module.finrank ℂ (b63l_periodF C) = 6 := by
    exact hsat.trans (b63d_exact_periodF_rank C hG hm)
  obtain ⟨Q, hQ⟩ := b3_exists_intersectionForm (C := C) (by simp : Module.finrank ℂ ℂ = 1)
  have hw := (b63l_image_riemann C hG Q hQ).2.1
  have ht := Submodule.finrank_add_eq_of_isCompl hw
  have hc := b2a_finrank_conjSubmodule (b63l_periodF C)
  have hb : Module.finrank ℂ (ℂ ⊗[ℤ] b63l_periodLattice C) =
      Module.finrank ℤ (b63l_periodLattice C) := Module.finrank_baseChange
  have hq := Submodule.finrank_quotient_add_finrank (b63l_periodF C)
  omega

end HodgeLean.Foundations.Program
