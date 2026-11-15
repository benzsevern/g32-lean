import HodgeLean.Foundations.Program.PrymVariationCentreEigenBasics

noncomputable section
open HodgeLean.Papers
open scoped Manifold ContDiff TensorProduct
namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000 in
theorem b63d_saturated_eigen_ranks (C : Type) [TopologicalSpace C] [ChartedSpace ℂ C]
    [IsManifold 𝓘(ℂ, ℂ) ω C] [T2Space C] [CompactSpace C] [ConnectedSpace C]
    [MulAction b4b_Group C]
    (hG : ∀ g : b4b_Group, ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω (fun x : C ↦ g • x))
    (hm : Module.finrank ℂ (b4_HomG b63d_naturalRep
      (fun g ↦ b4_cplxAct ℂ (C := C) g) (b3_periodF ℂ C)) = 3 ∧
      Module.finrank ℂ (b4_HomG (HurwitzPrymRex_barRep b63d_naturalRep)
        (fun g ↦ b4_cplxAct ℂ (C := C) g) (b3_periodF ℂ C)) = 3) :
    Module.finrank ℂ (b63d_eigenF C hG g32h_omega) = 3 ∧
    Module.finrank ℂ (b63d_eigenF C hG (star g32h_omega)) = 3 := by
  letI : Module.Finite ℤ (b3_periodLattice ℂ C) := b3_periodLattice_finite (by simp)
  letI : Module.Free ℤ (b3_periodLattice ℂ C) := b3_periodLattice_free
  letI : Module.Finite ℤ (b63l_periodLattice C) := inferInstance
  letI : Module.Free ℤ (b63l_periodLattice C) := inferInstance
  let I := (b63l_periodLattice C).subtype.baseChange ℂ
  let σ := b63d_periodRep C hG
  let a : b4b_Group → ℂ := fun g ↦ (b4b_projectorCoeff g : ℂ)
  let D : ℂ := b4b_projectorDenominator
  have hD : D ≠ 0 := by norm_num [D, b4b_projectorDenominator]
  have hr : LinearMap.range I = LinearMap.range (∑ g, a g • σ g) := by
    change LinearMap.range I = LinearMap.range (∑ g : b4b_Group,
      (b4b_projectorCoeff g : ℂ) • b4_cplxAct ℂ (C := C) g)
    rw [← b4_cplxMap_groupEnd]
    exact b63d_saturated_operator_complex_range (b4_groupEnd ℂ (C := C) b4b_projectorCoeff)
  have hT : (b4b_centreAct C hG).toIntLinearMap.baseChange ℂ = σ b63d_scalarElement := by
    rw [b63d_period_centre_scalar]
    rfl
  let v₀ : Fin 4 → ℂ := Pi.single 0 1
  have hv₀ : v₀ ≠ 0 := by intro h; have h0 := congrFun h 0; norm_num [v₀] at h0
  have hp : (∑ g, a g • b63d_naturalRep g) v₀ = D • v₀ := by
    rw [b63d_naturalRep_projector_apply]
    simp only [v₀, Pi.single_eq_same, mul_one, D]
  have h1 := b63d_eigen_lower_bound b63d_naturalRep σ (b3_periodF ℂ C) I a hr
    b63d_scalarElement g32h_omega D hD v₀ hv₀ hp (b63d_naturalRep_scalar v₀)
  have hbv : HurwitzPrymRex_Bar.of v₀ ≠ 0 := by
    intro h
    exact hv₀ (congrArg HurwitzPrymRex_Bar.val h)
  have hbp : (∑ g, a g • HurwitzPrymRex_barRep b63d_naturalRep g)
      (HurwitzPrymRex_Bar.of v₀) = D • HurwitzPrymRex_Bar.of v₀ := by
    apply HurwitzPrymRex_Bar.ext
    rw [b63d_conjugateRep_projector_val]
    change (∑ g, a g • b63d_naturalRep g) v₀ = star D • v₀
    rw [hp]
    norm_num [D, b4b_projectorDenominator]
  have h2 := b63d_eigen_lower_bound (HurwitzPrymRex_barRep b63d_naturalRep) σ
    (b3_periodF ℂ C) I a hr b63d_scalarElement (star g32h_omega) D hD
    (HurwitzPrymRex_Bar.of v₀) hbv hbp
    (b63d_conjugateRep_scalar (HurwitzPrymRex_Bar.of v₀))
  change Module.finrank ℂ (b4_HomG b63d_naturalRep
    (fun g ↦ b4_cplxAct ℂ (C := C) g) (b3_periodF ℂ C)) ≤ _ at h1
  change Module.finrank ℂ (b4_HomG (HurwitzPrymRex_barRep b63d_naturalRep)
    (fun g ↦ b4_cplxAct ℂ (C := C) g) (b3_periodF ℂ C)) ≤ _ at h2
  have hl1 := (le_of_eq hm.1.symm).trans h1
  have hl2 := (le_of_eq hm.2.symm).trans h2
  have hEF (z : ℂ) : b63d_eigenF C hG z =
      (b3_periodF ℂ C).comap I ⊓
        (LinearMap.ker (σ b63d_scalarElement - z • LinearMap.id)).comap I :=
    congrArg (fun T : (ℂ ⊗[ℤ] b3_periodLattice ℂ C) →ₗ[ℂ] (ℂ ⊗[ℤ] b3_periodLattice ℂ C) ↦
      (b3_periodF ℂ C).comap I ⊓ (LinearMap.ker (T - z • LinearMap.id)).comap I) hT
  have hfin (z : ℂ) := congrArg
    (fun P : Submodule ℂ (ℂ ⊗[ℤ] b63l_periodLattice C) ↦ Module.finrank ℂ P) (hEF z)
  have h1' : 3 ≤ Module.finrank ℂ (b63d_eigenF C hG g32h_omega) :=
    hl1.trans_eq (hfin g32h_omega).symm
  have h2' : 3 ≤ Module.finrank ℂ (b63d_eigenF C hG (star g32h_omega)) :=
    hl2.trans_eq (hfin (star g32h_omega)).symm
  have hi : Function.Injective I := Module.Flat.lTensor_preserves_injective_linearMap
    (b63l_periodLattice C).subtype (b63l_periodLattice C).subtype_injective
  have hd : Disjoint (b63d_eigenF C hG g32h_omega)
      (b63d_eigenF C hG (star g32h_omega)) :=
    b63d_eigen_pullback_disjoint ((b4b_centreAct C hG).toIntLinearMap.baseChange ℂ) I hi (b63l_periodF C) _ _ b63d_omega_ne_star
  exact b63d_finrank_three_of_disjoint (b63l_periodF C)
    (b63d_eigenF C hG g32h_omega) (b63d_eigenF C hG (star g32h_omega))
    (b63d_saturated_dimensions C hG hm).2.1 inf_le_left inf_le_left hd h1' h2'

end HodgeLean.Foundations.Program
