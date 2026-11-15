import HodgeLean.Foundations.Program.G32SelectedRealizationCentre
import HodgeLean.Foundations.Program.G32SelectedRealizationTransport

noncomputable section
set_option maxRecDepth 2000
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint TopologicalSpace
open HodgeLean.RealDefs HodgeLean.Adapters HodgeLean.Papers HodgeLean.Foundations
open scoped TensorProduct CategoryTheory.MonObj Manifold ContDiff
namespace HodgeLean.Foundations.Program
attribute [local instance] b65z_SharedFamily.topC b65z_SharedFamily.chartC
  b65z_SharedFamily.manC b65z_SharedFamily.t2C b65z_SharedFamily.compactC
  b65z_SharedFamily.connectedC b65z_SharedFamily.actionC b65z_SharedFamily.fibreChart
  b65z_SharedFamily.fibreMan b65z_SharedFamily.fibreT2 b65z_SharedFamily.fibreCompact
  b65z_SharedFamily.fibreConnected b65z_SharedFamily.totalChart b65z_SharedFamily.totalMan

theorem g32y_reference_projection {c : Fin 10 → ℂ} {g : Fin 13 → b4b_Group}
    (D : b65z_SharedFamily c g) (t : b6t_polydisc c) :
    let i0 := b63e_transportMap c D.C D.hC (b6t_polydisc c) (Set.Subset.refl _)
      D.P (b65z_s₀ c) t
    ∃ p : g32x_L D t →ₗ[ℤ]
        b63l_parameterLattice c D.C D.hC (b6t_polydisc c) (Set.Subset.refl _) (b65z_s₀ c),
      i0 ∘ₗ p = (b4_groupEnd ℂ b4b_projectorCoeff).toIntLinearMap ∧
      p ∘ₗ i0 = b4b_projectorDenominator • LinearMap.id ∧
      b3_periodF ℂ (b65z_fibre c D.C t) ≤
        (b63e_transportedF c D.C D.hC (b6t_polydisc c) (Set.Subset.refl _)
          D.P (b65z_s₀ c) t).comap (p.baseChange ℂ) := by
  classical
  let i0 := b63e_transportMap c D.C D.hC (b6t_polydisc c) (Set.Subset.refl _)
    D.P (b65z_s₀ c) t
  let P := (b4_groupEnd ℂ (C := b65z_fibre c D.C t) b4b_projectorCoeff).toIntLinearMap
  obtain ⟨E, hE, _⟩ := b63e_lattice_period_transport c D.C D.hC (b6t_polydisc c)
    (Set.Subset.refl _) D.hG D.P D.hP (b65z_s₀ c) t
  obtain ⟨p, hp, hret⟩ := g32y_saturated_marking_retraction P b4b_projectorDenominator
    (g32y_retained_projector_square D t) E
  have hIp : i0 ∘ₗ p = P := by
    apply LinearMap.ext
    intro x
    have hh := LinearMap.congr_fun hp x
    change (E (p x)).val = P x at hh
    exact (hE (p x)).symm.trans hh
  have hpI : p ∘ₗ i0 = b4b_projectorDenominator • LinearMap.id := by
    apply LinearMap.ext
    intro x
    have hh := LinearMap.congr_fun hret x
    change p (E x).val = b4b_projectorDenominator • x at hh
    rw [hE x] at hh
    exact hh
  refine ⟨p, hIp, hpI, ?_⟩
  intro x hx
  change i0.baseChange ℂ (p.baseChange ℂ x) ∈ b3_periodF ℂ (b65z_fibre c D.C t)
  have hc := congrArg (LinearMap.baseChange ℂ) hIp
  simp only [LinearMap.baseChange_comp] at hc
  have hh := LinearMap.congr_fun hc x
  simp only [LinearMap.comp_apply] at hh
  rw [hh]
  exact b4_groupEnd_periodF (E := ℂ) (D.hG t) b4b_projectorCoeff hx

theorem g32y_reference_projection_weil {c : Fin 10 → ℂ} {g : Fin 13 → b4b_Group}
    (D : b65z_SharedFamily c g) (t : b6t_polydisc c)
    (p : g32x_L D t →ₗ[ℤ]
      b63l_parameterLattice c D.C D.hC (b6t_polydisc c) (Set.Subset.refl _) (b65z_s₀ c))
    (hp : (b63e_transportMap c D.C D.hC (b6t_polydisc c) (Set.Subset.refl _)
      D.P (b65z_s₀ c) t) ∘ₗ p = (b4_groupEnd ℂ b4b_projectorCoeff).toIntLinearMap)
    (x : g32x_L D t) :
    b63g2_operator c D.C D.hC (b6t_polydisc c) (Set.Subset.refl _) (b65z_s₀ c) (p x) =
      p x + (2 : ℤ) • p (b4_latticeAct ℂ b63d_scalarElement x) := by
  let i0 := b63e_transportMap c D.C D.hC (b6t_polydisc c) (Set.Subset.refl _)
    D.P (b65z_s₀ c) t
  obtain ⟨E, hE, _⟩ := b63e_lattice_period_transport c D.C D.hC (b6t_polydisc c)
    (Set.Subset.refl _) D.hG D.P D.hP (b65z_s₀ c) t
  have hinj : Function.Injective i0 := by
    intro a b hab
    apply E.injective
    apply Subtype.ext
    exact (hE a).trans (hab.trans (hE b).symm)
  apply hinj
  rw [g32y_reference_operator_transport D t, map_add, map_zsmul]
  have hpx (v : g32x_L D t) : i0 (p v) = b4_groupEnd ℂ b4b_projectorCoeff v :=
    LinearMap.congr_fun hp v
  rw [hpx, hpx]
  rw [g32y_groupEnd_centre_commute D t b4b_projectorCoeff x]

end HodgeLean.Foundations.Program
