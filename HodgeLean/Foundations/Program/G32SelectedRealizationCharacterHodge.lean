import HodgeLean.Foundations.Program.G32SelectedRealizationSubgroupActions
import HodgeLean.Foundations.Program.G32SelectedRealizationJacobianHodge
import HodgeLean.Foundations.Program.G32SelectedRealizationSimultaneousEigen
import HodgeLean.Foundations.Program.G32SelectedRealizationLinearMultiplicity

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

set_option maxHeartbeats 400000 in
theorem g32y_jacobian_character_hodge_dimension {c : Fin 10 → ℂ} {g : Fin 13 → b4b_Group}
    (D : b65z_SharedFamily c g) (t : b6t_polydisc c)
    (f : g32p_G → AbelianEnd (g32x_J D t))
    (hf : ∀ a, homPullback (f a).hom 1 = g32x_deck D t a)
    (S : g32p_Supplier) (χ : S.H →* ℂˣ) :
    Module.finrank ℂ ↥((⨅ h : S.H, Module.End.eigenspace
      ((homPullback (f h).hom 1).baseChange ℂ) (χ h : ℂ)) ⊓
        cohomologyHodgePiece (g32x_J D t) 1 (1, 0)) =
      Module.finrank ℂ (b4_HomG (papersLinRep χ).ρ
        (fun h : S.H ↦ b4_formAct ℂ (C := b65z_fibre c D.C t) h)
        (b3_HolForm ℂ (b65z_fibre c D.C t))) := by
  classical
  letI : Fintype S.H := Fintype.ofFinite S.H
  obtain ⟨e, heF, he⟩ := g32y_jacobian_hodge_comparison D t
  let A := fun h : S.H ↦ b4_cplxAct ℂ (C := b65z_fibre c D.C t) h
  let B := fun h : S.H ↦ (homPullback (f h).hom 1).baseChange ℂ
  let F := b3_periodF ℂ (b65z_fibre c D.C t)
  have hc (h : S.H) : e.toLinearMap ∘ₗ A h = B h ∘ₗ e.toLinearMap := by
    apply LinearMap.ext
    intro x
    change e (A h x) = B h (e x)
    have hB : B h = (g32x_deck D t h).baseChange ℂ := by
      dsimp only [B]
      rw [hf]
    rw [hB]
    dsimp only [A]
    rw [g32y_subgroup_cplxAct (E := ℂ) (C := b65z_fibre c D.C t) S.H h]
    exact he h x
  have hm := g32y_simultaneous_eigenspace_equiv e A B hc (fun h ↦ (χ h : ℂ))
  have hmap : ((⨅ h, Module.End.eigenspace (A h) (χ h : ℂ)) ⊓ F).map e.toLinearMap =
      (⨅ h, Module.End.eigenspace (B h) (χ h : ℂ)) ⊓
        cohomologyHodgePiece (g32x_J D t) 1 (1, 0) := by
    rw [Submodule.map_inf _ e.injective, hm, heF]
  have hd := (Submodule.equivMapOfInjective e.toLinearMap e.injective
    ((⨅ h, Module.End.eigenspace (A h) (χ h : ℂ)) ⊓ F)).finrank_eq
  rw [hmap] at hd
  rw [← hd, inf_comm]
  have hlin := g32y_linear_character_multiplicity χ
    (fun h : S.H ↦ b4_cplxAct ℂ (C := b65z_fibre c D.C t) h) F
  rw [← hlin]
  exact b4_hodge_eq_holo (by simp) (fun h : S.H ↦ D.hG t h) (papersLinRep χ).ρ

end HodgeLean.Foundations.Program
