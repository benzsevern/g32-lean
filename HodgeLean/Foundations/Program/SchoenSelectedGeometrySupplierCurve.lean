import HodgeLean.Foundations.Program.G32SelectedRealizationSecond
import HodgeLean.Foundations.Program.G32SelectedProp46
import HodgeLean.Foundations.Program.RiemannSurfaceQuotient
import HodgeLean.Adapters.CycleClassPullbackDefs
import HodgeLean.Foundations.Program.UniversalFamilyB60cIsogeny
import HodgeLean.Foundations.Program.CycleFoundationsPullback

noncomputable section
set_option maxRecDepth 2000
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open HodgeLean.RealDefs HodgeLean.Adapters HodgeLean.Papers HodgeLean.Foundations
open HodgeLean.Foundations.Symplectic
open scoped Manifold ContDiff TensorProduct CategoryTheory.MonObj
namespace HodgeLean.Foundations.Program
attribute [local instance] b65z_SharedFamily.topC b65z_SharedFamily.chartC
  b65z_SharedFamily.manC b65z_SharedFamily.t2C b65z_SharedFamily.compactC
  b65z_SharedFamily.connectedC b65z_SharedFamily.actionC b65z_SharedFamily.fibreChart
  b65z_SharedFamily.fibreMan b65z_SharedFamily.fibreT2 b65z_SharedFamily.fibreCompact
  b65z_SharedFamily.fibreConnected b65z_SharedFamily.fibreFaithful b65z_SharedFamily.totalChart b65z_SharedFamily.totalMan

/-- Analytic quotient curves and their cyclic deck action on the actual retained fibre.
Source: G32 v0.16, §4.1; Miranda, Algebraic Curves and Riemann Surfaces,
Ch. III, Theorem 3.4; `rsq_exists_manifold`, `rsq_faithful_quotient`. -/
theorem s0_supplier_curve_aux {c : Fin 10 → ℂ} {g : Fin 13 → b4b_Group}
    (D : b65z_SharedFamily c g) (t : b6t_polydisc c) (S : g32p_Supplier) :
    let C := b65z_fibre c D.C t
    let Y := rsq_Quot S.χ.ker C
    let Z := rsq_Quot S.H C
    ∃ e : (S.H ⧸ S.χ.ker) ≃* Multiplicative (ZMod S.m),
      (∀ h : S.H, e (QuotientGroup.mk h) = S.χ h) ∧
      FaithfulSMul (S.H ⧸ S.χ.ker) Y ∧
      ∃ cy : ChartedSpace ℂ Y, ∃ cz : ChartedSpace ℂ Z,
        letI := cy
        letI := cz
        IsManifold 𝓘(ℂ, ℂ) ω Y ∧ IsManifold 𝓘(ℂ, ℂ) ω Z ∧
        ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω (rsq_proj S.χ.ker C) ∧
        ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω (rsq_proj S.H C) ∧
        ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω (rsq_coarsen (X := C) S.χ.ker) ∧
        (∀ a : S.H ⧸ S.χ.ker,
          ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω (fun y : Y ↦ a • y)) ∧
        (∀ x : C, rsq_coarsen S.χ.ker (rsq_proj S.χ.ker C x) = rsq_proj S.H C x) := by
  classical
  let C := b65z_fibre c D.C t
  have hH : ∀ h : S.H,
      ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω (fun x : C ↦ h • x) :=
    fun h ↦ D.hG t h
  have hK : ∀ h : S.χ.ker,
      ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω (fun x : C ↦ h • x) :=
    fun h ↦ hH h
  letI := rsq_t2Space (Module.finrank_self ℂ) (fun h ↦ (hH h).continuous)
  letI := rsq_t2Space (Module.finrank_self ℂ) (fun h ↦ (hK h).continuous)
  obtain ⟨cy, hy, hπy⟩ := rsq_exists_manifold (Module.finrank_self ℂ) hK
  obtain ⟨cz, hz, hπz⟩ := rsq_exists_manifold (Module.finrank_self ℂ) hH
  letI := cy
  letI := cz
  letI := hy
  letI := hz
  refine ⟨QuotientGroup.quotientKerEquivOfSurjective S.χ S.surjective,
    fun h ↦ rfl, rsq_faithful_quotient (Module.finrank_self ℂ) hH S.χ.ker,
    cy, cz, hy, hz, hπy, hπz, ?_, ?_, fun x ↦ rfl⟩
  · exact rsq_contMDiff_of_comp (Module.finrank_self ℂ) hK hπy _ hπz
  · intro a
    induction a using QuotientGroup.induction_on with
    | H h =>
      exact rsq_contMDiff_of_comp (Module.finrank_self ℂ) hK hπy _
        (hπy.comp (hH h))


#print axioms s0_supplier_curve_aux
end HodgeLean.Foundations.Program
