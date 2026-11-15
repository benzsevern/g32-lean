import HodgeLean.Foundations.Program.RigidStartingSystemSmallCircles
import HodgeLean.Foundations.Program.RigidStartingSystemCircleShrink

noncomputable section
open Set Metric
namespace HodgeLean.Foundations.Program

theorem b65r_source_circle_class (i : Fin 4) (R : ℝ)
    (havoid : ∀ z : ℂ, ‖z‖ < R → z ≠ 0 → b65r_sourceChart i z ∈ b65r_sourceDomain)
    (w : ℂ) (hw0 : w ≠ 0) (hw : ‖w‖ < R) :
    ∃ C : ((Fin 4 → ℂ) →L[ℂ] (Fin 4 → ℂ))ˣ,
      b65f_transport (Fin 4 → ℂ) b65r_A
        (fun t ↦ b65r_sourceChart i (Complex.exp (2*Real.pi*Complex.I*(t : ℂ))*w)) =
        C.val*b65r_operator (b4b_toMatrix (b4b_generators i))*(C⁻¹).val := by
  let W := {z : ℂ // ‖z‖ < R ∧ z ≠ 0}
  have hcont : Continuous (fun z : W ↦ b65r_sourceChart i z) := by
    apply continuous_iff_continuousAt.mpr
    intro z
    exact ((b65r_sourceChart_analytic i z z.property.2).continuousAt).comp
      continuous_subtype_val.continuousAt
  let q : C(W,b65r_sourceDomain) := ⟨fun z ↦ ⟨b65r_sourceChart i z,
    havoid z z.property.1 z.property.2⟩,hcont.subtype_mk _⟩
  obtain ⟨s,hs,hsmall⟩ := b65r_small_source_circles i
  exact b65r_shrink_circle_transport (Fin 4 → ℂ) b65r_sourceDomain
    b65r_sourceDomain_open b65r_A b65r_A_analytic (b65r_sourceChart i) R q
    (fun _ ↦ rfl) _ s hs hsmall w hw0 hw

theorem b65r_peripheral_transport (i : Fin 4) (R : ℝ)
    (havoid : ∀ z : ℂ, ‖z‖ < R → z ≠ 0 → b65r_sourceChart i z ∈ b65r_sourceDomain)
    (w : ℂ) (hw0 : w ≠ 0) (hw : ‖w‖ < R)
    {x y : b65r_sourceDomain} (k : Path x y) (d : Path y y)
    (hd : ∀ t : unitInterval, (d t : ℂ) =
      b65r_sourceChart i (Complex.exp (2*Real.pi*Complex.I*((t : ℝ) : ℂ))*w)) :
    ∃ C : ((Fin 4 → ℂ) →L[ℂ] (Fin 4 → ℂ))ˣ,
      b65f_transport (Fin 4 → ℂ) b65r_A
        (fun t ↦ (((k.trans d).trans k.symm).extend t).val) =
        C.val*b65r_operator (b4b_toMatrix (b4b_generators i))*(C⁻¹).val := by
  apply b65r_stemmed_transport (Fin 4 → ℂ) b65r_sourceDomain b65r_sourceDomain_open
    b65r_A b65r_A_analytic k d
  obtain ⟨C,hC⟩ := b65r_source_circle_class i R havoid w hw0 hw
  refine ⟨C,?_⟩
  rw [← hC]
  apply b65r_transport_eqOn
  intro t ht
  dsimp only
  rw [Path.extend_apply _ ht]
  exact hd ⟨t,ht⟩

end HodgeLean.Foundations.Program
