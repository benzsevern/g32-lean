import HodgeLean.Foundations.QuotientDuality.ProperCycleFiniteSheetOrientation
import HodgeLean.Foundations.Analytic.ComplexAnalyticSpaceBase

/-! # Holomorphic coordinates pulled back along an actual local sheet -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicTopology.Singular HodgeLean.Foundations.Analytic
namespace HodgeLean.Foundations.QuotientDuality

/-- A holomorphic map pulls the literal coordinate chart back along its actual local sheet as a holomorphic coordinate chart.
Source: Grauert--Remmert, Coherent Analytic Sheaves, section 1.1.5; Hatcher, Algebraic Topology, section 3.3.
HC no distance; AV milestone no distance. -/
lemma properCycle_holomorphic_sheet_chart_coordinates
    {X Y : TopCat.{0}} (S : an_ReducedSpace X) (T : an_ReducedSpace Y)
    (f : X ⟶ Y) (hf : an_IsHom S T f)
    (H : OpenPartialHomeomorph X Y) (hH : ∀ z : X, f z = H z)
    (d : ℕ) (e : OpenPartialHomeomorph Y (Fin d → ℂ))
    (he : ∀ i, T.IsHolFun (fun z : e.source => e z i)) :
    ∀ i, S.IsHolFun (fun z : (H.trans e).source => (H.trans e) z i) := by
  intro i
  have hi := hf.2 e.source e.open_source (fun z : e.source => e z i) (he i)
  have hsub : (H.trans e).source ⊆ f ⁻¹' e.source := by
    intro z hz
    change f z ∈ e.source
    rw [hH]
    exact hz.2
  have hr := anb_isHolFun_restrict S.atlas hsub hi
  simpa only [OpenPartialHomeomorph.trans_apply, ← hH] using hr

/-- One actual holomorphic coordinate chart at a point supplies holomorphic coordinate charts inside every prescribed open neighborhood.
Source: Grauert--Remmert, Coherent Analytic Sheaves, section 1.1.5, restriction of holomorphic functions.
HC no distance; AV milestone no distance. -/
lemma properCycle_holomorphic_chart_neighborhood_basis
    {Y : TopCat.{0}} (T : an_ReducedSpace Y) (d : ℕ) (y : Y)
    (e : OpenPartialHomeomorph Y (Fin d → ℂ)) (hy : y ∈ e.source)
    (he : ∀ i, T.IsHolFun (fun z : e.source => e z i))
    (V : Set Y) (hV : IsOpen V) (hyV : y ∈ V) :
    ∃ E : OpenPartialHomeomorph Y (Fin d → ℂ), y ∈ E.source ∧ E.source ⊆ V ∧
      ∀ i, T.IsHolFun (fun z : E.source => E z i) := by
  refine ⟨e.restrOpen V hV, ⟨hy, hyV⟩, Set.inter_subset_right, ?_⟩
  intro i
  exact anb_isHolFun_restrict T.atlas Set.inter_subset_left (he i)

end HodgeLean.Foundations.QuotientDuality
