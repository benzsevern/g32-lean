import HodgeLean.Foundations.QuotientDuality.ProperCycleHolomorphicSheetCharts
import Mathlib.Topology.IsLocalHomeomorph

/-! # Actual local degree of a finite fibre of a holomorphic local homeomorphism -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicTopology.Singular HodgeLean.Foundations.Analytic
namespace HodgeLean.Foundations.QuotientDuality

/-- Original complex-normalized global classes have local pushforward multiplicity equal to the actual finite fibre cardinality for a holomorphic map that is a local homeomorphism at every fibre point.
Source: Hatcher, Algebraic Topology, section 3.3, complex orientation and the sum of local degrees.
HC no distance; AV milestone no distance. -/
lemma properCycle_holomorphic_local_degree
    {X Y : TopCat.{0}} [T2Space X] (S : an_ReducedSpace X) (T : an_ReducedSpace Y)
    (f : X ⟶ Y) (hf : an_IsHom S T f) (y : Y)
    (hlocal : IsLocalHomeomorphOn f (f ⁻¹' {y})) (hfinite : (f ⁻¹' {y}).Finite) (d : ℕ)
    (cX : Homology ℚ X (2 * d)) (cY : Homology ℚ Y (2 * d))
    (hcomplexX : ∀ (e : OpenPartialHomeomorph X (Fin d → ℂ)),
      (∀ i, S.IsHolFun (fun z : e.source => e z i)) → ∀ (x : X) (hx : x ∈ e.source),
        localOrientation X (2 * d) cX x = localClassOfChart d e x hx)
    (hcomplexY : ∀ (e : OpenPartialHomeomorph Y (Fin d → ℂ)),
      (∀ i, T.IsHolFun (fun z : e.source => e z i)) → ∀ (z : Y) (hz : z ∈ e.source),
        localOrientation Y (2 * d) cY z = localClassOfChart d e z hz)
    (hchartsY : ∀ V : Set Y, IsOpen V → y ∈ V →
      ∃ e : OpenPartialHomeomorph Y (Fin d → ℂ), y ∈ e.source ∧ e.source ⊆ V ∧
        ∀ i, T.IsHolFun (fun z : e.source => e z i)) :
    localOrientation Y (2 * d) (homologyMap ℚ (2 * d) f cX) y =
      (Nat.card (f ⁻¹' {y}) : ℚ) • localOrientation Y (2 * d) cY y := by
  classical
  letI : Fintype (f ⁻¹' {y}) := hfinite.fintype
  rw [properCycle_finite_fibre_local_pushforward f y hfinite]
  have hpoint (x : f ⁻¹' {y}) :
      properCycle_finite_fibre_point_pushforward f y hfinite (2 * d) x
        (localOrientation X (2 * d) cX x.val) = localOrientation Y (2 * d) cY y := by
    obtain ⟨H, hx, hH⟩ := hlocal x.val x.property
    have hH' : ∀ z : X, f z = H z := congrFun hH
    have hxy : H x.val = y := (hH' x.val).symm.trans x.property
    obtain ⟨e, hy, he, hhol⟩ := hchartsY H.target H.open_target (hxy ▸ H.map_source hx)
    have hxe : H x.val ∈ e.source := hxy.symm ▸ hy
    have hsource := properCycle_holomorphic_sheet_chart_coordinates S T f hf H hH' d e hhol
    rw [hcomplexX (H.trans e) hsource x.val ⟨hx, hxe⟩, hcomplexY e hhol y hy]
    exact properCycle_finite_sheet_chart_orientation f y hfinite x d H hH' hx e he hy
  simp only [hpoint, Finset.sum_const, Finset.card_univ, Nat.card_eq_fintype_card,
    Nat.cast_smul_eq_nsmul]

end HodgeLean.Foundations.QuotientDuality
