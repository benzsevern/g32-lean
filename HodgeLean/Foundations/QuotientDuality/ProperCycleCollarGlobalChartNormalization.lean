import HodgeLean.Foundations.QuotientDuality.ProperCycleCollarChartCapPoint
import HodgeLean.Foundations.QuotientDuality.ProperCycleCollarComplexCapScalar
import HodgeLean.Foundations.QuotientDuality.ProperCycleChartImageComplexOrientation
import HodgeLean.Foundations.QuotientDuality.ProperCycleOpenPointDegree

/-! # Original global supported cap values in complex chart coordinates
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicTopology.Singular TopologicalSpace
open HodgeLean.Foundations.Program
namespace HodgeLean.Foundations.QuotientDuality

/-- A literal normal multiplicity in the original supported restriction gives that multiplicity times the original complex cap scalar in the actual global support point value, with the original compressed chart orientation.
Source: ProperCycleSupportCollar.chart_cap_point; ProperCycleSupportCollar.chart_complex_cap_scalar; properCycle_chart_image_complex_orientation.
HC no distance; AV milestone no distance. -/
lemma ProperCycleSupportCollar.global_chart_normalization
    {X : TopCat.{0}} [T1Space X] {S : Set X} (C : ProperCycleSupportCollar X S) (hS : IsClosed S)
    (r d : ℕ) (e : OpenPartialHomeomorph X ((Fin r → ℂ) × (Fin d → ℂ)))
    (W : Opens X) (hWe : (W : Set X) ⊆ e.source) (hWN : (W : Set X) ⊆ C.neighborhood)
    (hR : ∀ (x : X) (hx : x ∈ W), (C.retraction ⟨x, hWN hx⟩).val ∈ e.source)
    (hflat : ∀ x ∈ e.source, x ∈ S ↔ (e x).2 = 0)
    (z : S) (hzW : z.val ∈ W) (hcenter : e z.val = (0, 0)) (m : ℚ)
    (a : CohomologyWithSupport ℚ X S (2*d))
    (ha : relativeCohomologyMap ℚ (2*d) (b6m_subspacePairMap X (W : Set X) Sᶜ) a =
      m • chartNormalProjectionCoclass (Fin r → ℂ) d e S hflat (W : Set X) hWe)
    (c : Homology ℚ X (2*d+2*r)) :
    let L : ((Fin r → ℂ) × (Fin d → ℂ)) ≃L[ℂ] (Fin (r+d) → ℂ) :=
      ContinuousLinearEquiv.ofFinrankEq
        (by simp only [Module.finrank_prod, Module.finrank_pi, Fintype.card_fin])
    let φ := e.trans L.toHomeomorph.toOpenPartialHomeomorph
    let degree := eqToIso (congrArg (fun n => orientationGroup X n z.val)
      (show 2*(r+d) = 2*d+2*r by omega))
    localOrientation X (2*d+2*r) c z.val = degree.hom.hom
      (localClassOfChart (r+d) φ z.val ⟨hWe hzW, Set.mem_univ _⟩) →
    let V : Opens (TopCat.of S) := ⟨{s : S | s.val ∈ e.source},
      e.open_source.preimage continuous_subtype_val⟩
    relativeHomologyMap ℚ (2*r)
      (properCycle_flat_support_point_pair X S e 0 hflat z (hWe hzW) (congrArg Prod.fst hcenter))
      ((properCycle_open_local_homology_iso (TopCat.of S) V ⟨z, hWe hzW⟩ (2*r)).inv.hom
        (localOrientation (TopCat.of S) (2*r) (C.cap hS (2*d) (2*r) c a) z)) =
      (m * properCycle_standard_complex_cap_scalar r d) • standardComplexLocalClass ℚ r := by
  dsimp only
  intro hc
  let b := m • relativeCohomologyMap ℚ (2*d)
    (properCycle_product_support_projection (Fin r → ℂ) (TopCat.of (Fin d → ℂ)) {0})
    (normalizedRelativeCoclass (standardComplexLocalClass ℚ d)
      (standardComplexLocalClass_ne_zero_for_chart d))
  have ha' : relativeCohomologyMap ℚ (2*d) (b6m_subspacePairMap X (W : Set X) Sᶜ) a =
      relativeCohomologyMap ℚ (2*d)
        (TopPair.ofSubsetHom (X := TopCat.of W)
          (Y := TopCat.of ((Fin r → ℂ) × (Fin d → ℂ)))
          (TopPair.Hom.fst (C.chart_retraction_point_pair (Fin r → ℂ) (TopCat.of (Fin d → ℂ))
            e W hWe hWN hR 0 hflat z hzW hcenter))
          (C.chart_retraction_triad_maps (Fin r → ℂ) (TopCat.of (Fin d → ℂ))
            e W hWe hWN hR 0 hflat z hzW hcenter).1) b := by
    dsimp only [b]
    rw [map_smul, C.chart_normal_coclass (Fin r → ℂ) d e W hWe hWN hR hflat z hzW hcenter]
    exact ha
  let v := C.chart_local_support_cap hS (Fin r → ℂ) (TopCat.of (Fin d → ℂ))
    e W hWe hWN hR 0 hflat z hzW hcenter (2*d) (2*r)
    ((properCycle_open_local_homology_iso X W ⟨z.val, hzW⟩ (2*d+2*r)).inv.hom
      (localOrientation X (2*d+2*r) c z.val)) b
  have h := C.chart_cap_point hS (Fin r → ℂ) (TopCat.of (Fin d → ℂ))
    e W hWe hWN hR 0 hflat z hzW hcenter (2*d) (2*r) a b ha' c
  let V : Opens (TopCat.of S) := ⟨{s : S | s.val ∈ e.source},
    e.open_source.preimage continuous_subtype_val⟩
  let o := properCycle_open_local_homology_iso (TopCat.of S) V ⟨z, hWe hzW⟩ (2*r)
  have hInv : o.inv.hom (localOrientation (TopCat.of S) (2*r) (C.cap hS (2*d) (2*r) c a) z) = v := by
    apply o.toLinearEquiv.injective
    change o.hom.hom (o.inv.hom _) = o.hom.hom v
    rw [o.inv_hom_id_apply]
    have ho := LinearMap.congr_fun
      (properCycle_open_local_homology_iso_map (TopCat.of S) V ⟨z, hWe hzW⟩ (2*r)) v
    exact h.symm.trans ho.symm
  rw [hInv]
  dsimp only [v]
  rw [hc, properCycle_open_point_inverse_degree X W ⟨z.val, hzW⟩
    (2*(r+d)) (2*d+2*r) (by omega)]
  exact C.chart_complex_cap_scalar hS r d e W hWe hWN hR hflat z hzW hcenter _
    (properCycle_chart_image_complex_orientation X r d e W hWe z.val hzW hcenter) m

end HodgeLean.Foundations.QuotientDuality
