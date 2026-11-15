import HodgeLean.Foundations.Program.SchoenTowerHardt6RbCompactHeightBaseChange
import HodgeLean.Foundations.Program.SchoenTowerHardt6RbTriangulatedCarrierFormula
import HodgeLean.Foundations.Program.SchoenTowerHardt6RbGraphCompose

/-! An actual finite triangulation transports through the prepared base map with its full Boolean graph. -/
noncomputable section
set_option maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

theorem s2v_hardt6rb_triangulation_height_base_change {n : ℕ}
    (K : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin (n + 1)))) (hK : K.faces.Finite)
    (U : Set (EuclideanSpace ℝ (Fin (n + 1)))) (H : K.space ≃ₜ U)
    (J : s2v_t11b_Formula ((n + 1) + (n + 1)))
    (hJ : ∀ z, z ∈ J.realize ↔ ∃ x : K.space,
      (∀ i, z (Fin.castAdd (n + 1) i) = x.val i) ∧ (∀ i, z (Fin.natAdd (n + 1) i) = (H x).val i))
    (A : Set (EuclideanSpace ℝ (Fin n))) (β : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (hβ : ContinuousOn β A) (hβinj : Set.InjOn β A)
    (G : s2v_t11b_Formula (n + n))
    (hG : ∀ z, z ∈ G.realize ↔ ∃ x ∈ A,
      (∀ i, z (Fin.castAdd n i) = x i) ∧ (∀ i, z (Fin.natAdd n i) = β x i))
    (e : (EuclideanSpace ℝ (Fin n) × ℝ) ≃L[ℝ] EuclideanSpace ℝ (Fin (n + 1)))
    (he0 : ∀ p, e p 0 = p.2) (hes : ∀ p i, e p i.succ = p.1 i)
    (hbase : ∀ z ∈ U, (e.symm z).1 ∈ A) :
    let φ := fun z => e (β (e.symm z).1, (e.symm z).2)
    ∃ h : K.space ≃ₜ (φ '' U), ∃ R : s2v_t11b_Formula ((n + 1) + (n + 1)),
      (∀ x, (h x).val = φ (H x).val) ∧
      (∀ z, z ∈ R.realize ↔ ∃ x : K.space,
        (∀ i, z (Fin.castAdd (n + 1) i) = x.val i) ∧ (∀ i, z (Fin.natAdd (n + 1) i) = (h x).val i)) := by
  intro φ
  obtain ⟨hU, F, hF⟩ := s2v_hardt6rb_triangulated_carrier_formula K hK U H J hJ
  obtain ⟨k₀, R₀, hk₀, hR₀⟩ := s2v_hardt6rb_compact_height_base_change A β hβ hβinj G hG F
    (hF.symm ▸ hU) e he0 hes (fun z hz => hbase z (hF ▸ hz))
  let k : U ≃ₜ (φ '' U) := (Homeomorph.setCongr hF.symm).trans
    (k₀.trans (Homeomorph.setCongr (congrArg (fun S => φ '' S) hF)))
  have hk (x : U) : (k x).val = φ x.val := hk₀ ⟨x.val, hF.symm ▸ x.property⟩
  have hR (z) : z ∈ R₀.realize ↔ ∃ x : U,
      (∀ i, z (Fin.castAdd (n + 1) i) = x.val i) ∧
      (∀ i, z (Fin.natAdd (n + 1) i) = (k x).val i) := by
    rw [hR₀]
    constructor
    · rintro ⟨x, hx, hy⟩
      exact ⟨⟨x.val, hF ▸ x.property⟩, hx, hy⟩
    · rintro ⟨x, hx, hy⟩
      exact ⟨⟨x.val, hF.symm ▸ x.property⟩, hx, hy⟩
  obtain ⟨R, hR⟩ := s2v_hardt6rb_actual_graph_compose K.space U (φ '' U) H k J R₀ hJ hR
  exact ⟨H.trans k, R, fun x => hk (H x), hR⟩

end HodgeLean.Foundations.Program
