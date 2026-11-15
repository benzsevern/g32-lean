import HodgeLean.Adapters.NormalConeB4aGysinRegularGraphOpen

noncomputable section
namespace HodgeLean.Adapters

/-- A parametrization embedded only on an open parameter domain represents its
whole domain image locally by a holomorphic graph at each regular point. -/
theorem a3b4a_gysin_open_embedded_regular_graph_neighborhood
    {n c : ℕ} (h : (Fin n → ℂ) → ((Fin n → ℂ) × (Fin c → ℂ)))
    (U : Set (Fin n → ℂ)) (hU : IsOpen U)
    (he : Topology.IsEmbedding (fun z : U => h z))
    (x : Fin n → ℂ) (hxU : x ∈ U) (hh : AnalyticAt ℂ h x)
    (hp : IsUnit (fderiv ℂ (fun z => (h z).1) x)) :
    ∃ (O : Set ((Fin n → ℂ) × (Fin c → ℂ)))
      (ψ : C((Fin n → ℂ), (Fin c → ℂ))),
      IsOpen O ∧ h x ∈ O ∧
      (∀ p ∈ O, AnalyticAt ℂ ψ p.1) ∧
      ∀ p ∈ O, p ∈ h '' U ↔ p.2 = ψ p.1 := by
  obtain ⟨E, ψ, hx, hEU, hcoord, hψ, himage⟩ :=
    a3b4a_gysin_regular_graph_inside_open h x hh hp U hU hxU
  let A : Set U := Subtype.val ⁻¹' E.source
  have hA : IsOpen A := E.open_source.preimage continuous_subtype_val
  obtain ⟨W, hW, hpre⟩ := he.isInducing.isOpen_iff.mp hA
  have hxW : h x ∈ W := by
    have hxA : (⟨x, hxU⟩ : U) ∈ A := hx
    rw [← hpre] at hxA
    exact hxA
  let O := W ∩ Prod.fst ⁻¹' E.target
  have hxO : h x ∈ O := by
    refine ⟨hxW, ?_⟩
    change (h x).1 ∈ E.target
    rw [← hcoord]
    exact E.map_source hx
  refine ⟨O, ψ, hW.inter (E.open_target.preimage continuous_fst), hxO,
    fun p hpO => hψ p.1 hpO.2, ?_⟩
  intro p hpO
  constructor
  · rintro ⟨z, hzU, hzp⟩
    have hzW : h z ∈ W := hzp.symm ▸ hpO.1
    have hzA : (⟨z, hzU⟩ : U) ∈ A := by
      rw [← hpre]
      exact hzW
    have hpimage : p ∈ h '' E.source := ⟨z, hzA, hzp⟩
    rw [himage] at hpimage
    exact hpimage.2
  · intro hpGraph
    have hpimage : p ∈ h '' E.source := by
      rw [himage]
      exact ⟨hpO.2, hpGraph⟩
    obtain ⟨z, hz, hzp⟩ := hpimage
    exact ⟨z, hEU hz, hzp⟩

end HodgeLean.Adapters
