import HodgeLean.Adapters.NormalConeB4aGysinEmbeddedGraphOpen
import HodgeLean.Adapters.NormalConeB4aGysinGraphNormal

noncomputable section
namespace HodgeLean.Adapters
open CategoryTheory AlgebraicGeometry
open HodgeLean.Foundations.Analytic

/-- An embedded regular parametrization of the actual local support supplies
its holomorphic normal chart with identity vertical derivative. -/
theorem a3b4a_gysin_open_embedded_support_normal_chart
    {Z : Scheme.{0}} {q : Z ⟶ Spec (CommRingCat.of ℂ)}
    [LocallyOfFiniteType q] [QuasiCompact q] [IsSeparated q]
    (γ : AlgebraicCycle Z ℚ) {n c : ℕ}
    (Φ : OpenPartialHomeomorph (ComplexPoint (Over.mk q))
      ((Fin n → ℂ) × (Fin c → ℂ))) (hΦ : a3b4_IsHolChart q Φ)
    (h : (Fin n → ℂ) → ((Fin n → ℂ) × (Fin c → ℂ)))
    (U : Set (Fin n → ℂ)) (hU : IsOpen U)
    (he : Topology.IsEmbedding (fun z : U => h z))
    (x : Fin n → ℂ) (hxU : x ∈ U) (hh : AnalyticAt ℂ h x)
    (hp : IsUnit (fderiv ℂ (fun z => (h z).1) x)) (hx : h x ∈ Φ.target)
    (hS : ∀ y ∈ Φ.source, y ∈ a3b4_cycleSupport q γ ↔ Φ y ∈ h '' U) :
    ∃ C : A3b4aGysinNormalChart q γ c, C.point = Φ.symm (h x) ∧
      HasFDerivAt (fun v' => (C.chart (Φ.symm ((h x).1, v' + (h x).2))).2)
        (ContinuousLinearMap.id ℂ (Fin c → ℂ)) 0 := by
  letI : LocallyOfFiniteType (Over.mk q).hom := ‹LocallyOfFiniteType q›
  letI : QuasiCompact (Over.mk q).hom := ‹QuasiCompact q›
  letI : IsSeparated (Over.mk q).hom := ‹IsSeparated q›
  obtain ⟨O, ψ, hO, hxO, hψ, hgraph⟩ :=
    a3b4a_gysin_open_embedded_regular_graph_neighborhood h U hU he x hxU hh hp
  let W := Φ.source ∩ Φ ⁻¹' O
  have hW : IsOpen W := Φ.isOpen_inter_preimage hO
  let Ψ := Φ.restrOpen W hW
  have hy : Φ.symm (h x) ∈ Ψ.source := by
    refine ⟨Φ.map_target hx, Φ.map_target hx, ?_⟩
    change Φ (Φ.symm (h x)) ∈ O
    rwa [Φ.right_inv hx]
  have hxΨ : h x ∈ Ψ.target := by
    have hmem := Ψ.map_source hy
    change Φ (Φ.symm (h x)) ∈ Ψ.target at hmem
    rwa [Φ.right_inv hx] at hmem
  have hhol : a3b4_IsHolChart q Ψ := by
    constructor
    · intro j
      exact anrem_isHolFun_restrict (f4_analytification (Over.mk q))
        (fun _ hz => hz.1) (hΦ.1 j)
    · intro j
      exact anrem_isHolFun_restrict (f4_analytification (Over.mk q))
        (fun _ hz => hz.1) (hΦ.2 j)
  have hψ' : ∀ y ∈ Ψ.source, AnalyticAt ℂ ψ (Ψ y).1 :=
    fun y hy => hψ (Φ y) hy.2.2
  have hgraph' : ∀ y ∈ Ψ.source,
      y ∈ a3b4_cycleSupport q γ ↔ (Ψ y).2 = ψ (Ψ y).1 := by
    intro y hy
    exact (hS y hy.1).trans (hgraph (Φ y) hy.2.2)
  have hs : Φ.symm (h x) ∈ a3b4_cycleSupport q γ := by
    apply (hS _ (Φ.map_target hx)).mpr
    rw [Φ.right_inv hx]
    exact ⟨x, hxU, rfl⟩
  exact a3b4a_gysin_graph_normal_chart γ Ψ hhol ψ hψ' hgraph'
    (h x).1 (h x).2 hxΨ hs

end HodgeLean.Adapters
