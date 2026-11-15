import HodgeLean.Adapters.NormalConeB4aClassHolomorphicCharts
import HodgeLean.Foundations.Analytic.ComplexAnalyticSpaceRemmertProper

/-! # Holomorphic maps detected by coordinate functions

Route: combine the finitely many coordinate representatives into one analytic
map in each source chart, then apply the analytic chart criterion for maps.
-/

noncomputable section
namespace HodgeLean.Adapters
open Set Topology TopologicalSpace
open HodgeLean.Foundations.Analytic

/-- Pullbacks of the target atlas coordinate functions detect holomorphic maps. -/
theorem a3b4a_class_isHom_of_coordinate_functions
    {M N : Type} [TopologicalSpace M] [TopologicalSpace N]
    (S : an_ReducedSpace M) (T : an_ReducedSpace N) (f : M → N) (hf : Continuous f)
    (hcoord : ∀ j, ∀ k : Fin (T.atlas.chart j).n,
      S.IsHolFun (fun x : f ⁻¹' (T.atlas.chart j).dom => (T.atlas.chart j).toFun (f x) k)) :
    an_IsHom S T f := by
  apply (an_isHom_iff_chart S T f).mpr
  refine ⟨hf, fun j i x hx => ?_⟩
  let d := T.atlas.chart j
  let c := S.atlas.chart i
  have hk := fun k => hcoord j k ⟨x, hx.1⟩ i hx.2
  choose N hN hxN G hG hNG using hk
  let N' := (⋂ k, N k) ∩ f ⁻¹' d.dom
  have hN' : IsOpen N' := (isOpen_iInter_of_finite hN).inter (d.isOpen_dom.preimage hf)
  obtain ⟨O, hO, hON⟩ := anb_exists_open_trace c hN'
  let G' : (Fin c.n → ℂ) → (Fin d.n → ℂ) := fun z k => G k z
  have hG' : AnalyticAt ℂ G' (c.toFun x) := analyticAt_pi_iff.mpr hG
  refine ⟨O ∩ {w | AnalyticAt ℂ G' w}, hO.inter (isOpen_analyticAt ℂ G'),
    ⟨(hON x hx.2).mpr ⟨mem_iInter.mpr hxN, hx.1⟩, hG'⟩, G',
    fun w hw => hw.2, fun y hy hyW => ?_⟩
  have hyN := (hON y hy.2).mp hyW.1
  funext k
  exact hNG k ⟨y, hy.1⟩ ⟨mem_iInter.mp hyN.1 k, hy.2⟩

/-- Holomorphicity on an open subspace is ambient holomorphicity for any
function whose domain is contained in that open subspace. -/
theorem a3b4a_classHolomorphic_of_openSpace
    {M : Type} [TopologicalSpace M] (S : an_ReducedSpace M)
    {O V : Set M} (hO : IsOpen O) (hVO : V ⊆ O) (g : V → ℂ)
    (hg : (anrem_openSpace S hO).IsHolFun
      (fun y : (Subtype.val ⁻¹' V : Set O) => g ⟨y.1.1, y.2⟩)) :
    S.IsHolFun g := by
  intro y i hy
  obtain ⟨N, hN, hyN, G, hG, hEq⟩ :=
    hg ⟨⟨y.1, hVO y.2⟩, y.2⟩ i hy
  refine ⟨Subtype.val '' N, hO.isOpenMap_subtype_val N hN, ⟨_, hyN, rfl⟩, G, hG, ?_⟩
  intro z hz
  obtain ⟨w, hwN, hwz⟩ := hz.1
  have hw : (⟨z.1, hVO z.2⟩ : O) = w := Subtype.ext hwz.symm
  exact hEq ⟨⟨z.1, hVO z.2⟩, z.2⟩ ⟨hw.symm ▸ hwN, hz.2⟩

end HodgeLean.Adapters
