import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Calculus.ImplicitFunction.ProdDomain
import Mathlib.Topology.IsLocalHomeomorph
import Mathlib.Topology.Constructions

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open Topology Filter
namespace HodgeLean.Foundations.Program

/-- A local inverse chart pulls back to an arbitrary continuous base.
Source: Mathlib, OpenPartialHomeomorph source and target homeomorphisms. -/
def s2e_c11_pullbackLocalChart
    {E B A : Type*} [TopologicalSpace E] [TopologicalSpace B] [TopologicalSpace A]
    (e : OpenPartialHomeomorph E B) (g : A → B) (hg : Continuous g) :
    {p : {p : A × E // g p.1 = e p.2} // p.1.2 ∈ e.source} ≃ₜ
      {a : A // g a ∈ e.target} where
  toFun p := ⟨p.1.1.1, by rw [p.1.2]; exact e.map_source p.2⟩
  invFun a := ⟨⟨(a.1, e.symm (g a.1)), (e.right_inv a.2).symm⟩, e.map_target a.2⟩
  left_inv p := by
    apply Subtype.ext
    apply Subtype.ext
    change (p.1.1.1, e.symm (g p.1.1.1)) = p.1.1
    apply Prod.ext
    · rfl
    change e.symm (g p.1.1.1) = p.1.1.2
    rw [p.1.2, e.left_inv p.2]
  right_inv a := by apply Subtype.ext; rfl
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact continuous_fst.comp (continuous_subtype_val.comp continuous_subtype_val)
  continuous_invFun := by
    apply Continuous.subtype_mk
    apply Continuous.subtype_mk
    apply continuous_subtype_val.prodMk
    exact e.continuousOn_invFun.comp_continuous
      (hg.comp continuous_subtype_val) (fun a => a.2)

/-- Local homeomorphisms remain local homeomorphisms after arbitrary continuous base change.
Source: Mathlib, open local charts and continuity under base change. -/
theorem s2e_c11_localHomeomorph_baseChange
    {E B A : Type*} [TopologicalSpace E] [TopologicalSpace B] [TopologicalSpace A]
    (f : E → B) (hf : IsLocalHomeomorph f) (g : A → B) (hg : Continuous g) :
    IsLocalHomeomorph (fun p : {p : A × E // g p.1 = f p.2} => p.1.1) := by
  apply isLocalHomeomorph_iff_isOpenEmbedding_restrict.mpr
  intro p
  obtain ⟨e, hx, he⟩ := hf p.1.2
  subst f
  let U : Set {p : A × E // g p.1 = e p.2} := {p | p.1.2 ∈ e.source}
  have hU : IsOpen U := e.open_source.preimage (continuous_snd.comp continuous_subtype_val)
  refine ⟨U, hU.mem_nhds hx, ?_⟩
  have hV : IsOpen {a : A | g a ∈ e.target} := e.open_target.preimage hg
  exact hV.isOpenEmbedding_subtypeVal.comp (s2e_c11_pullbackLocalChart e g hg).isOpenEmbedding

/-- The local-on-a-set version of continuous base change.
Source: Mathlib, IsLocalHomeomorphOn and open local inverse charts. -/
theorem s2e_c11_localHomeomorphOn_baseChange
    {E B A : Type*} [TopologicalSpace E] [TopologicalSpace B] [TopologicalSpace A]
    (f : E → B) (S : Set E) (hf : IsLocalHomeomorphOn f S)
    (g : A → B) (hg : Continuous g) :
    IsLocalHomeomorphOn (fun p : {p : A × E // g p.1 = f p.2} => p.1.1)
      {p | p.1.2 ∈ S} := by
  apply (isLocalHomeomorphOn_iff_isOpenEmbedding_restrict _).mpr
  intro p hp
  obtain ⟨e, hx, he⟩ := hf p.1.2 hp
  subst f
  let U : Set {p : A × E // g p.1 = e p.2} := {p | p.1.2 ∈ e.source}
  have hU : IsOpen U := e.open_source.preimage (continuous_snd.comp continuous_subtype_val)
  refine ⟨U, hU.mem_nhds hx, ?_⟩
  have hV : IsOpen {a : A | g a ∈ e.target} := e.open_target.preimage hg
  exact hV.isOpenEmbedding_subtypeVal.comp (s2e_c11_pullbackLocalChart e g hg).isOpenEmbedding

/-- A zero locus is the pullback of its graph-coordinate map along the zero section.
Source: Mathlib, subtype product topology and the graph construction. -/
def s2e_c11_levelPullbackHomeomorph
    {V W : Type*} [TopologicalSpace V] [TopologicalSpace W] [Zero W]
    (F : V × W → W) :
    {p : V × (V × W) // (0, p.1) = (F p.2, p.2.1)} ≃ₜ
      {z : V × W // F z = 0} where
  toFun p := ⟨p.1.2, (congrArg Prod.fst p.2).symm⟩
  invFun z := ⟨(z.1.1, z.1), by
    apply Prod.ext
    · exact z.2.symm
    · rfl⟩
  left_inv p := by
    apply Subtype.ext
    change (p.1.2.1, p.1.2) = p.1
    apply Prod.ext
    · exact (congrArg Prod.snd p.2).symm
    · rfl
  right_inv z := by apply Subtype.ext; rfl
  continuous_toFun := continuous_snd.comp continuous_subtype_val |>.subtype_mk _
  continuous_invFun := by
    apply Continuous.subtype_mk
    exact (continuous_fst.comp continuous_subtype_val).prodMk continuous_subtype_val

/-- Ambient inverse charts yield local inverse charts for projection from the zero locus.
Source: Mathlib, open local charts and continuous base change along the zero section. -/
theorem s2e_c11_level_projection_of_local_charts
    {V W : Type*} [TopologicalSpace V] [TopologicalSpace W] [Zero W]
    (F : V × W → W) (S : Set {z : V × W // F z = 0})
    (hchart : ∀ z ∈ S, ∃ e : OpenPartialHomeomorph (V × W) (W × V),
      z.1 ∈ e.source ∧ (fun w => (F w, w.1)) = e) :
    IsLocalHomeomorphOn (fun z : {z : V × W // F z = 0} => z.1.1) S := by
  intro z hz
  obtain ⟨e, hez, he⟩ := hchart z hz
  let h := s2e_c11_levelPullbackHomeomorph F
  have he' : IsLocalHomeomorphOn (fun w => (F w, w.1)) e.source := by
    rw [he]
    exact IsLocalHomeomorphOn.OpenPartialHomeomorph.isLocalHomeomorphOn e
  have hp := s2e_c11_localHomeomorphOn_baseChange _ _ he'
    (fun v : V => ((0 : W), v)) (continuous_const.prodMk continuous_id)
  have hp' : IsLocalHomeomorphOn
      ((fun z : {z : V × W // F z = 0} => z.1.1) ∘ h)
      {p | p.1.2 ∈ e.source} := by
    convert hp using 1
    funext p
    exact (congrArg Prod.snd p.2).symm
  have ht := hp'.of_comp_right h.isLocalHomeomorph.isLocalHomeomorphOn
  exact ht z ⟨h.symm z, hez, h.apply_symm_apply z⟩

/-- The implicit-function theorem makes zero-locus projection locally invertible at regular roots.
Source: Mathlib, HasStrictFDerivAt.implicitFunctionDataOfProdDomain. -/
theorem s2e_c11_implicit_zero_projection
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V]
    (F : V × ℂ → ℂ) (S : Set {z : V × ℂ // F z = 0})
    (hderiv : ∀ z ∈ S, ∃ D : V × ℂ →L[ℂ] ℂ,
      HasStrictFDerivAt F D z.1 ∧
        (D ∘L ContinuousLinearMap.inr ℂ V ℂ).IsInvertible) :
    IsLocalHomeomorphOn (fun z : {z : V × ℂ // F z = 0} => z.1.1) S := by
  apply s2e_c11_level_projection_of_local_charts F S
  intro z hz
  obtain ⟨D, hD, hI⟩ := hderiv z hz
  let φ := hD.implicitFunctionDataOfProdDomain hI
  refine ⟨φ.toOpenPartialHomeomorph, φ.pt_mem_toOpenPartialHomeomorph_source, ?_⟩
  funext w
  exact (φ.toOpenPartialHomeomorph_apply w).symm

/-- Restricting a local homeomorphism on an open set gives a local homeomorphism on that subtype.
Source: Mathlib, IsLocalHomeomorphOn.comp and open subtype embeddings. -/
theorem s2e_c11_localHomeomorphOn_open_restrict
    {E B : Type*} [TopologicalSpace E] [TopologicalSpace B]
    (f : E → B) (S : Set E) (hS : IsOpen S) (hf : IsLocalHomeomorphOn f S) :
    IsLocalHomeomorph (S.domRestrict f) := by
  apply isLocalHomeomorph_iff_isLocalHomeomorphOn_univ.mpr
  exact hf.comp hS.isOpenEmbedding_subtypeVal.isLocalHomeomorph.isLocalHomeomorphOn
    (fun x _ => x.2)

end HodgeLean.Foundations.Program
