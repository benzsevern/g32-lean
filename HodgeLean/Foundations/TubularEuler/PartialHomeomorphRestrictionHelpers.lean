import Mathlib.Topology.OpenPartialHomeomorph.Constructions
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Complex.Basic

/-! # Compatible restrictions of partial homeomorphisms

Forward agreement on the smaller source determines inverse agreement on its target.
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
open Topology
namespace HodgeLean.Foundations.TubularEuler

theorem partialHomeomorph_target_subset_and_inverse_eq {X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y]
    (e e' : OpenPartialHomeomorph X Y) (hs : e.source ⊆ e'.source)
    (he : Set.EqOn e e' e.source) :
    e.target ⊆ e'.target ∧ Set.EqOn e.symm e'.symm e.target := by
  constructor
  · intro y hy
    have hx := e.map_target hy
    have ht := e'.map_source (hs hx)
    rw [← he hx, e.right_inv hy] at ht
    exact ht
  · intro y hy
    have hx := e.map_target hy
    calc
      e.symm y = e'.symm (e' (e.symm y)) := (e'.left_inv (hs hx)).symm
      _ = e'.symm y := by rw [← he hx, e.right_inv hy]

theorem partialHomeomorph_contDiffOn_of_compatible
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (e e' : OpenPartialHomeomorph E F) (hs : e.source ⊆ e'.source)
    (he : Set.EqOn e e' e.source)
    (hf : ContDiffOn ℝ ⊤ e' e'.source) (hg : ContDiffOn ℝ ⊤ e'.symm e'.target) :
    ContDiffOn ℝ ⊤ e e.source ∧ ContDiffOn ℝ ⊤ e.symm e.target := by
  obtain ⟨ht, hi⟩ := partialHomeomorph_target_subset_and_inverse_eq e e' hs he
  exact ⟨(hf.mono hs).congr (fun x hx => he hx),
    (hg.mono ht).congr (fun y hy => hi hy)⟩

theorem partialHomeomorph_fibre_derivative_of_compatible
    {B E F : Type*} [TopologicalSpace B]
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F]
    (e e' : OpenPartialHomeomorph (B × E) (B × F))
    (he : Set.EqOn e e' e.source) (b : B) (hb : (b, (0 : E)) ∈ e.source)
    (A : E →L[ℂ] F) (hA : HasFDerivAt (fun w : E => (e' (b, w)).2) A 0) :
    HasFDerivAt (fun w : E => (e (b, w)).2) A 0 := by
  apply hA.congr_of_eventuallyEq
  have hc : Continuous (fun w : E => (b, w)) := continuous_const.prodMk continuous_id
  filter_upwards [hc.continuousAt.eventually (e.open_source.mem_nhds hb)] with w hw
  exact congrArg Prod.snd (he hw)

#print axioms partialHomeomorph_fibre_derivative_of_compatible
#print axioms partialHomeomorph_contDiffOn_of_compatible
#print axioms partialHomeomorph_target_subset_and_inverse_eq

end HodgeLean.Foundations.TubularEuler
