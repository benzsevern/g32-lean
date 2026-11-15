import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Complex.Basic
import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.Topology.Algebra.OpenSubgroup

noncomputable section
open Filter
open scoped Topology BigOperators
namespace HodgeLean.Foundations.Curves.AbelAdapter.StageFour

theorem open_subgroup_of_local_curves {W T : Type*}
    [NormedAddCommGroup W] [NormedSpace ℂ W] [CompleteSpace W]
    [AddCommGroup T] [TopologicalSpace T] [IsTopologicalAddGroup T]
    {n : ℕ} (b : Module.Basis (Fin n) ℂ W) (c : W →+ T) (hc : IsOpenMap c)
    (g : Fin n → ℂ → W) (hg : ∀ i, HasStrictDerivAt (g i) (b i) 0)
    (hg0 : ∀ i, g i 0 = 0) (S : AddSubgroup T)
    (hmem : ∀ i, ∀ᶠ z in 𝓝 (0 : ℂ), c (g i z) ∈ S) : IsOpen (S : Set T) := by
  classical
  let H : (Fin n → ℂ) → W := fun z ↦ ∑ i, g i (z i)
  let D : (Fin n → ℂ) →L[ℂ] W :=
    ∑ i, (ContinuousLinearMap.proj i : (Fin n → ℂ) →L[ℂ] ℂ).smulRight (b i)
  have hDi (i : Fin n) : HasStrictFDerivAt (fun z : Fin n → ℂ ↦ g i (z i))
      ((ContinuousLinearMap.proj i : (Fin n → ℂ) →L[ℂ] ℂ).smulRight (b i)) 0 := by
    exact ((hg i).hasStrictFDerivAt.comp (0 : Fin n → ℂ)
      (hasStrictFDerivAt_apply (𝕜 := ℂ) i (0 : Fin n → ℂ))).congr_fderiv
      (by ext z; rfl)
  have hD : HasStrictFDerivAt H D 0 := by
    have hs := HasStrictFDerivAt.sum (u := Finset.univ) (fun i _ ↦ hDi i)
    have heq : (∑ i, fun z : Fin n → ℂ ↦ g i (z i)) = H := by
      funext z
      simp only [H, Finset.sum_apply]
    exact heq ▸ hs
  have hsurj : Function.Surjective D := by
    intro w
    refine ⟨fun i ↦ b.repr w i, ?_⟩
    simp only [D, ContinuousLinearMap.sum_apply, ContinuousLinearMap.smulRight_apply,
      ContinuousLinearMap.proj_apply]
    exact b.sum_repr w
  have hH0 : H 0 = 0 := by simp only [H, Pi.zero_apply, hg0, Finset.sum_const_zero]
  have hparam (i : Fin n) : ∀ᶠ z : Fin n → ℂ in 𝓝 0, c (g i (z i)) ∈ S := by
    have ht : Tendsto (fun z : Fin n → ℂ ↦ z i) (𝓝 (0 : Fin n → ℂ)) (𝓝 (0 : ℂ)) :=
      (continuous_apply i).continuousAt
    exact ht.eventually (hmem i)
  have hnear : ∀ᶠ z in 𝓝 (0 : Fin n → ℂ), c (H z) ∈ S := by
    filter_upwards [Filter.eventually_all.mpr hparam] with z hz
    change c (∑ i, g i (z i)) ∈ S
    rw [map_sum]
    exact S.sum_mem fun i _ ↦ hz i
  have hpre : {w : W | c w ∈ S} ∈ 𝓝 (0 : W) := by
    have hmap := hD.map_nhds_eq_of_surj (LinearMap.range_eq_top.mpr hsurj)
    rw [hH0] at hmap
    rw [← hmap]
    exact hnear
  have himage := hc.image_mem_nhds hpre
  rw [map_zero] at himage
  apply S.isOpen_of_mem_nhds
  exact Filter.mem_of_superset himage (by rintro _ ⟨w, hw, rfl⟩; exact hw)

end HodgeLean.Foundations.Curves.AbelAdapter.StageFour
