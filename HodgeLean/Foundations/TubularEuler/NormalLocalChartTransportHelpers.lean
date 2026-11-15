import HodgeLean.Foundations.TubularEuler.LocalInverseChartTransportHelpers
import HodgeLean.Foundations.TubularEuler.LinearFrameZeroHelpers

/-! # Actual bundle-coordinate transport of analytic normal inverses

The original linear frame, bundle projection, and ambient chart determine the transported map.
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
open Bundle Topology
namespace HodgeLean.Foundations.TubularEuler

theorem normal_local_inverse_chart_transport
    {B X : Type*} [TopologicalSpace B] [TopologicalSpace X]
    (k : ℕ) (E : B → Type*) [∀ x, AddCommGroup (E x)] [∀ x, Module ℂ (E x)]
    [TopologicalSpace (TotalSpace (Fin k → ℂ) E)]
    (e : Trivialization (Fin k → ℂ) (π (Fin k → ℂ) E)) [e.IsLinear ℂ]
    (b : OpenPartialHomeomorph B (Fin k → ℂ))
    (a : OpenPartialHomeomorph X ((Fin k → ℂ) × (Fin k → ℂ)))
    (c : OpenPartialHomeomorph ((Fin k → ℂ) × (Fin k → ℂ))
      ((Fin k → ℂ) × (Fin k → ℂ)))
    (hP : c.source ⊆ (e.toOpenPartialHomeomorph.trans
      (b.prod (OpenPartialHomeomorph.refl (Fin k → ℂ)))).target)
    (ha : c.target ⊆ a.target)
    (hzero : ∀ q ∈ c.source, (q.1, (0 : Fin k → ℂ)) ∈ c.source)
    (hsupp : ∀ q ∈ c.source, (c q).2 = 0 ↔ q.2 = 0)
    (hcf : ContDiffOn ℝ ⊤ c c.source) (hcg : ContDiffOn ℝ ⊤ c.symm c.target)
    (hder : ∀ q ∈ c.source, ∃ A : (Fin k → ℂ) ≃L[ℂ] (Fin k → ℂ),
      HasFDerivAt (fun w : Fin k → ℂ => (c (q.1, w)).2) A.toContinuousLinearMap 0)
    (S : Set X) (hS : ∀ y ∈ a.source, y ∈ S ↔ (a y).2 = 0) :
    let P := e.toOpenPartialHomeomorph.trans
      (b.prod (OpenPartialHomeomorph.refl (Fin k → ℂ)))
    let L := (P.trans c).trans a.symm
    ∀ z ∈ L.source,
      z.proj ∈ b.source ∧ z ∈ e.source ∧ L z ∈ a.source ∧
      zeroSection (Fin k → ℂ) E z.proj ∈ L.source ∧
      (L z ∈ S ↔ z.2 = 0) ∧
      let C := (P.symm.trans L).trans a
      (b z.proj, (0 : Fin k → ℂ)) ∈ C.source ∧
      ContDiffOn ℝ ⊤ C C.source ∧ ContDiffOn ℝ ⊤ C.symm C.target ∧
      ∃ A : (Fin k → ℂ) ≃L[ℂ] (Fin k → ℂ),
        HasFDerivAt (fun w : Fin k → ℂ => (C (b z.proj, w)).2)
          A.toContinuousLinearMap 0 := by
  let P := e.toOpenPartialHomeomorph.trans
    (b.prod (OpenPartialHomeomorph.refl (Fin k → ℂ)))
  let L := (P.trans c).trans a.symm
  let C := (P.symm.trans L).trans a
  obtain ⟨hCsource, hEq⟩ := partialHomeomorph_transported_coordinates P a c hP ha
  have hcompat : Set.EqOn C c C.source := by
    intro q hq
    exact hEq (hCsource ▸ hq)
  have hsub : C.source ⊆ c.source := by
    rw [hCsource]
  obtain ⟨hCf, hCg⟩ := partialHomeomorph_contDiffOn_of_compatible C c hsub hcompat hcf hcg
  dsimp only
  intro z hz
  have hzP : z ∈ P.source := hz.1.1
  have hzc : P z ∈ c.source := hz.1.2
  have hze : z ∈ e.source := hzP.1
  have hb : z.proj ∈ e.baseSet := e.mem_source.mp hze
  have hfst : (P z).1 = b z.proj := congrArg b (e.coe_fst' hb)
  have hzb : z.proj ∈ b.source := by
    have h := hzP.2.1
    change (e z).1 ∈ b.source at h
    rwa [e.coe_fst' hb] at h
  have hza : L z ∈ a.source := a.map_target hz.2
  have hcz : (b z.proj, (0 : Fin k → ℂ)) ∈ C.source := by
    rw [hCsource]
    have h := hzero (P z) hzc
    rwa [hfst] at h
  have hz0P : zeroSection (Fin k → ℂ) E z.proj ∈ P.source := by
    have he0 : zeroSection (Fin k → ℂ) E z.proj ∈ e.source := e.mem_source.mpr hb
    refine ⟨he0, ?_⟩
    change (e (zeroSection (Fin k → ℂ) E z.proj)).1 ∈ b.source ∧
      (e (zeroSection (Fin k → ℂ) E z.proj)).2 ∈ Set.univ
    rw [e.coe_fst' (x := zeroSection (Fin k → ℂ) E z.proj) hb]
    exact ⟨hzb, Set.mem_univ _⟩
  have hz0 : zeroSection (Fin k → ℂ) E z.proj ∈ L.source := by
    have h : P.symm (b z.proj, (0 : Fin k → ℂ)) ∈ L.source := hcz.1.2
    have hP0 := linearFrame_product_zero_coordinates k E e b z hze
    change P (zeroSection (Fin k → ℂ) E z.proj) = ((P z).1, 0) at hP0
    rw [hfst] at hP0
    rw [← hP0, P.left_inv hz0P] at h
    exact h
  have hs : L z ∈ S ↔ z.2 = 0 := by
    have hval : a (L z) = c (P z) := a.right_inv hz.2
    calc
      L z ∈ S ↔ (a (L z)).2 = 0 := hS (L z) hza
      _ ↔ (c (P z)).2 = 0 := by rw [hval]
      _ ↔ (P z).2 = 0 := hsupp (P z) hzc
      _ ↔ z.2 = 0 := linearFrame_zero_iff k E e z hze
  obtain ⟨A, hA⟩ := hder (P z) hzc
  rw [hfst] at hA
  exact ⟨hzb, hze, hza, hz0, hs, hcz, hCf, hCg, A,
    partialHomeomorph_fibre_derivative_of_compatible C c hcompat (b z.proj) hcz
      A.toContinuousLinearMap hA⟩

#print axioms normal_local_inverse_chart_transport

end HodgeLean.Foundations.TubularEuler
