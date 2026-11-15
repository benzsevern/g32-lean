import Mathlib.Topology.VectorBundle.Basic
import Mathlib.Topology.OpenPartialHomeomorph.Constructions
import Mathlib.Analysis.Complex.Basic

/-! # Detecting the original zero vectors in complex linear frames

The coordinate equation refers to the retained fibre element.
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
open Bundle
namespace HodgeLean.Foundations.TubularEuler

theorem linearFrame_zero_iff
    {B : Type*} [TopologicalSpace B] (k : ℕ) (E : B → Type*)
    [∀ x, AddCommGroup (E x)] [∀ x, Module ℂ (E x)]
    [TopologicalSpace (TotalSpace (Fin k → ℂ) E)]
    (e : Trivialization (Fin k → ℂ) (π (Fin k → ℂ) E)) [e.IsLinear ℂ]
    (z : TotalSpace (Fin k → ℂ) E) (hz : z ∈ e.source) :
    (e z).2 = 0 ↔ z.2 = 0 := by
  exact (e.linearEquivAt ℂ z.proj (e.mem_source.mp hz)).map_eq_zero_iff

theorem linearFrame_product_zero_coordinates
    {B : Type*} [TopologicalSpace B] (k : ℕ) (E : B → Type*)
    [∀ x, AddCommGroup (E x)] [∀ x, Module ℂ (E x)]
    [TopologicalSpace (TotalSpace (Fin k → ℂ) E)]
    (e : Trivialization (Fin k → ℂ) (π (Fin k → ℂ) E)) [e.IsLinear ℂ]
    (b : OpenPartialHomeomorph B (Fin k → ℂ))
    (z : TotalSpace (Fin k → ℂ) E) (hz : z ∈ e.source) :
    let P := e.toOpenPartialHomeomorph.trans
      (b.prod (OpenPartialHomeomorph.refl (Fin k → ℂ)))
    P (zeroSection (Fin k → ℂ) E z.proj) = ((P z).1, (0 : Fin k → ℂ)) := by
  have hb : z.proj ∈ e.baseSet := e.mem_source.mp hz
  have he0 : e (zeroSection (Fin k → ℂ) E z.proj) = (z.proj, 0) := by
    apply Prod.ext
    · exact e.coe_fst' hb
    · exact (e.linearEquivAt ℂ z.proj hb).map_zero
  change (b.prod (OpenPartialHomeomorph.refl (Fin k → ℂ)))
    (e (zeroSection (Fin k → ℂ) E z.proj)) =
      (((b.prod (OpenPartialHomeomorph.refl (Fin k → ℂ))) (e z)).1, 0)
  rw [he0]
  change (b z.proj, (0 : Fin k → ℂ)) = (b (e z).1, 0)
  rw [e.coe_fst' hb]

theorem linearFrame_zeroSection
    {B : Type*} [TopologicalSpace B] (k : ℕ) (E : B → Type*)
    [∀ y, AddCommGroup (E y)] [∀ y, Module ℂ (E y)]
    [TopologicalSpace (TotalSpace (Fin k → ℂ) E)]
    (e : Trivialization (Fin k → ℂ) (π (Fin k → ℂ) E)) [e.IsLinear ℂ]
    (y : B) (hy : y ∈ e.baseSet) :
    e (zeroSection (Fin k → ℂ) E y) = (y, (0 : Fin k → ℂ)) := by
  apply Prod.ext
  · exact e.coe_fst' hy
  · exact (e.linearEquivAt ℂ y hy).map_zero

#print axioms linearFrame_zeroSection

#print axioms linearFrame_zero_iff
#print axioms linearFrame_product_zero_coordinates

end HodgeLean.Foundations.TubularEuler
