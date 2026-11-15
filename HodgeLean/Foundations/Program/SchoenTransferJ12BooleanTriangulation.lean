import HodgeLean.Foundations.RationalHomologyManifold.Defs
import HodgeLean.Foundations.Semialgebraic.CompatibleTriangulation

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory
open HodgeLean.Foundations.RationalHomologyManifold
namespace HodgeLean.Foundations.Program

/-- Compact Boolean realizations supply finite triangulations of their actual homeomorphic spaces.
Source: Coste, An Introduction to Semialgebraic Geometry (2002), Theorem 4.4. -/
theorem s4_selected_boolean_finite_triangulation
    (X : TopCat.{0}) [CompactSpace X] (N : ℕ) (f : s2v_t11b_Formula N)
    (h : X ≃ₜ f.realize) : Nonempty (FiniteTriangulation X) := by
  let : CompactSpace f.realize := h.compactSpace
  have hf : IsCompact f.realize := isCompact_iff_compactSpace.mpr inferInstance
  obtain ⟨K, hK, e, _, _⟩ :=
    Semialgebraic.CompatibleTriangulation.compact_compatible_triangulation N f hf
      (Fin.elim0 : Fin 0 → s2v_t11b_Formula N)
  exact ⟨⟨N, K, hK, e.trans h.symm⟩⟩

end HodgeLean.Foundations.Program
