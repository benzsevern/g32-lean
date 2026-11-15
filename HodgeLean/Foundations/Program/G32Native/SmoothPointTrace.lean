import HodgeLean.Foundations.Program.SchoenTransferQ3PointNormalOrientation
import HodgeLean.Foundations.QuotientDuality.LocalTrace
import HodgeLean.Adapters.NormalConeB4aClassRestriction

/-! Evaluation of the actual point-supported class against a retained orientation. -/
noncomputable section
set_option maxHeartbeats 400000
open CategoryTheory TopologicalSpace AlgebraicTopology.Singular
open HodgeLean.Adapters HodgeLean.Foundations.QuotientDuality
namespace HodgeLean.Foundations.Program.G32Native

/-- A chart flattening a singleton has no tangential coordinate. -/
theorem singleton_chart_tangent_dimension
    {M : Type} [TopologicalSpace M] (r d : ℕ)
    (e : OpenPartialHomeomorph M ((Fin r → ℂ) × (Fin d → ℂ)))
    (x : M) (hx : x ∈ e.source)
    (hflat : ∀ y ∈ e.source, y ∈ ({x} : Set M) ↔ (e y).2 = 0) : r = 0 := by
  have h0 : (e x).2 = 0 := (hflat x hx).mp (Set.mem_singleton x)
  let H := flattenedSupportHomeomorph (Fin r → ℂ) d e x hx
  have hconst (a : Fin r → ℂ) : (H (a, 0) : M) = x :=
    Set.mem_singleton_iff.mp ((flattenedSupportHomeomorph_mem_support_iff
      (Fin r → ℂ) d e x hx {x} hflat h0 (a, 0)).mpr rfl)
  have h10 : (fun _ : Fin r => (1 : ℂ)) = 0 := by
    have hh : H ((fun _ : Fin r => (1 : ℂ)), 0) = H (0, 0) :=
      Subtype.ext ((hconst _).trans (hconst _).symm)
    exact congrArg Prod.fst (H.injective hh)
  by_contra hr
  have hh := congrFun h10 ⟨0, Nat.pos_of_ne_zero hr⟩
  exact one_ne_zero hh

#print axioms singleton_chart_tangent_dimension
end HodgeLean.Foundations.Program.G32Native
