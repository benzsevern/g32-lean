import HodgeLean.Foundations.Program.G32Native.BlowupRatioLinearMap
import HodgeLean.Foundations.Program.G32Native.IdealGeneratorSpan

/-! Finite generators of affine blow-up chart algebras. -/
noncomputable section
set_option maxHeartbeats 400000
open AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- Ratios of a generating family generate the entire affine blow-up chart algebra. -/
theorem g32l4_blowUp_ratios_adjoin_top {R K : Type} [CommRing R]
    (I : Ideal R) (a : I) (g : K → I)
    (hg : Ideal.span (Set.range (fun k => (g k : R))) = I) :
    Algebra.adjoin R (Set.range (fun k => affineBlowUpAlgebra.ratio I a (g k))) = ⊤ := by
  let S := Algebra.adjoin R (Set.range (fun k => affineBlowUpAlgebra.ratio I a (g k)))
  have hle : Submodule.span R (Set.range g) ≤
      S.toSubmodule.comap (g32l4_blowUp_ratioLinearMap I a) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨k, rfl⟩
    exact Algebra.subset_adjoin (Set.mem_range_self k)
  rw [g32l4_ideal_generators_span_top I g hg] at hle
  have hratio (b : I) : affineBlowUpAlgebra.ratio I a b ∈ S := hle (by trivial)
  apply top_unique
  intro x _
  refine Algebra.adjoin_induction
    (p := fun y hy => (⟨y, hy⟩ : affineBlowUpAlgebra I a) ∈ S) ?_ ?_ ?_ ?_ x.property
  · rintro _ ⟨b, hb, rfl⟩
    simpa only [affineBlowUpAlgebra.ratio, awayFrac_one] using hratio ⟨b, hb⟩
  · intro r
    exact S.algebraMap_mem r
  · intro y z hy hz hy' hz'
    exact S.add_mem hy' hz'
  · intro y z hy hz hy' hz'
    exact S.mul_mem hy' hz'

end HodgeLean.Foundations.Program
