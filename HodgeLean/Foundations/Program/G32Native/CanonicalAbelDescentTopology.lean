import HodgeLean.Foundations.Program.G32Native.CanonicalAbelDescent

/-! # Continuity of the retained symmetric Abel sum -/
noncomputable section
set_option maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open HodgeLean.Adapters HodgeLean.Foundations.Curves.AbelAdapter
open HodgeLean.Foundations.Curves.AbelAdapter.StageTwo
open scoped BigOperators Topology
namespace HodgeLean.Foundations.Program.G32Native

/-- A symmetric sum of continuous functions descends continuously on the retained quotient. -/
theorem canonicalDescendedSum_continuous (G : CanonicalAbelGeometry)
    {A : Type*} [AddCommMonoid A] [TopologicalSpace A] [ContinuousAdd A]
    (f : ComplexPoint G.Z → A) (hf : Continuous f) :
    Continuous (canonicalDescendedSum G f) := by
  have hq := Topology.IsQuotientMap.of_surjective_continuous G.surjectiveγ
    (Point.continuous_map G.γ)
  apply hq.continuous_iff.mpr
  have he : canonicalDescendedSum G f ∘ Point.map G.γ =
      fun u : ComplexPoint (g3_power G.Z (2 * G.k)) =>
        ∑ i, f (Point.map (g3_proj G.Z (2 * G.k) i) u) := by
    funext u
    have h := canonicalDescendedSum_tuple G f
      (fun i => Point.map (g3_proj G.Z (2 * G.k) i) u)
    change canonicalDescendedSum G f (Point.map G.γ
      (s2_lift (2 * G.k) (fun i => u ≫ g3_proj G.Z (2 * G.k) i))) = _ at h
    rw [s2e_lift_coordinates] at h
    exact h
  rw [he]
  exact continuous_finset_sum _ (fun i _ => hf.comp (Point.continuous_map _))

/-- Continuity holds on the full symmetric product, also along its collision locus. -/
theorem canonicalSymmetricAbel_continuous (G : CanonicalAbelGeometry)
    (p : ComplexPoint G.Z) : Continuous (canonicalSymmetricAbel G p) := by
  letI := b3_periodLattice_finite (C := ComplexPoint G.Z)
    (Module.finrank_fin_fun (n := 1) ℂ)
  letI := b3_periodLattice_free (E := Fin 1 → ℂ) (C := ComplexPoint G.Z)
  letI := b2_latticeMap_discrete _ (b3_isWeightOne (C := ComplexPoint G.Z)
    (Module.finrank_fin_fun (n := 1) ℂ))
  exact canonicalDescendedSum_continuous G _
    (analyticAbel_continuous (Module.finrank_fin_fun (n := 1) ℂ) p)

#print axioms canonicalDescendedSum_continuous
#print axioms canonicalSymmetricAbel_continuous
end HodgeLean.Foundations.Program.G32Native
