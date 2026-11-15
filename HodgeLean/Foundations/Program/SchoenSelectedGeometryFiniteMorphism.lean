import HodgeLean.Foundations.Program.SchoenSelectedGeometryIntegralModel
import HodgeLean.Foundations.Mathlib.ZmtIso

noncomputable section
set_option maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry Set Topology
namespace HodgeLean.Foundations.Program

/-- A proper morphism with finite closed-point fibres over a field is finite.
Source: the Jacobson property, openness of the quasi-finite locus, and proper quasi-finite finiteness. -/
theorem s0_finite_of_finite_closed_fibers
    {k : Type} [Field k] {Z X : Scheme.{0}}
    (sZ : Z ⟶ Spec (.of k)) (sX : X ⟶ Spec (.of k))
    (f : Z ⟶ X) [IsProper f] [LocallyOfFiniteType sZ] [LocallyOfFiniteType sX]
    (hfib : ∀ x : X, IsClosed ({x} : Set X) →
      (f ⁻¹' {x} ∩ closedPoints Z).Finite) : IsFinite f := by
  letI : JacobsonSpace Z := LocallyOfFiniteType.jacobsonSpace sZ
  letI : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace sX
  have hfin (x : X) (hx : IsClosed ({x} : Set X)) : (f ⁻¹' {x}).Finite := by
    have hs : IsClosed (f ⁻¹' {x}) := hx.preimage f.continuous
    have ht : IsClosed (f ⁻¹' {x} ∩ closedPoints Z) := by
      rw [← Set.biUnion_of_singleton (f ⁻¹' {x} ∩ closedPoints Z)]
      exact (hfib x hx).isClosed_biUnion (fun z hz ↦ hz.2)
    have he := closure_inter_closedPoints hs
    rw [ht.closure_eq] at he
    rw [← he]
    exact hfib x hx
  have hqf (z : Z) (hz : IsClosed ({f z} : Set X)) : f.QuasiFiniteAt z := by
    letI : Finite (f ⁻¹' {f z}) := (hfin _ hz).to_subtype
    letI : Finite (f.fiber (f z)) := (f.fiberHomeo (f z)).finite_iff.mpr inferInstance
    exact Scheme.Hom.quasiFiniteAt_iff_isOpen_singleton_asFiber.mpr (isOpen_discrete _)
  haveI : LocallyQuasiFinite f := by
    rw [← Scheme.Hom.quasiFiniteLocus_eq_top_iff, eq_top_iff]
    intro z _
    by_contra hz
    have hc : IsClosed (f '' (f.quasiFiniteLocus : Set Z)ᶜ) :=
      f.isClosedMap _ f.quasiFiniteLocus.isOpen.isClosed_compl
    obtain ⟨_, ⟨c, hc', rfl⟩, hcl⟩ :=
      nonempty_inter_closedPoints (Set.Nonempty.image f ⟨z, hz⟩) hc.isLocallyClosed
    exact hc' (hqf c hcl)
  exact IsFinite.of_isProper_of_locallyQuasiFinite f

#print axioms s0_finite_of_finite_closed_fibers
end HodgeLean.Foundations.Program
