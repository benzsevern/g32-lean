import HodgeLean.Ported.NYLL.SchemeTheory.Modules.Invertible.Invertible

/-! # Invertibility under specified native module isomorphisms -/
noncomputable section
set_option maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program.G32Native
open Scheme.Modules

/-- A specified native isomorphism transports each original unit trivialization. -/
theorem paired_c3_invertible_of_iso {X : Scheme.{0}} {M N : X.Modules}
    (e : M ≅ N) (hN : IsInvertible N) : IsInvertible M := by
  refine ⟨fun x => ?_⟩
  obtain ⟨U, hx, ⟨b⟩⟩ := hN.exists_trivialization x
  exact ⟨U, hx, ⟨(Scheme.Modules.pullback U.ι).mapIso e ≪≫ b⟩⟩

#print axioms paired_c3_invertible_of_iso
end HodgeLean.Foundations.Program.G32Native
