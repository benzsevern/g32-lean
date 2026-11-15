import HodgeLean.Ported.NYLL.SchemeTheory.Modules.LocalMorphisms
import Mathlib.CategoryTheory.Limits.Shapes.Kernels

/-! # Actual section equations for a module kernel lift -/
noncomputable section
set_option maxHeartbeats 200000
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace HodgeLean.Foundations.Program.G32Native
open Scheme.Modules

/-- Inclusion detects the section of an actual kernel lift. -/
theorem paired_c3_kernel_lift_section {X : Scheme.{0}} {M N Q : X.Modules}
    (q : N ⟶ Q) (f : M ⟶ N) (hf : f ≫ q = 0)
    (U : X.Opens) (s : Γ(M, U)) (t : Γ(kernel q, U))
    (h : f.val.app (op U) s = (kernel.ι q).val.app (op U) t) :
    (kernel.lift q f hf).app U s = t := by
  apply (Scheme.Modules.Hom.mono_iff_injective (kernel.ι q)).mp inferInstance U
  change (kernel.lift q f hf ≫ kernel.ι q).app U s = _
  rw [kernel.lift_ι]
  exact h

end HodgeLean.Foundations.Program.G32Native
