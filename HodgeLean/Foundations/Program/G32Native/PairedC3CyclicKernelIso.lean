import HodgeLean.Foundations.Program.G32Native.PairedC3CyclicKernels

/-! # Comparing kernels of two epimorphisms from the structure module -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 20000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace HodgeLean.Foundations.Program.G32Native
open Scheme.Modules

/-- The kernel of a generating section is annihilated by every other
map from the structure module to the same target. -/
theorem paired_c3_cyclic_kernel_condition {X : Scheme.{0}} {Q : X.Modules}
    (q : SheafOfModules.unit X.ringCatSheaf ⟶ Q) [Epi q]
    (f : SheafOfModules.unit X.ringCatSheaf ⟶ Q) : kernel.ι q ≫ f = 0 := by
  ext U s
  let r : Γ(X, U.unop) := (kernel.ι q).val.app U s
  change pairedC3UnitAppLinear f U.unop r = 0
  apply paired_c3_cyclic_annihilator q f U.unop r
  have h := congrArg (fun g : kernel q ⟶ Q => g.val.app U s) (kernel.condition q)
  change pairedC3UnitAppLinear q U.unop r = 0 at h
  exact h

/-- Two generating sections of the same module have the same actual
kernel subobject, with the original inclusions retained. -/
def pairedC3CyclicKernelIso {X : Scheme.{0}} {Q : X.Modules}
    (q p : SheafOfModules.unit X.ringCatSheaf ⟶ Q) [Epi q] [Epi p] :
    kernel q ≅ kernel p where
  hom := kernel.lift p (kernel.ι q) (paired_c3_cyclic_kernel_condition q p)
  inv := kernel.lift q (kernel.ι p) (paired_c3_cyclic_kernel_condition p q)
  hom_inv_id := by
    apply (cancel_mono (kernel.ι q)).mp
    simp only [Category.assoc, kernel.lift_ι_assoc, kernel.lift_ι, Category.id_comp]
  inv_hom_id := by
    apply (cancel_mono (kernel.ι p)).mp
    simp only [Category.assoc, kernel.lift_ι_assoc, kernel.lift_ι, Category.id_comp]

/-- The comparison retains the original inclusion into the structure module. -/
theorem paired_c3_cyclic_kernel_iso_inclusion {X : Scheme.{0}} {Q : X.Modules}
    (q p : SheafOfModules.unit X.ringCatSheaf ⟶ Q) [Epi q] [Epi p] :
    (pairedC3CyclicKernelIso q p).hom ≫ kernel.ι p = kernel.ι q := kernel.lift_ι _ _ _

end HodgeLean.Foundations.Program.G32Native
