import HodgeLean.Foundations.Program.SchoenCycleS3ConormalIsoTransport
import HodgeLean.Foundations.Program.G32Native.PairedC3RouteNObjects

/-! # Zero conormals for isomorphisms -/
noncomputable section
set_option maxHeartbeats 200000
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace HodgeLean.Foundations.Program.G32Native
open HodgeLean.Foundations.Program

/-- An isomorphism has zero actual conormal, by the kernel definition. -/
theorem paired_c3_conormal_isZero_of_isIso {X Y : Scheme} (f : X ⟶ Y) [IsIso f] :
    IsZero (s2c_conormal f) := by
  let g := SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom
  letI : IsIso g := s2e_unitPushforward_isIso f
  exact (Scheme.Modules.pullback f).map_isZero (isZero_kernel_of_mono g)

/-- The empty free sheaf is zero, directly from its section generators. -/
theorem paired_c3_free_empty_isZero (X : Scheme) :
    IsZero (SheafOfModules.free (R := X.ringCatSheaf) (Fin 0) : X.Modules) := by
  rw [IsZero.iff_id_eq_zero]
  apply (SheafOfModules.freeHomEquiv _ (I := Fin 0)).injective
  funext j
  exact Fin.elim0 j

/-- The rank-zero frame of an isomorphism's actual conormal. -/
def pairedC3IsomorphismConormalFrame {X Y : Scheme} (f : X ⟶ Y) [IsIso f] :
    s2c_conormal f ≅ SheafOfModules.free (R := X.ringCatSheaf) (Fin 0) :=
  (paired_c3_conormal_isZero_of_isIso f).iso (paired_c3_free_empty_isZero X)

end HodgeLean.Foundations.Program.G32Native
