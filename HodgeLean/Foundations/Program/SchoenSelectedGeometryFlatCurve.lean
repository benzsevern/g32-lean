import HodgeLean.Foundations.Program.SchoenSelectedGeometryDominantStalk
import Mathlib.RingTheory.Flat.TorsionFree

noncomputable section
set_option maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- A dominant map from an integral scheme is flat when its target stalks are Dedekind domains.
Source: torsion-free modules over Dedekind domains are flat. -/
theorem s0_flat_of_dominant_dedekind_stalks
    {X Y : Scheme} [IsIntegral X] [IsReduced Y]
    (f : X ⟶ Y) [QuasiCompact f] [IsDominant f]
    (hY : ∀ y : Y, IsDedekindDomain (Y.presheaf.stalk y)) : Flat f := by
  apply Flat.of_stalkMap f
  intro x
  let R := Y.presheaf.stalk (f x)
  let S := X.presheaf.stalk x
  letI : Algebra R S := (f.stalkMap x).hom.toAlgebra
  letI : IsDedekindDomain R := hY (f x)
  letI : Module.IsTorsionFree R S :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr (s0_dominant_stalkMap_injective f x)
  have hflat : Module.Flat R S := inferInstance
  rwa [← RingHom.flat_algebraMap_iff, RingHom.algebraMap_toAlgebra] at hflat

#print axioms s0_flat_of_dominant_dedekind_stalks
end HodgeLean.Foundations.Program
