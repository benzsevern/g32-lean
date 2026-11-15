import HodgeLean.Foundations.AlgebraicGeometry.SingularCycles.RamifiedDefs
import Mathlib.RingTheory.Regular.Flat
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra

/-! # Regular stalk parameters under a flat morphism

A flat map of scheme stalks is local and therefore faithfully flat.
Regular target parameters remain regular after mapping into the source stalk.
HC no distance; AV milestone no distance.
-/

noncomputable section
open CategoryTheory AlgebraicGeometry HodgeLean.Adapters
set_option maxHeartbeats 400000
namespace AlgebraicGeometry.SingularCycles

theorem regular_stalk_parameters_pullback {X Z : Scheme} (f : X ⟶ Z) [Flat f]
    (x : X) (rs : List (Z.presheaf.stalk (f x)))
    (hreg : RingTheory.Sequence.IsRegular (Z.presheaf.stalk (f x)) rs) :
    RingTheory.Sequence.IsRegular (X.presheaf.stalk x) (rs.map (f.stalkMap x).hom) := by
  let A := Z.presheaf.stalk (f x)
  let B := X.presheaf.stalk x
  letI : Algebra A B := (f.stalkMap x).hom.toAlgebra
  letI : Module.Flat A B := Flat.stalkMap f x
  letI : IsLocalHom (algebraMap A B) := f.toLRSHom.prop x
  letI : Module.FaithfullyFlat A B := Module.FaithfullyFlat.of_flat_of_isLocalHom
  exact hreg.of_faithfullyFlat

theorem regular_parameter_germs_pullback {X Z : Scheme} (f : X ⟶ Z) [Flat f]
    (x : X) (U : Z.Opens) (hx : f x ∈ U) {d : ℕ} (g : Fin d → Γ(Z, U))
    (hreg : RingTheory.Sequence.IsRegular (Z.presheaf.stalk (f x))
      (List.ofFn fun j => Z.presheaf.germ U (f x) hx (g j))) :
    RingTheory.Sequence.IsRegular (X.presheaf.stalk x)
      (List.ofFn fun j => X.presheaf.germ (f ⁻¹ᵁ U) x hx (f.app U (g j))) := by
  have h := regular_stalk_parameters_pullback f x _ hreg
  rw [List.map_ofFn] at h
  simp only [Function.comp_def] at h
  have heq : (fun j => (f.stalkMap x).hom (Z.presheaf.germ U (f x) hx (g j))) =
      (fun j => X.presheaf.germ (f ⁻¹ᵁ U) x hx (f.app U (g j))) := by
    funext j
    exact Scheme.Hom.germ_stalkMap_apply f U x hx (g j)
  rw [heq] at h
  exact h

end AlgebraicGeometry.SingularCycles
