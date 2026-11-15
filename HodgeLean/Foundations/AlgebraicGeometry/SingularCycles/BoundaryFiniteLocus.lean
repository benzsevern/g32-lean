import HodgeLean.Foundations.AlgebraicGeometry.SingularCycles.BoundaryFiniteAlgebra
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Morphisms.Finite

noncomputable section
open CategoryTheory TopologicalSpace
open scoped Classical
namespace AlgebraicGeometry.SingularCycles

set_option backward.isDefEq.respectTransparency false in
theorem boundary_spec_flat_fiber_open {R S : CommRingCat} (φ : R ⟶ S)
    [IsFinite (Spec.map φ)] [IsNoetherianRing R] :
    IsOpen {p : Spec R | ∀ x : Spec S, Spec.map φ x = p →
      ((Spec.map φ).stalkMap x).hom.Flat} := by
  have hfin := (IsFinite.SpecMap_iff φ).mp inferInstance
  algebraize [φ.hom]
  haveI : Module.FinitePresentation R S := Module.finitePresentation_of_finite R S
  have heq : {p : Spec R | ∀ x : Spec S, Spec.map φ x = p →
      ((Spec.map φ).stalkMap x).hom.Flat} = Module.freeLocus R S := by
    ext p
    constructor
    · intro hp
      apply boundary_finite_fiber_free
      intro Q hQ hQp
      have h : Spec.map φ (⟨Q, hQ⟩ : PrimeSpectrum S) = p :=
        PrimeSpectrum.ext hQp
      have hf := hp ⟨Q, hQ⟩ h
      exact (RingHom.Flat.respectsIso.arrow_mk_iso_iff
        (Scheme.arrowStalkMapSpecIso φ ⟨Q, hQ⟩)).mp hf
    · intro hp x hx
      apply (RingHom.Flat.respectsIso.arrow_mk_iso_iff
        (Scheme.arrowStalkMapSpecIso φ x)).mpr
      exact boundary_free_fiber_flat p hp x.asIdeal
        (congrArg PrimeSpectrum.asIdeal hx)
  rw [heq]
  exact Module.isOpen_freeLocus

end AlgebraicGeometry.SingularCycles
