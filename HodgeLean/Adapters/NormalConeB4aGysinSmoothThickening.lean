import HodgeLean.Adapters.NormalConeB4aGysinParameterOpen
import Mathlib.RingTheory.Smooth.Basic
import Mathlib.RingTheory.Finiteness.NilpotentKer

/-! # Finite retractions onto smooth quotients of nilpotent thickenings -/

noncomputable section
namespace HodgeLean.Adapters

/-- A formally smooth quotient of a Noetherian nilpotent thickening lifts back into the
full algebra, making that full algebra finite over the lifted quotient. -/
theorem a3b4a_gysin_exists_finite_smooth_retraction
    {k A B : Type*} [CommRing k] [CommRing A] [IsNoetherianRing A] [CommRing B]
    [Algebra k A] [Algebra k B] [Algebra.FormallySmooth k B]
    (π : A →ₐ[k] B) (hπ : Function.Surjective π)
    (hnil : IsNilpotent (RingHom.ker π)) :
    ∃ σ : B →ₐ[k] A, π.comp σ = AlgHom.id k B ∧
      letI : Algebra B A := σ.toRingHom.toAlgebra
      Module.Finite B A := by
  let σ := Algebra.FormallySmooth.liftOfSurjective (AlgHom.id k B) π hπ hnil
  have hσ : π.comp σ = AlgHom.id k B :=
    Algebra.FormallySmooth.comp_liftOfSurjective (AlgHom.id k B) π hπ hnil
  refine ⟨σ, hσ, ?_⟩
  letI : Algebra B A := σ.toRingHom.toAlgebra
  let f : A →ₐ[B] B :=
    { π.toRingHom with
      commutes' := fun b => by
        change π (σ b) = b
        exact DFunLike.congr_fun hσ b }
  have hfg : (RingHom.ker f).FG := (RingHom.ker f).fg_of_isNoetherianRing
  exact Module.finite_of_surjective_of_ker_le_nilradical f hπ
    (hfg.isNilpotent_iff_le_nilradical.mp hnil) hfg

end HodgeLean.Adapters
