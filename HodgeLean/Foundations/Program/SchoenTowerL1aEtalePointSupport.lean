import HodgeLean.Foundations.Program.SchoenTowerL1aPrincipalSupport
import HodgeLean.Foundations.Program.SchoenTowerL1aLocalPointParameter
import Mathlib.RingTheory.RingHom.Etale
import Mathlib.RingTheory.Noetherian.Basic

/-! # Etale parameter equations retaining actual finite rational support

An etale affine curve parameter can be restricted around its finite support
so that its zero equation is the actual distinguished point kernel.
HC no distance; AV milestone no distance.
-/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

set_option backward.isDefEq.respectTransparency false in
/-- An etale polynomial parameter with one distinguished zero generates that actual point kernel on a principal neighborhood of the finite support.
Source: Stacks Project, tag 02FM; Atiyah–Macdonald, Introduction to Commutative Algebra, Proposition 1.10 and Chapter 3. -/
theorem s2v_l1a_etale_parameter_point_support
    {K A ι : Type} [Field K] [CommRing A] [Algebra K A] [Algebra.FiniteType K A]
    [Finite ι] (φ : ι → A →ₐ[K] K) (hinj : Function.Injective φ) (i₀ : ι)
    (g : A) (hEt : (Polynomial.aeval (R := K) g).toRingHom.Etale)
    (hg0 : φ i₀ g = 0) (hg : ∀ i, i ≠ i₀ → φ i g ≠ 0) :
    ∃ d : A, (∀ i, φ i d = 1) ∧
      (RingHom.ker (φ i₀).toRingHom).map (algebraMap A (Localization.Away d)) =
        Ideal.span {algebraMap A (Localization.Away d) g} := by
  let P := Polynomial K
  let m := RingHom.ker (φ i₀).toRingHom
  letI : m.IsPrime := RingHom.ker_isPrime _
  letI : Algebra P A := (Polynomial.aeval (R := K) g).toRingHom.toAlgebra
  letI : Algebra.Etale P A := hEt
  letI : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing K A
  have hlocal := s2v_l1a_unramified_parameter_local_point_ideal g (φ i₀) hg0 inferInstance
  apply s2v_l1a_principal_ideal_neighborhood_of_point_localization φ hinj i₀ m
    (IsNoetherian.noetherian m) g hg0 hg
  rw [hlocal, Ideal.map_span, Set.image_singleton]

end HodgeLean.Foundations.Program
