import HodgeLean.Foundations.AlgebraicGeometry.RamifiedNormalization.StageThree.Defs
import HodgeLean.Foundations.Program.SchoenTowerI2aFieldOpenFactor

/-! # Nonempty quotient charts at a branch intersection
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
open CategoryTheory
namespace AlgebraicGeometry.RamifiedNormalization.StageThree

theorem branch_generator_not_isUnit {X : Scheme} (I : X.IdealSheafData)
    (U : X.affineOpens) (x : X) (hx : x ∈ U.1) (hI : x ∈ I.support)
    (u : Γ(X, U)) (hu : I.ideal U = Ideal.span {u}) : ¬ IsUnit u := by
  intro hunit
  have hz := (Scheme.IdealSheafData.mem_support_iff_of_mem hx).mp hI
  rw [hu, X.zeroLocus_span] at hz
  have hn := (X.mem_zeroLocus_iff _ x).mp hz u (Set.mem_singleton u)
  rw [X.basicOpen_of_isUnit hunit] at hn
  exact hn hx

theorem quotient_chart_nontrivial {R S : Type} [CommRing R] [CommRing S]
    (f : R →+* S) (s : S) (u v : R) (hu : ¬ IsUnit u)
    (hk : RingHom.ker (Polynomial.eval₂RingHom f s) =
      Ideal.span {Polynomial.C u - Polynomial.X * Polynomial.C v}) : Nontrivial S := by
  refine ⟨⟨0, 1, ?_⟩⟩
  intro h01
  have hmem : (1 : Polynomial R) ∈ RingHom.ker (Polynomial.eval₂RingHom f s) := by
    rw [RingHom.mem_ker, map_one]
    exact h01.symm
  rw [hk] at hmem
  have ht : Ideal.span {Polynomial.C u - Polynomial.X * Polynomial.C v} = ⊤ :=
    (Ideal.eq_top_iff_one _).mpr hmem
  have hi := (Ideal.span_singleton_eq_top.mp ht).map (Polynomial.evalRingHom (0 : R))
  apply hu
  simpa using hi

theorem affineOpen_nonempty (X : Scheme) (V : X.affineOpens)
    [Nontrivial Γ(X, V)] : Nonempty V.1 := by
  haveI : Nonempty (Spec ↧Γ(X, V)) := inferInstance
  exact ⟨V.2.isoSpec.inv (Classical.arbitrary (Spec ↧Γ(X, V)))⟩

def quotientChartEquiv {R S : Type} [CommRing R] [CommRing S]
    (f : R →+* S) (s : S) (u v : R)
    (hf : Function.Surjective (Polynomial.eval₂RingHom f s))
    (hk : RingHom.ker (Polynomial.eval₂RingHom f s) =
      Ideal.span {Polynomial.C u - Polynomial.X * Polynomial.C v}) :
    RegularPairChart.ring u v ≃+* S :=
  (Ideal.quotEquivOfEq hk.symm).trans
    (RingHom.quotientKerEquivOfSurjective hf)

theorem quotientChartEquiv_mk {R S : Type} [CommRing R] [CommRing S]
    (f : R →+* S) (s : S) (u v : R)
    (hf : Function.Surjective (Polynomial.eval₂RingHom f s))
    (hk : RingHom.ker (Polynomial.eval₂RingHom f s) =
      Ideal.span {Polynomial.C u - Polynomial.X * Polynomial.C v}) :
    (quotientChartEquiv f s u v hf hk).toRingHom.comp (Ideal.Quotient.mk _) =
      Polynomial.eval₂RingHom f s := by
  apply RingHom.ext
  intro p
  simp [quotientChartEquiv]

end AlgebraicGeometry.RamifiedNormalization.StageThree
