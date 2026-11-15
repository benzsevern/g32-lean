import HodgeLean.Foundations.AlgebraicGeometry.SingularCycles.RamifiedDefs
import HodgeLean.Adapters.IntersectionProductLocalAssembly
import HodgeLean.Adapters.NormalConeB4aGysinExactModel

/-! # The unreduced fibre length in a source stalk

At a point of a fibre over a marked target point, the defining prime ideal
in the target stalk is its maximal ideal. The quotient length is measured
in the source stalk without taking a reduction.
HC no distance; AV milestone no distance.
-/

noncomputable section
open CategoryTheory AlgebraicGeometry HodgeLean.Adapters
set_option maxHeartbeats 400000
namespace AlgebraicGeometry.SingularCycles

theorem genericLength_eq_source_stalk_quotient {X Z : Scheme} [IsNoetherian Z]
    (f : X ⟶ Z) (z : Z) (y : (ccm3_inverseIdeal f z).subscheme)
    (hy : f ((ccm3_inverseIdeal f z).subschemeι y) = z) :
    ccm3_genericLength f z y =
      Module.length (X.presheaf.stalk ((ccm3_inverseIdeal f z).subschemeι y))
        (X.presheaf.stalk ((ccm3_inverseIdeal f z).subschemeι y) ⧸
          (IsLocalRing.maximalIdeal
            (Z.presheaf.stalk (f ((ccm3_inverseIdeal f z).subschemeι y)))).map
              (f.stalkMap ((ccm3_inverseIdeal f z).subschemeι y)).hom) := by
  have hideal : a3i_stalkIdeal Z (f ((ccm3_inverseIdeal f z).subschemeι y)) z =
      IsLocalRing.maximalIdeal
        (Z.presheaf.stalk (f ((ccm3_inverseIdeal f z).subschemeι y))) := by
    calc
      _ = a3i_stalkIdeal Z (f ((ccm3_inverseIdeal f z).subschemeι y))
          (f ((ccm3_inverseIdeal f z).subschemeι y)) :=
        congrArg (a3i_stalkIdeal Z (f ((ccm3_inverseIdeal f z).subschemeι y))) hy.symm
      _ = _ := a3c_stalkIdeal_self Z _
  rw [← a3sv_inverseStalk_length f z y, hideal]

theorem local_parameter_length_eq_nearby_reduced_fibre_card
    {R S : Type} [CommRing R] [IsNoetherianRing R] [CommRing S] [Algebra R S]
    [Algebra.FiniteType R S] [Module.Flat R S]
    (p : Ideal R) [p.IsPrime] [IsAlgClosed p.ResidueField]
    (q : Ideal S) [q.IsPrime] [q.LiesOver p] [Algebra.QuasiFiniteAt R q] :
    ∃ (R' : Type) (_ : CommRing R') (_ : Algebra R R') (_ : Algebra.Etale R R')
      (P : Ideal R') (_ : P.IsPrime) (_ : P.LiesOver p)
      (e : TensorProduct R R' S), IsIdempotentElem e ∧
      Module.Finite R' (Localization.Away e) ∧ Module.Flat R' (Localization.Away e) ∧
      IsLocalRing (P.Fiber (Localization.Away e)) ∧
      (∃ Q : Ideal (TensorProduct R R' S), Q.IsPrime ∧ Q.LiesOver P ∧
        Q.comap Algebra.TensorProduct.includeRight.toRingHom = q ∧ e ∉ Q) ∧
      ∃ U : Set (PrimeSpectrum R'), IsOpen U ∧ ⟨P, inferInstance⟩ ∈ U ∧
        ∀ (b : PrimeSpectrum R'), b ∈ U →
          ∀ [IsAlgClosed b.asIdeal.ResidueField] [_root_.IsReduced (b.asIdeal.Fiber (Localization.Away e))],
            Module.length
              (Localization.AtPrime q ⧸ p.map (algebraMap R (Localization.AtPrime q)))
              (Localization.AtPrime q ⧸ p.map (algebraMap R (Localization.AtPrime q))) =
                (Nat.card (PrimeSpectrum (b.asIdeal.Fiber (Localization.Away e))) : ℕ∞) := by
  obtain ⟨R', _, _, _, P, _, _, e, he, hfin, hflat, hlocal, hres, hpoint, hlen⟩ :=
    a3b4a_gysin_exists_exact_local_model p q
  letI : Module.Finite R' (Localization.Away e) := hfin
  letI : Module.Flat R' (Localization.Away e) := hflat
  letI : IsLocalRing (P.Fiber (Localization.Away e)) := hlocal
  letI : IsNoetherianRing R' := Algebra.FiniteType.isNoetherianRing R R'
  letI : Module.FinitePresentation R' (Localization.Away e) :=
    Module.finitePresentation_of_finite R' (Localization.Away e)
  letI : IsAlgClosed P.ResidueField := IsAlgClosed.of_ringEquiv p.ResidueField P.ResidueField
    (AlgEquiv.ofBijective
      (Ideal.ResidueField.mapₐ p P (Algebra.ofId _ _) (P.over_def p)) hres).toRingEquiv
  obtain ⟨U, hU, hPU, hcard⟩ :=
    a3b4a_gysin_local_fibre_length_eq_card_nearby (A := Localization.Away e)
      (⟨P, inferInstance⟩ : PrimeSpectrum R')
  refine ⟨R', inferInstance, inferInstance, inferInstance, P, inferInstance, inferInstance,
    e, he, hfin, hflat, hlocal, hpoint, U, hU, hPU, ?_⟩
  intro b hb _ _
  exact hlen.symm.trans (hcard b hb)

end AlgebraicGeometry.SingularCycles
