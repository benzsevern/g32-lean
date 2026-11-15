import HodgeLean.Foundations.Program.CompensationAssemblyFiniteSmooth
import Mathlib.RingTheory.Etale.Field
import Mathlib.RingTheory.Flat.Rank

noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 10000
open CategoryTheory AlgebraicGeometry HodgeLean.Adapters
open scoped TensorProduct
namespace HodgeLean.Foundations.Program

theorem cq_finiteEtale_complex_finrank (B : Type) [CommRing B] [Algebra ℂ B]
    [Algebra.EssFiniteType ℂ B] [Algebra.FormallyEtale ℂ B] :
    Module.finrank ℂ B = Nat.card (PrimeSpectrum B) := by
  classical
  letI : Module.Finite ℂ B := Algebra.FormallyUnramified.finite_of_free ℂ B
  letI : IsArtinianRing B := IsArtinianRing.of_finite ℂ B
  letI : Fintype (PrimeSpectrum B) := Fintype.ofFinite _
  simpa only [Module.finrank_fintype_fun_eq_card, Nat.card_eq_fintype_card] using
    (Algebra.FormallyEtale.equivPiOfIsSepClosed ℂ B).toLinearEquiv.finrank_eq

theorem cq_finiteEtale_complex_fiber_card (R B : Type) [CommRing R] [IsDomain R]
    [CommRing B] [Algebra R B] [Algebra R ℂ]
    [Module.Finite R B] [Module.Flat R B] [Algebra.Etale R B] :
    Nat.card (PrimeSpectrum (ℂ ⊗[R] B)) =
      Module.rankAtStalk (R := R) B ⟨⊥, inferInstance⟩ := by
  let p : PrimeSpectrum ℂ := ⟨⊥, inferInstance⟩
  let p0 : PrimeSpectrum R := ⟨⊥, inferInstance⟩
  have hc : Module.rankAtStalk (R := R) B (p.comap (algebraMap R ℂ)) =
      Module.rankAtStalk (R := R) B p0 := by
    symm
    apply Module.rankAtStalk_eq_of_le_of_finite_of_flat B
    change (⊥ : Ideal R) ≤ _
    exact bot_le
  have hf : Module.rankAtStalk (R := ℂ) (ℂ ⊗[R] B) p = Module.finrank ℂ (ℂ ⊗[R] B) :=
    congrFun (Module.rankAtStalk_eq_finrank_of_free (R := ℂ) (M := ℂ ⊗[R] B)) p
  calc
    Nat.card (PrimeSpectrum (ℂ ⊗[R] B)) = Module.finrank ℂ (ℂ ⊗[R] B) :=
      (cq_finiteEtale_complex_finrank (ℂ ⊗[R] B)).symm
    _ = Module.rankAtStalk (R := ℂ) (ℂ ⊗[R] B) p := hf.symm
    _ = Module.rankAtStalk (R := R) B (p.comap (algebraMap R ℂ)) :=
      Module.rankAtStalk_baseChange (M := B) p
    _ = Module.rankAtStalk (R := R) B p0 := hc

theorem cq_rankAtStalk_domain (R M : Type) [CommRing R] [IsDomain R]
    [AddCommGroup M] [Module R M] (p : PrimeSpectrum R) :
    Module.rankAtStalk (R := R) M p = Module.finrank R M := by
  change Module.finrank (Localization.AtPrime p.asIdeal)
    (LocalizedModule p.asIdeal.primeCompl M) = Module.finrank R M
  rw [IsLocalization.finrank_eq (Localization.AtPrime p.asIdeal) p.asIdeal.primeCompl
    p.asIdeal.primeCompl_le_nonZeroDivisors]
  exact IsLocalizedModule.finrank_eq p.asIdeal.primeCompl
    (LocalizedModule.mkLinearMap p.asIdeal.primeCompl M) p.asIdeal.primeCompl_le_nonZeroDivisors

theorem cq_finiteEtale_complex_fiber_degree (R B : Type) [CommRing R] [IsDomain R]
    [CommRing B] [IsDomain B] [Algebra R B] [Algebra R ℂ]
    [Module.Finite R B] [Module.Flat R B] [Algebra.Etale R B]
    (hinj : Function.Injective (algebraMap R B)) :
    a1p_degree (Spec.map (CommRingCat.ofHom (algebraMap R B)))
        (⟨⊥, inferInstance⟩ : Spec (CommRingCat.of B)) =
      Nat.card (PrimeSpectrum (ℂ ⊗[R] B)) := by
  rw [cq_finiteEtale_complex_fiber_card, cq_rankAtStalk_domain]
  have hx : ((Spec.map (CommRingCat.ofHom (algebraMap R B)))
      (⟨⊥, inferInstance⟩ : Spec (CommRingCat.of B))).asIdeal = ⊥ := by
    change Ideal.comap (algebraMap R B) ⊥ = ⊥
    exact (RingHom.ker_eq_comap_bot (algebraMap R B)).symm.trans
      ((RingHom.injective_iff_ker_eq_bot (algebraMap R B)).mp hinj)
  have h := a1x_degree_specMap_bot (CommRingCat.ofHom (algebraMap R B))
    (⟨⊥, inferInstance⟩ : Spec (CommRingCat.of B)) rfl hx
  have ha : (CommRingCat.ofHom (algebraMap R B)).hom.toAlgebra =
      (inferInstance : Algebra R B) := toAlgebra_algebraMap
  rw [ha] at h
  exact h

end HodgeLean.Foundations.Program
