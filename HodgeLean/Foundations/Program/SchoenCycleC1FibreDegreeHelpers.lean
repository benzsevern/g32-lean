import Mathlib.RingTheory.TotallySplit
import Mathlib.RingTheory.Spectrum.Prime.FreeLocus
import Mathlib.LinearAlgebra.Dimension.Localization

/-! # Geometric fibre counts and generic field degrees -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped TensorProduct
namespace HodgeLean.Foundations.Program

/-- The rational points of a finite etale algebra over a separably
closed field count its vector-space dimension. -/
theorem s2e_c1_etale_algHom_card
    (k A : Type*) [Field k] [IsSepClosed k] [CommRing A] [Algebra k A]
    [Module.Finite k A] [Algebra.Etale k A] :
    Nat.card (A →ₐ[k] k) = Module.finrank k A := by
  classical
  have : IsArtinianRing A := isArtinian_of_tower k inferInstance
  let := Fintype.ofFinite (PrimeSpectrum A)
  rw [Nat.card_congr (Algebra.IsFiniteSplit.algHomEquivPrimeSpectrum k A)]
  rw [(Algebra.FormallyEtale.equivPiOfIsSepClosed k A).toLinearEquiv.finrank_eq]
  simp only [Module.finrank_fintype_fun_eq_card, Nat.card_eq_fintype_card]

/-- A reduced etale geometric fibre of a finite flat domain extension
measures the degree of its actual fraction fields. -/
theorem s2e_c1_fieldDegree_eq_etale_fibre_card
    (R S K L : Type*) [CommRing R] [IsDomain R] [CommRing S] [IsDomain S]
    [Field K] [Field L] [Algebra R S] [Module.Finite R S] [Module.Flat R S]
    [Algebra R K] [Algebra S L] [Algebra R L] [Algebra K L]
    [IsScalarTower R S L] [IsScalarTower R K L]
    [IsFractionRing R K] [IsFractionRing S L]
    (p : Ideal R) [p.IsPrime] [IsSepClosed p.ResidueField]
    [Algebra.Etale p.ResidueField (p.Fiber S)] :
    Module.finrank K L = Nat.card (p.Fiber S →ₐ[p.ResidueField] p.ResidueField) := by
  rw [IsFractionRing.finrank_eq R K S L,
    s2e_c1_etale_algHom_card, p.finrank_fiber_eq_finrank]


/-- The rank of a finite flat algebra over a domain is counted by any
etale geometric fibre, even if other fibres have ramification. -/
theorem s2e_c1_finiteFlat_rank_eq_geometric_fibre_card
    (R S k : Type*) [CommRing R] [IsDomain R] [CommRing S]
    [Field k] [IsSepClosed k] [Algebra R S] [Algebra R k]
    [Module.Finite R S] [Module.Flat R S] [Algebra.Etale k (k ⊗[R] S)] :
    Module.finrank R S = Nat.card (S →ₐ[R] k) := by
  let p : PrimeSpectrum k := ⟨⊥, inferInstance⟩
  have hf : Module.rankAtStalk (R := k) (k ⊗[R] S) p =
      Module.finrank k (k ⊗[R] S) :=
    congrFun (Module.rankAtStalk_eq_finrank_of_free (R := k) (M := k ⊗[R] S)) p
  calc
    Module.finrank R S = Module.rankAtStalk (R := R) S (p.comap (algebraMap R k)) :=
      (by
        change Module.finrank R S = Module.finrank
          (Localization.AtPrime (p.comap (algebraMap R k)).asIdeal)
          (LocalizedModule (p.comap (algebraMap R k)).asIdeal.primeCompl S)
        rw [IsLocalization.finrank_eq
          (Localization.AtPrime (p.comap (algebraMap R k)).asIdeal)
          (p.comap (algebraMap R k)).asIdeal.primeCompl
          (p.comap (algebraMap R k)).asIdeal.primeCompl_le_nonZeroDivisors,
          IsLocalizedModule.finrank_eq _ (LocalizedModule.mkLinearMap _ S)
            (p.comap (algebraMap R k)).asIdeal.primeCompl_le_nonZeroDivisors])
    _ = Module.rankAtStalk (R := k) (k ⊗[R] S) p :=
      (Module.rankAtStalk_baseChange (M := S) p).symm
    _ = Module.finrank k (k ⊗[R] S) := hf
    _ = Nat.card ((k ⊗[R] S) →ₐ[k] k) := (s2e_c1_etale_algHom_card k _).symm
    _ = Nat.card (S →ₐ[R] k) :=
      (Nat.card_congr (Algebra.TensorProduct.liftEquivRight R k S k)).symm


/-- Only the selected geometric fibre needs to be etale in order to
measure the generic degree of a finite flat extension. -/
theorem s2e_c1_fieldDegree_eq_geometric_fibre_card
    (R S K L k : Type*) [CommRing R] [IsDomain R] [CommRing S] [IsDomain S]
    [Field K] [Field L] [Field k] [IsSepClosed k]
    [Algebra R S] [Module.Finite R S] [Module.Flat R S]
    [Algebra R K] [Algebra S L] [Algebra R L] [Algebra K L] [Algebra R k]
    [IsScalarTower R S L] [IsScalarTower R K L]
    [IsFractionRing R K] [IsFractionRing S L]
    [Algebra.Etale k (k ⊗[R] S)] :
    Module.finrank K L = Nat.card (S →ₐ[R] k) := by
  rw [IsFractionRing.finrank_eq R K S L]
  exact s2e_c1_finiteFlat_rank_eq_geometric_fibre_card R S k


end HodgeLean.Foundations.Program
