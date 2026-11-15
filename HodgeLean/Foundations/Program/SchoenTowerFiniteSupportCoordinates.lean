import HodgeLean.Foundations.Program.SchoenTowerCoordinateFlat
import HodgeLean.Foundations.Program.SchoenTowerLocalJetInterpolation
import HodgeLean.Foundations.Program.SchoenTowerEtaleNeighborhood
import Mathlib.RingTheory.Smooth.Fiber

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace HodgeLean.Foundations.Program

/-- Local differential generators at finitely many rational points give a global polynomial
coordinate with specified values and an étale principal neighborhood of the support.
Source: Stacks Project, Tag 054L; Atiyah–Macdonald, Proposition 1.10. -/
theorem s2t_etale_coordinate_of_local_differential_generators {K A ι : Type*}
    [Field K] [IsAlgClosed K] [CommRing A] [IsDomain A] [Algebra K A]
    [Algebra.FiniteType K A] [Finite ι] [Nonempty ι]
    (φ : ι → A →ₐ[K] K) (hinj : Function.Injective φ)
    [∀ i, (RingHom.ker (φ i).toRingHom).IsPrime]
    [∀ i, Nontrivial (KaehlerDifferential K (Localization.AtPrime (RingHom.ker (φ i).toRingHom)))]
    (t : (i : ι) → Localization.AtPrime (RingHom.ker (φ i).toRingHom))
    (ht : ∀ i, Submodule.span (Localization.AtPrime (RingHom.ker (φ i).toRingHom))
      {KaehlerDifferential.D K (Localization.AtPrime (RingHom.ker (φ i).toRingHom)) (t i)} = ⊤)
    (c : ι → K) :
    ∃ g r : A, (∀ i, φ i g = c i) ∧ (∀ i, φ i r = 1) ∧
      letI := (Polynomial.aeval (R := K) g).toRingHom.toAlgebra
      Algebra.Etale (Polynomial K) (Localization.Away r) := by
  classical
  obtain ⟨g, hg, hjet⟩ := s2t_interpolate_localized_jets φ hinj t c
  letI : Algebra (Polynomial K) A := (Polynomial.aeval (R := K) g).toRingHom.toAlgebra
  letI : IsScalarTower K (Polynomial K) A :=
    IsScalarTower.of_algebraMap_eq' (Polynomial.aeval (R := K) g).comp_algebraMap.symm
  have hspan (i : ι) : Submodule.span (Localization.AtPrime (RingHom.ker (φ i).toRingHom))
      {(KaehlerDifferential.D K (Localization.AtPrime (RingHom.ker (φ i).toRingHom))
        (algebraMap A (Localization.AtPrime (RingHom.ker (φ i).toRingHom)) g))} = ⊤ := by
    obtain ⟨k, hk⟩ := hjet i
    exact s2t_differential_generator_of_same_jet _ (KaehlerDifferential.D K _)
      (IsLocalRing.maximalIdeal_le_jacobson ⊥) (t i) _ k hk (ht i)
  have hne (i : ι) : KaehlerDifferential.D K
      (Localization.AtPrime (RingHom.ker (φ i).toRingHom))
        (algebraMap A (Localization.AtPrime (RingHom.ker (φ i).toRingHom)) g) ≠ 0 := by
    intro hz
    have h := hspan i
    rw [hz, Submodule.span_zero_singleton] at h
    exact bot_ne_top h
  let i₀ : ι := Classical.arbitrary ι
  let B := Localization.AtPrime (RingHom.ker (φ i₀).toRingHom)
  let D : Derivation K A (KaehlerDifferential K B) :=
    (KaehlerDifferential.D K B).compAlgebraMap A
  have hD : D (algebraMap (Polynomial K) A Polynomial.X) ≠ 0 := by
    change KaehlerDifferential.D K B (algebraMap A B
      (Polynomial.aeval (R := K) g Polynomial.X)) ≠ 0
    rw [Polynomial.aeval_X]
    exact hne i₀
  letI : Module.Flat (Polynomial K) A := s2t_polynomial_flat_of_nonzero_differential D hD
  letI : Algebra.FiniteType (Polynomial K) A := .of_restrictScalars_finiteType K (Polynomial K) A
  letI : Algebra.FinitePresentation (Polynomial K) A :=
    Algebra.FinitePresentation.of_finiteType.mp inferInstance
  have hunram (i : ι) : Algebra.IsUnramifiedAt (Polynomial K)
      (RingHom.ker (φ i).toRingHom) := by
    apply s2t_formallyUnramified_of_differential_generator (K := K) Polynomial.X
    convert hspan i using 1
    rw [IsScalarTower.algebraMap_apply (Polynomial K) A]
    change Submodule.span _ {(KaehlerDifferential.D K _
      (algebraMap A _ (Polynomial.aeval (R := K) g Polynomial.X)))} = _
    rw [Polynomial.aeval_X]
  letI (i : ι) : Algebra.IsUnramifiedAt (Polynomial K) (RingHom.ker (φ i).toRingHom) := hunram i
  letI (i : ι) : Algebra.IsEtaleAt (Polynomial K) (RingHom.ker (φ i).toRingHom) :=
    Algebra.IsEtaleAt.of_isUnramifiedAt_of_flat _
  obtain ⟨r, hr, hEt⟩ := s2t_common_principal_etale_neighborhood (R := Polynomial K) φ hinj
  exact ⟨g, r, hg, hr, hEt⟩

end HodgeLean.Foundations.Program
