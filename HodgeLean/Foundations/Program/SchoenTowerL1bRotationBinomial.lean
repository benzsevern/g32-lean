import HodgeLean.Foundations.Program.SchoenTowerL1bKvalMaps
import HodgeLean.Foundations.Program.SchoenTowerL1bKummerRoots

noncomputable section
set_option maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- A cyclic binomial generator has a nonzero numerator and denominator in any
represented domain whose fraction field is the base field. -/
theorem s2v_l1b_rotation_fraction_binomial
    {R F K : Type*} [CommRing R] [IsDomain R] [Field F] [Field K]
    [Algebra R F] [IsFractionRing R F] [Algebra F K]
    [FiniteDimensional F K] [IsGalois F K] [IsCyclic (K ≃ₐ[F] K)]
    (hroots : (primitiveRoots (Module.finrank F K) F).Nonempty) :
    let ρ := (algebraMap F K).comp (algebraMap R F)
    ∃ (t : K) (a b : R), a ≠ 0 ∧ b ≠ 0 ∧ t ≠ 0 ∧
      Subfield.closure (Set.range ρ ∪ {t}) = ⊤ ∧
      t ^ Module.finrank F K = ρ a / ρ b := by
  obtain ⟨t, ht, hgen, c, hc⟩ := s2v_l1b_cyclic_section_generator
    (R := R) (F := F) (K := K) hroots
  obtain ⟨a, b, hb, hab⟩ := IsFractionRing.div_surjective R c
  have hb' : b ≠ 0 := nonZeroDivisors.ne_zero hb
  have ha : a ≠ 0 := by
    intro ha
    subst a
    rw [map_zero, zero_div] at hab
    have hc' : c = 0 := hab.symm
    rw [hc', map_zero] at hc
    exact pow_ne_zero _ ht hc.symm
  refine ⟨t, a, b, ha, hb', ht, hgen, ?_⟩
  change t ^ Module.finrank F K =
    algebraMap F K (algebraMap R F a) / algebraMap F K (algebraMap R F b)
  rw [← map_div₀, hab]
  exact hc.symm

/-- The retained finite cyclic field extension gives binomial data over the actual
represented stalk, with one generator before any prime is selected. -/
theorem s2v_l1b_rotation_stalk_binomial
    (B : Over (Spec (CommRingCat.of ℂ))) [IsIntegral B.left]
    {K : Type} [Field K] (x : B.left) (κ : B.left.functionField ⟶ CommRingCat.of K)
    (R : Type) [CommRing R] [IsDomain R]
    (eR : R ≃+* B.left.presheaf.stalk x)
    (m : ℕ)
    (hfield : letI := κ.hom.toAlgebra
      Module.Finite B.left.functionField K ∧ IsGalois B.left.functionField K ∧
      IsCyclic (K ≃ₐ[B.left.functionField] K) ∧
      Module.finrank B.left.functionField K = m) :
    let ρ := (s2v_l1b_kval_stalkMap B.left x κ).comp eR.toRingHom
    ∃ (t : K) (a b : R), a ≠ 0 ∧ b ≠ 0 ∧ t ≠ 0 ∧
      Subfield.closure (Set.range ρ ∪ {t}) = ⊤ ∧ t ^ m = ρ a / ρ b := by
  letI := κ.hom.toAlgebra
  obtain ⟨hfinite, hgalois, hcyclic, hdegree⟩ := hfield
  letI := hfinite
  letI := hgalois
  letI := hcyclic
  letI : Algebra R B.left.functionField :=
    ((algebraMap (B.left.presheaf.stalk x) B.left.functionField).comp eR.toRingHom).toAlgebra
  letI : IsFractionRing R B.left.functionField :=
    IsFractionRing.of_ringEquiv_left eR (fun _ => rfl)
  obtain ⟨t, a, b, ha, hb, ht, hgen, hpow⟩ :=
    s2v_l1b_rotation_fraction_binomial (R := R) (F := B.left.functionField) (K := K)
      (s2v_l1b_functionField_primitiveRoots B _ Module.finrank_pos)
  refine ⟨t, a, b, ha, hb, ht, hgen, ?_⟩
  rw [hdegree] at hpow
  exact hpow

end HodgeLean.Foundations.Program
