import HodgeLean.Foundations.Program.SchoenCycleS3CoordinateDensity

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexProjectiveSpace
attribute [local instance] MvPolynomial.gradedAlgebra
namespace HodgeLean.Foundations.Program

theorem s2e_residue_support_chart {k : ℕ} (i j : Fin (k + 1))
    (p : PrimeSpectrum (MvPolynomial {q : Fin (k + 1) // q ≠ i} ℂ)) :
    s2e_s2b_chart i p ∈ (s2e_s2b_residueIdeal k j).support ↔
      s2e_s2b_chartHom.{0} i (chartCoordinate.{0} i j) ∈ p.asIdeal := by
  change s2e_s2b_chart i p ∈ ((s2e_s2b_residueIdeal k j).support : Set _ ) ↔ _
  rw [s2e_s2b_residueIdeal, Scheme.IdealSheafData.coe_support_vanishingIdeal]
  have hh := s2e_chart_preimage_basicOpen i j
  have hm := Iff.of_eq (congrArg (fun U => p ∈ U) hh)
  change (s2e_s2b_chart i p ∉ projectiveSpaceBasicOpen k (MvPolynomial.X j)) ↔ _
  change (s2e_s2b_chart i p ∈ projectiveSpaceBasicOpen k (MvPolynomial.X j) ↔
    s2e_s2b_chartHom.{0} i (chartCoordinate.{0} i j) ∉ p.asIdeal) at hm
  change (¬ ((s2e_s2b_chart i p) ∈ projectiveSpaceBasicOpen k (MvPolynomial.X j))) ↔ _
  rw [hm]
  simp only [not_not]

theorem s2e_distinct_residue_dense (k : ℕ) (j t : Fin (k + 1)) (htj : t ≠ j) :
    ((s2e_s2b_residueIdeal k j).support : Set _) ⊆
      closure (((s2e_s2b_residueIdeal k j).support : Set _) \
        ((s2e_s2b_residueIdeal k t).support : Set (ProjectiveSpace (Fin (k + 1)) (Spec ↧ℂ)))) := by
  intro y hy
  have hc : y ∈ ⨆ i : Fin (k + 1), projectiveSpaceBasicOpen k (MvPolynomial.X i) := by
    rw [show (⨆ i : Fin (k + 1), projectiveSpaceBasicOpen k (MvPolynomial.X i)) = ⊤ from
      (CategoryTheory.Limits.pullback.snd (CategoryTheory.Limits.terminal.from (Spec ↧ℂ))
        (CategoryTheory.Limits.terminal.from (Proj (UniversalGrading k)))).iSup_preimage_eq_top
          (iSup_coordinateBasicOpen_eq_top k)]
    trivial
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hc
  change y ∈ (projectiveSpaceBasicOpen k (MvPolynomial.X i) : Set _) at hi
  rw [← s2e_chart_range i] at hi
  obtain ⟨p, rfl⟩ := hi
  have hpj := (s2e_residue_support_chart i j p).mp hy
  have hji : j ≠ i := by
    intro h
    subst j
    rw [s2e_chartHom_coordinate, dite_eq_left rfl] at hpj
    exact p.isPrime.ne_top (p.asIdeal.eq_top_of_isUnit_mem hpj isUnit_one)
  let I := Ideal.span {s2e_s2b_chartHom.{0} i (chartCoordinate.{0} i j)}
  let q : PrimeSpectrum (MvPolynomial {q : Fin (k + 1) // q ≠ i} ℂ) :=
    ⟨I, s2e_chart_coordinate_prime i j hji⟩
  have hpcl : p ∈ closure ({q} : Set _) := by
    rw [PrimeSpectrum.closure_singleton]
    exact Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hpj)
  have hqj : s2e_s2b_chart i q ∈ (s2e_s2b_residueIdeal k j).support :=
    (s2e_residue_support_chart i j q).mpr (Ideal.subset_span (Set.mem_singleton _))
  have hqt : s2e_s2b_chart i q ∉ (s2e_s2b_residueIdeal k t).support := by
    rw [s2e_residue_support_chart]
    exact s2e_chart_distinct_coordinate_not_mem i j t hji htj
  have hh := mem_closure_image (s2e_s2b_chart i).continuous.continuousAt hpcl
  apply closure_mono _ hh
  rintro _ ⟨z, hz, rfl⟩
  rw [Set.mem_singleton_iff] at hz
  subst z
  exact ⟨hqj, hqt⟩

end HodgeLean.Foundations.Program
