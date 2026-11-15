import HodgeLean.Foundations.Program.SchoenCycleProjectiveAffineIdeals

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexProjectiveSpace
attribute [local instance] MvPolynomial.gradedAlgebra
namespace HodgeLean.Foundations.Program

/-- The projective ratio basic-open formula before specialization of the affine ring map.
Source: Schoen (1988), Lemma 2.4 proof, printed p. 15; standard projective charts. -/
theorem s2e_proj_coordinate_preimage {k : ℕ} (i j : Fin (k + 1))
    {R : Type} [CommRing R]
    (f : HomogeneousLocalization.Away (UniversalGrading k) (MvPolynomial.X i) →+* R) :
    (Spec.map (CommRingCat.ofHom f) ≫ Proj.awayι (UniversalGrading k) (MvPolynomial.X i)
      (MvPolynomial.isHomogeneous_X _ _) zero_lt_one) ⁻¹ᵁ
        Proj.basicOpen (UniversalGrading k) (MvPolynomial.X j) =
      PrimeSpectrum.basicOpen (f (chartCoordinate.{0} i j)) := by
  rw [Scheme.Hom.comp_preimage]
  rw [show Proj.awayι (UniversalGrading k) (MvPolynomial.X i)
      (MvPolynomial.isHomogeneous_X (ULift ℤ) i) zero_lt_one ⁻¹ᵁ
        Proj.basicOpen (UniversalGrading k) (MvPolynomial.X j) =
      PrimeSpectrum.basicOpen
        (HomogeneousLocalization.Away.isLocalizationElem
          (MvPolynomial.isHomogeneous_X (ULift ℤ) i) (MvPolynomial.isHomogeneous_X (ULift ℤ) j)) from
    Proj.awayι_preimage_basicOpen
      (𝒜 := UniversalGrading k) (f := MvPolynomial.X i) (g := MvPolynomial.X j)
      (m := 1) (m' := 1) (MvPolynomial.isHomogeneous_X (ULift ℤ) i) zero_lt_one
      (MvPolynomial.isHomogeneous_X (ULift ℤ) j) zero_lt_one]
  rw [s2e_specMap_preimage_basicOpen]
  have helem : HomogeneousLocalization.Away.isLocalizationElem
      (MvPolynomial.isHomogeneous_X (ULift ℤ) i) (MvPolynomial.isHomogeneous_X (ULift ℤ) j) =
      chartCoordinate.{0} i j := by
    apply HomogeneousLocalization.val_injective
    simp [HomogeneousLocalization.Away.isLocalizationElem, chartCoordinate]
  rw [helem]

/-- Normalized affine coordinates pull back each homogeneous basic open to its ratio basic open.
Source: Schoen (1988), Lemma 2.4 proof, printed p. 15. -/
theorem s2e_chart_preimage_basicOpen {k : ℕ} (i j : Fin (k + 1)) :
    s2e_s2b_chart i ⁻¹ᵁ projectiveSpaceBasicOpen k (MvPolynomial.X j) =
      PrimeSpectrum.basicOpen (s2e_s2b_chartHom.{0} i (chartCoordinate.{0} i j)) := by
  rw [projectiveSpaceBasicOpen, ← Scheme.Hom.comp_preimage,
    s2e_s2b_chart, Limits.pullback.lift_snd]
  exact s2e_proj_coordinate_preimage i j (s2e_s2b_chartHom.{0} i)


/-- The normalized coordinate equation generates a radical ideal.
Source: Schoen (1988), Lemma 2.3(vi), printed pp. 13–14; Lemma 2.4 proof, printed p. 15. -/
theorem s2e_chart_coordinate_radical {k : ℕ} (i j : Fin (k + 1)) :
    (Ideal.span {s2e_s2b_chartHom.{0} i (chartCoordinate.{0} i j)}).IsRadical := by
  classical
  by_cases h : j = i
  · subst j
    rw [s2e_chartHom_coordinate, dite_eq_left rfl, Ideal.span_singleton_one]
    exact Ideal.radical_eq_iff.mp (Ideal.radical_top _)
  · obtain ⟨E⟩ := s2e_chartQuotient i {j} (by simpa using Ne.symm h)
    have himage : ((fun q : Fin (k + 1) =>
        if h : q = i then (1 : MvPolynomial {q : Fin (k + 1) // q ≠ i} ℂ)
        else MvPolynomial.X ⟨q, h⟩) '' (↑({j} : Finset (Fin (k + 1))) : Set _)) =
        {s2e_s2b_chartHom.{0} i (chartCoordinate.{0} i j)} := by
      rw [s2e_chartHom_coordinate]
      ext p
      simp only [Set.mem_image, Finset.mem_coe, Finset.mem_singleton,
        exists_eq_left, Set.mem_singleton_iff]
      exact eq_comm
    rw [himage] at E
    have hE := (⟨E⟩ : Nonempty _)
    obtain ⟨E'⟩ := hE
    letI := isReduced_of_injective E'.toRingHom E'.injective
    exact (Ideal.isRadical_iff_quotient_reduced _).mpr inferInstance

/-- The actual residue hyperplane restricts to its normalized linear equation.
Source: Schoen (1988), Lemma 2.3(vi), printed pp. 13–14; Lemma 2.4 proof, printed p. 15. -/
theorem s2e_residueIdeal_chart {k : ℕ} (i j : Fin (k + 1)) :
    Ideal.map (Scheme.ΓSpecIso
        ↧(MvPolynomial {j : Fin (k + 1) // j ≠ i} ℂ)).hom.hom
      (((s2e_s2b_residueIdeal k j).comap (s2e_s2b_chart i)).ideal ⟨⊤, isAffineOpen_top _⟩) =
      Ideal.span {s2e_s2b_chartHom.{0} i (chartCoordinate.{0} i j)} := by
  unfold s2e_s2b_residueIdeal
  rw [s2e_open_comap_vanishingIdeal]
  have hZ : (⟨(projectiveSpaceBasicOpen k (MvPolynomial.X j)).carrierᶜ,
      (projectiveSpaceBasicOpen k (MvPolynomial.X j)).isOpen.isClosed_compl⟩ :
      TopologicalSpace.Closeds _).preimage (s2e_s2b_chart i).continuous =
      ⟨(PrimeSpectrum.basicOpen (s2e_s2b_chartHom.{0} i (chartCoordinate.{0} i j))).carrierᶜ,
        (PrimeSpectrum.basicOpen _).isOpen.isClosed_compl⟩ := by
    apply TopologicalSpace.Closeds.ext
    ext y
    change (s2e_s2b_chart i) y ∉ projectiveSpaceBasicOpen k (MvPolynomial.X j) ↔
      y ∉ PrimeSpectrum.basicOpen (s2e_s2b_chartHom.{0} i (chartCoordinate.{0} i j))
    exact not_congr (Iff.of_eq (congrArg
      (fun U : (Spec ↧(MvPolynomial {q : Fin (k + 1) // q ≠ i} ℂ)).Opens => y ∈ U)
      (s2e_chart_preimage_basicOpen i j)))
  rw [hZ]
  exact s2e_spec_principal_vanishingIdeal _ _ (s2e_chart_coordinate_radical i j)

end HodgeLean.Foundations.Program
