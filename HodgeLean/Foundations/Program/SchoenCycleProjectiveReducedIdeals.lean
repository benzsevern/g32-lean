import HodgeLean.Foundations.Program.SchoenCycleResidueChartSum

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.ComplexProjectiveSpace
attribute [local instance] MvPolynomial.gradedAlgebra
namespace HodgeLean.Foundations.Program

/-- The image ideal of a quasi-compact morphism from a reduced scheme is radical.
Source: Schoen (1988), Lemma 2.4 proof, printed p. 15; reduced coordinate subspaces. -/
theorem s2e_kernel_radical_of_reduced {X Y : Scheme.{0}} (f : X ⟶ Y)
    [QuasiCompact f] [IsReduced X] : f.ker.radical = f.ker := by
  apply Scheme.IdealSheafData.ext
  funext U
  simp only [Scheme.IdealSheafData.radical_ideal, Scheme.Hom.ker_apply]
  exact (Ideal.isRadical_bot.comap (f.app U).hom).radical

/-- Every normalized coordinate intersection ideal is radical, including the unit-ideal chart.
Source: Schoen (1988), Lemma 2.4 proof, printed p. 15. -/
theorem s2e_chart_intersection_radical {k : ℕ} (i : Fin (k + 1))
    (T : Finset (Fin (k + 1))) :
    (Ideal.span ((fun j : Fin (k + 1) =>
      if h : j = i then (1 : MvPolynomial {j : Fin (k + 1) // j ≠ i} ℂ)
      else MvPolynomial.X ⟨j, h⟩) '' (↑T : Set (Fin (k + 1))))).IsRadical := by
  classical
  by_cases hi : i ∈ T
  · have h1 : (1 : MvPolynomial {j : Fin (k + 1) // j ≠ i} ℂ) ∈
        Ideal.span ((fun j : Fin (k + 1) =>
          if h : j = i then (1 : MvPolynomial {j : Fin (k + 1) // j ≠ i} ℂ)
          else MvPolynomial.X ⟨j, h⟩) '' (↑T : Set (Fin (k + 1)))) := by
      apply Ideal.subset_span
      exact ⟨i, hi, dite_eq_left rfl⟩
    rw [(Ideal.eq_top_iff_one _).mpr h1]
    exact Ideal.radical_eq_iff.mp (Ideal.radical_top _)
  · obtain ⟨E⟩ := s2e_chartQuotient i T hi
    letI := isReduced_of_injective E.toRingHom E.injective
    exact (Ideal.isRadical_iff_quotient_reduced _).mpr inferInstance

/-- The scheme intersection retains the reduced structure of its coordinate-chart quotients.
Source: Schoen (1988), Lemma 2.4 proof, printed p. 15. -/
theorem s2e_residue_intersection_radical (k : ℕ) (T : Finset (Fin (k + 1))) :
    (s2e_s2b_intersectionIdeal k T).radical = s2e_s2b_intersectionIdeal k T := by
  let I := s2e_s2b_intersectionIdeal k T
  let U (i : Fin (k + 1)) : (ProjectiveSpace (Fin (k + 1)) (Spec ↧ℂ)).affineOpens :=
    ⟨s2e_s2b_chart i ''ᵁ ⊤, (isAffineOpen_top _).image_of_isOpenImmersion (s2e_s2b_chart i)⟩
  have hU (i : Fin (k + 1)) : (U i).1 = projectiveSpaceBasicOpen k (MvPolynomial.X i) := by
    change s2e_s2b_chart i ''ᵁ ⊤ = _
    rw [Scheme.Hom.image_top_eq_opensRange]
    apply TopologicalSpace.Opens.ext
    simpa only [Scheme.Hom.coe_opensRange] using s2e_chart_range i
  have hcover : ⨆ i, (U i).1 = ⊤ := by
    simp only [hU]
    exact (pullback.snd (terminal.from (Spec ↧ℂ))
      (terminal.from (Proj (UniversalGrading.{0} k)))).iSup_preimage_eq_top
        (iSup_coordinateBasicOpen_eq_top k)
  apply le_antisymm
  · apply Scheme.IdealSheafData.le_of_iSup_eq_top U hcover
    intro i
    change (I.ideal (U i)).radical ≤ I.ideal (U i)
    let R := CommRingCat.of (MvPolynomial {j : Fin (k + 1) // j ≠ i} ℂ)
    let φ := (Scheme.ΓSpecIso R).hom.hom
    have hm : (Ideal.map φ ((I.comap (s2e_s2b_chart i)).ideal ⟨⊤, isAffineOpen_top _⟩)).IsRadical := by
      rw [s2e_chain_residue_projective_chart_aux]
      exact s2e_chart_intersection_radical i T
    have hl := hm.comap φ
    have hsurj : Function.Surjective φ := (Scheme.ΓSpecIso R).commRingCatIsoToRingEquiv.surjective
    have hinj : Function.Injective φ := (Scheme.ΓSpecIso R).commRingCatIsoToRingEquiv.injective
    rw [Ideal.comap_map_of_surjective φ hsurj,
      Ideal.comap_bot_of_injective φ hinj,
      sup_bot_eq] at hl
    rw [Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion] at hl
    have hh : ((I.ideal (U i)).radical).comap ((s2e_s2b_chart i).appIso ⊤).inv.hom =
        (I.ideal (U i)).comap ((s2e_s2b_chart i).appIso ⊤).inv.hom := by
      rw [Ideal.comap_radical, hl.radical]
    have hsurjInv : Function.Surjective ((s2e_s2b_chart i).appIso ⊤).inv.hom :=
      ((s2e_s2b_chart i).appIso ⊤).symm.commRingCatIsoToRingEquiv.surjective
    exact (Ideal.comap_injective_of_surjective _ hsurjInv hh).le
  · exact Scheme.IdealSheafData.le_radical I

end HodgeLean.Foundations.Program
