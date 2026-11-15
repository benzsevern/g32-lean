import HodgeLean.Foundations.Program.SchoenTowerL1bPrincipalEvaluationChart

/-! Coordinates on the affine image of an actual open immersion.
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- Etale coordinates and exact ideal equations on an affine open immersion give coordinates on its actual affine image. -/
theorem s2v_l1b_affine_image_coordinates
    {X Y : Over (Spec ↧ℂ)} [IsAffine X.left]
    (j : X ⟶ Y) [IsOpenImmersion j.left]
    {ι : Type} (w : ι → Γ(X.left, ⊤)) (s : Fin 2 → ι)
    (I : Fin 2 → Y.left.IdealSheafData)
    (hI : ∀ k, ((I k).comap j.left).ideal ⟨⊤, isAffineOpen_top X.left⟩ = Ideal.span {w (s k)})
    (hEt : (MvPolynomial.eval₂Hom X.hom.appTop.hom w).Etale)
    (p : ComplexPoint X) :
    ∃ (O : Y.left.affineOpens) (z : ι → Γ(Y.left, O))
      (hpre : ⊤ ≤ j.left ⁻¹ᵁ O.1),
      (Point.map j p).underlying ∈ O.1 ∧
      (MvPolynomial.eval₂Hom (Y.hom.appLE ⊤ O.1 le_top).hom z).Etale ∧
      (∀ k, (I k).ideal O = Ideal.span {z (s k)}) ∧
      (∀ i, (j.left.appLE O.1 ⊤ hpre).hom (z i) = w i) := by
  let O : Y.left.affineOpens :=
    ⟨j.left ''ᵁ ⊤, (isAffineOpen_top X.left).image_of_isOpenImmersion j.left⟩
  let e := (j.left.appIso ⊤).commRingCatIsoToRingEquiv
  let z (i : ι) := e.symm (w i)
  have hcoeff (r : Γ(Spec ↧ℂ, ⊤)) :
      e ((Y.hom.appLE ⊤ O.1 le_top).hom r) = X.hom.appTop.hom r := by
    change (j.left.appIso ⊤).hom ((Y.hom.appLE ⊤ O.1 le_top) r) = _
    rw [Scheme.Hom.appIso_hom']
    change ((Y.hom.appLE ⊤ O.1 le_top) ≫
      j.left.appLE (j.left ''ᵁ ⊤) ⊤ _) r = _
    rw [Scheme.Hom.appLE_comp_appLE, Over.w j]
    simp only [Scheme.Hom.appLE, TopologicalSpace.Opens.map_top, homOfLE_refl,
      op_id, X.left.presheaf.map_id, Category.comp_id]
  have hmap : e.symm.toRingHom.comp (MvPolynomial.eval₂Hom X.hom.appTop.hom w) =
      MvPolynomial.eval₂Hom (Y.hom.appLE ⊤ O.1 le_top).hom z := by
    apply MvPolynomial.ringHom_ext
    · intro r
      rw [MvPolynomial.eval₂Hom_C, RingHom.comp_apply, MvPolynomial.eval₂Hom_C]
      change e.symm (X.hom.appTop.hom r) = _
      rw [← hcoeff r, e.symm_apply_apply]
    · intro i
      rw [MvPolynomial.eval₂Hom_X', RingHom.comp_apply, MvPolynomial.eval₂Hom_X']
      rfl
  have hpre : ⊤ ≤ j.left ⁻¹ᵁ O.1 := by
    rw [Scheme.Hom.preimage_image_eq]
  refine ⟨O, z, hpre, ?_, ?_, ?_, ?_⟩
  · exact ⟨p.underlying, trivial, rfl⟩
  · rw [← hmap]
    exact RingHom.Etale.respectsIso.1 _ e.symm hEt
  · intro k
    have H := hI k
    rw [Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion] at H
    have H' := congrArg (Ideal.map e.symm.toRingHom) H
    change Ideal.map e.symm.toRingHom ((I k).ideal O |>.comap e.symm.toRingHom) =
      Ideal.map e.symm.toRingHom (Ideal.span {w (s k)}) at H'
    rw [Ideal.map_comap_of_surjective e.symm.toRingHom e.symm.surjective, Ideal.map_span,
      Set.image_singleton] at H'
    exact H'
  · intro i
    rw [← Scheme.Hom.appIso_hom']
    change (j.left.appIso ⊤).hom (e.symm (w i)) = w i
    exact e.apply_symm_apply _

end HodgeLean.Foundations.Program
