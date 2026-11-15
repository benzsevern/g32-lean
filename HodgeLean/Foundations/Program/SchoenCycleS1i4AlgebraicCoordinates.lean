import HodgeLean.Foundations.Program.SchoenCycleActualAnalyticAdic
import HodgeLean.Foundations.Program.SchoenCyclePolynomialPointIdeal
import HodgeLean.Foundations.Program.SchoenCycleNativePolynomialCoordinates
import HodgeLean.Foundations.Program.SchoenCycleOpenStalkSections

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
attribute [local instance] overSpecAlgebra
namespace HodgeLean.Foundations.Program

theorem s2e_chart_section_transport_germ
    (X : Scheme) (U : X.Opens) (x : X) (hx : x ∈ U) (s : Γ(X, U)) :
    X.presheaf.germ (U.ι ''ᵁ (⊤ : U.toScheme.Opens)) x
      (by simpa only [Scheme.Opens.ι_image_top] using hx)
      ((U.ι.appIso ⊤).inv (U.topIso.inv s)) = X.presheaf.germ U x hx s := by
  change ((U.topIso.inv ≫ (U.ι.appIso ⊤).inv) ≫
    X.presheaf.germ _ x _) s = _
  have h : U.topIso.inv ≫ (U.ι.appIso ⊤).inv =
      X.presheaf.map (eqToHom U.ι_image_top).op := by
    rw [Scheme.Opens.ι_appIso]
    change U.topIso.inv ≫ 𝟙 _ = U.topIso.inv
    exact Category.comp_id _
  rw [h]
  exact X.presheaf.germ_res_apply (eqToHom U.ι_image_top) x _ s

theorem s2e_sectionConst_germ_congr
    (X : Over (Spec ↧ℂ)) (U V : X.left.Opens) (h : U = V)
    (x : X.left) (hx : x ∈ U) (hy : x ∈ V) (c : ℂ) :
    X.left.presheaf.germ U x hx (HodgeLean.Adapters.a3b4a_gysin_sectionConst X.hom U c) =
      X.left.presheaf.germ V x hy (HodgeLean.Adapters.a3b4a_gysin_sectionConst X.hom V c) := by
  subst V
  rfl

theorem s2e_actual_centered_coordinate_as_etale
    (X : Over (Spec ↧ℂ)) (d : ℕ) [SmoothOfRelativeDimension d X.hom]
    (p : ComplexPoint X) (i : Fin d) :
    let D := ComplexPoint.localEtaleCoordinates X d p
    s2e_actual_centeredPolynomial_stalk X d p (MvPolynomial.X i) =
      X.left.presheaf.germ D.neighborhood p.underlying D.mem
        (D.coordinateAlgHom (MvPolynomial.X i) -
          D.coordinateAlgHom (MvPolynomial.C (ComplexPoint.localChart X d p p i))) := by
  let D := ComplexPoint.localEtaleCoordinates X d p
  letI : Algebra ℂ Γ(X.left, D.neighborhood) := overSpecAlgebra X D.neighborhood
  dsimp only
  rw [s2e_actual_centeredPolynomial_stalk, RingHom.comp_apply, MvPolynomial.eval₂Hom_X', map_sub, map_sub]
  congr 1
  · exact s2e_chart_section_transport_germ X.left D.neighborhood p.underlying D.mem
      (D.coordinateAlgHom (MvPolynomial.X i))
  · rw [show D.coordinateAlgHom (MvPolynomial.C (ComplexPoint.localChart X d p p i)) =
        HodgeLean.Adapters.a3b4a_gysin_sectionConst X.hom D.neighborhood
          (ComplexPoint.localChart X d p p i) from D.coordinateAlgHom.commutes _]
    exact s2e_sectionConst_germ_congr X D.ambientCoordinateOpen D.neighborhood
      D.neighborhood.ι_image_top p.underlying _ D.mem _

theorem s2e_actual_etale_polynomial_generators
    (X : Over (Spec ↧ℂ)) (d : ℕ) [SmoothOfRelativeDimension d X.hom]
    (p : ComplexPoint X) :
    let D := ComplexPoint.localEtaleCoordinates X d p
    let f := (X.left.presheaf.germ D.neighborhood p.underlying D.mem).hom.comp
      D.coordinateAlgHom.toRingHom
    Ideal.span (Set.range (fun i : Fin d => f (MvPolynomial.X i) -
      f (MvPolynomial.C (ComplexPoint.localChart X d p p i)))) =
        IsLocalRing.maximalIdeal (X.left.presheaf.stalk p.underlying) := by
  let D := ComplexPoint.localEtaleCoordinates X d p
  let A := X.left.presheaf.stalk p.underlying
  let R := Γ(X.left, D.neighborhood)
  let h := (X.left.presheaf.germ D.neighborhood p.underlying D.mem).hom
  letI : Algebra R A := h.toAlgebra
  letI := D.isAffine.isLocalization_stalk ⟨p.underlying, D.mem⟩
  have hh : h.FormallyUnramified := by
    change Algebra.FormallyUnramified R A
    exact Algebra.FormallyUnramified.of_isLocalization
      (D.isAffine.primeIdealOf ⟨p.underlying, D.mem⟩).asIdeal.primeCompl
  have hht : h.EssFiniteType := by
    change Algebra.EssFiniteType R A
    exact Algebra.EssFiniteType.of_isLocalization A
      (D.isAffine.primeIdealOf ⟨p.underlying, D.mem⟩).asIdeal.primeCompl
  let f := h.comp D.coordinateAlgHom.toRingHom
  let e := (s2e_nativeAnalyticGerm_value d).comp (s2e_stalk_nativeAnalyticGerm X d p)
  have hdt : D.coordinateAlgHom.toRingHom.EssFiniteType := by
    letI := D.coordinateAlgHom.toRingHom.toAlgebra
    letI : Algebra.Etale (MvPolynomial (Fin d) ℂ) R := D.etale
    change Algebra.EssFiniteType (MvPolynomial (Fin d) ℂ) R
    infer_instance
  apply s2e_unramified_polynomial_local_generators f
    (D.etale.formallyUnramified.comp hh) (hdt.comp hht)
    e (fun i => ComplexPoint.localChart X d p p i)
  apply MvPolynomial.ringHom_ext
  · intro c
    letI : Algebra ℂ R := overSpecAlgebra X D.neighborhood
    have hc := D.coordinateAlgHom.commutes c
    change D.coordinateAlgHom (MvPolynomial.C c) =
      HodgeLean.Adapters.a3b4a_gysin_sectionConst X.hom D.neighborhood c at hc
    change e (h (D.coordinateAlgHom (MvPolynomial.C c))) = _
    rw [hc, MvPolynomial.eval_C]
    change s2e_nativeAnalyticGerm_value d (s2e_stalk_nativeAnalyticGerm X d p
      (h (HodgeLean.Adapters.a3b4a_gysin_sectionConst X.hom D.neighborhood c))) = c
    rw [s2e_stalk_nativeAnalyticGerm_germ, s2e_regularSection_nativeAnalyticGerm_value]
    exact HodgeLean.Adapters.a3b4a_gysin_evaluate_sectionConst X.hom D.neighborhood p D.mem c
  · intro i
    rw [MvPolynomial.eval_X]
    change e (h (D.coordinateAlgHom (MvPolynomial.X i))) = _
    rw [show h (D.coordinateAlgHom (MvPolynomial.X i)) =
      X.left.presheaf.germ D.ambientCoordinateOpen p.underlying
        (by simpa only [LocalEtaleCoordinates.ambientCoordinateOpen, Scheme.Opens.ι_image_top] using D.mem)
        (D.ambientCoordinateSection i) from
      (s2e_chart_section_transport_germ X.left D.neighborhood p.underlying D.mem _).symm]
    change s2e_nativeAnalyticGerm_value d (s2e_stalk_nativeAnalyticGerm X d p _) = _
    rw [s2e_stalk_nativeAnalyticGerm_germ, s2e_regularSection_nativeAnalyticGerm_value]
    have hchart := congrFun (ComplexPoint.localChart_apply_of_mem X d p p
      (ComplexPoint.mem_localChart_source X d p)) i
    rw [D.ambientAnalyticCoordinates_apply_eq_evaluate] at hchart
    exact hchart.symm

theorem s2e_actual_maximalIdeal_centered_coordinates
    (X : Over (Spec ↧ℂ)) (d : ℕ) [SmoothOfRelativeDimension d X.hom]
    (p : ComplexPoint X) :
    IsLocalRing.maximalIdeal (X.left.presheaf.stalk p.underlying) =
      Ideal.span (Set.range (fun i : Fin d => s2e_actual_centeredPolynomial_stalk X d p (MvPolynomial.X i))) := by
  let D := ComplexPoint.localEtaleCoordinates X d p
  let f := (X.left.presheaf.germ D.neighborhood p.underlying D.mem).hom.comp
    D.coordinateAlgHom.toRingHom
  have h := s2e_actual_etale_polynomial_generators X d p
  change Ideal.span (Set.range (fun i : Fin d => f (MvPolynomial.X i) -
    f (MvPolynomial.C (ComplexPoint.localChart X d p p i)))) = _ at h
  have hc (i : Fin d) : f (MvPolynomial.X i) -
      f (MvPolynomial.C (ComplexPoint.localChart X d p p i)) =
        s2e_actual_centeredPolynomial_stalk X d p (MvPolynomial.X i) := by
    rw [s2e_actual_centered_coordinate_as_etale]
    exact (map_sub (X.left.presheaf.germ D.neighborhood p.underlying D.mem).hom _ _).symm
  simp only [hc] at h
  exact h.symm

end HodgeLean.Foundations.Program
