import HodgeLean.Foundations.Program.SchoenTowerL1bUnitGeneratorNeighborhood
import HodgeLean.Foundations.Program.SchoenTowerL1bSupports
import Mathlib.AlgebraicGeometry.Morphisms.Etale

/-! Exact generator replacement on actual affine opens of the fixed base.
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- Exact principal generator replacement can be realized as an affine-open refinement of the fixed base. -/
theorem s2v_l1b_affine_generator_refinement
    (X : Over (Spec ↧ℂ)) [IsIntegral X.left]
    (U : X.left.affineOpens) {ι : Type} [Fintype ι] [DecidableEq ι]
    (f g : ι → Γ(X.left, U))
    (hEt : (MvPolynomial.eval₂Hom (X.hom.appLE ⊤ U.1 le_top).hom f).Etale)
    (hgen : ∀ i, Ideal.span {g i} = Ideal.span {f i})
    (p : ComplexPoint X) (hp : p ∈ Point.overOpen U.1)
    (hz : ∀ i, Point.evaluate U.1 (f i) p = 0 ∨ g i = f i) :
    ∃ (V : X.left.affineOpens) (hV : V.1 ≤ U.1),
      p ∈ Point.overOpen V.1 ∧
      (MvPolynomial.eval₂Hom (X.hom.appLE ⊤ V.1 le_top).hom
        (fun i => (X.left.presheaf.map (homOfLE hV).op).hom (g i))).Etale := by
  letI : Nonempty U.1 := ⟨⟨p.underlying, hp⟩⟩
  letI : IsDomain Γ(X.left, U) := IsIntegral.component_integral U.1
  let A := Γ(X.left, U)
  let R := Γ(Spec ↧ℂ, ⊤)
  let a : R →+* A := (X.hom.appLE ⊤ U.1 le_top).hom
  letI : Algebra R A := a.toAlgebra
  let φ : A →+* ℂ := (Point.evaluationHom U.1 ⟨p, hp⟩).hom
  have heval (t : A) : φ t = Point.evaluate U.1 t p :=
    Point.evaluationHom_apply U.1 ⟨p, hp⟩ t
  have hz' (i : ι) : φ (f i) = 0 ∨ g i = f i := by
    rw [heval]
    exact hz i
  obtain ⟨d, hd, hloc⟩ := s2v_l1b_etale_coordinate_generator_replacement f g hEt hgen φ hz'
  let V := X.left.affineBasicOpen d
  have hV : V.1 ≤ U.1 := X.left.basicOpen_le d
  let r : A →+* Γ(X.left, V) := (X.left.presheaf.map (homOfLE hV).op).hom
  letI : Algebra A Γ(X.left, V) := r.toAlgebra
  letI : IsLocalization.Away d Γ(X.left, V) := U.2.isLocalization_basicOpen d
  let e : Localization.Away d ≃ₐ[A] Γ(X.left, V) :=
    IsLocalization.algEquiv (Submonoid.powers d) (Localization.Away d) Γ(X.left, V)
  have hcomp : e.toRingHom.comp
      (MvPolynomial.aeval (R := R) (fun i => algebraMap A (Localization.Away d) (g i))).toRingHom =
      MvPolynomial.eval₂Hom (X.hom.appLE ⊤ V.1 le_top).hom (fun i => r (g i)) := by
    apply MvPolynomial.ringHom_ext
    · intro t
      change e ((MvPolynomial.aeval (R := R)
        (fun i => algebraMap A (Localization.Away d) (g i))) (MvPolynomial.C t)) = _
      rw [MvPolynomial.aeval_C, MvPolynomial.eval₂Hom_C]
      rw [IsScalarTower.algebraMap_apply R A (Localization.Away d), e.commutes]
      change r (a t) = _
      change ((X.hom.appLE ⊤ U.1 le_top) ≫ X.left.presheaf.map (homOfLE hV).op) t = _
      rw [Scheme.Hom.appLE_map]
    · intro i
      change e ((MvPolynomial.aeval (R := R)
        (fun i => algebraMap A (Localization.Away d) (g i))) (MvPolynomial.X i)) = _
      rw [MvPolynomial.aeval_X, MvPolynomial.eval₂Hom_X', e.commutes]
      rfl
  refine ⟨V, hV, ?_, ?_⟩
  · apply (Point.mem_overOpen_basicOpen_iff_evaluate_ne_zero d p hp).mpr
    rw [heval] at hd
    exact hd
  · rw [← hcomp]
    exact RingHom.Etale.respectsIso.1 _ e.toRingEquiv hloc

/-- Etale coordinates restrict along an inclusion of affine opens with the actual section restriction map. -/
theorem s2v_l1b_affine_coordinate_restriction
    (X : Over (Spec ↧ℂ)) (U V : X.left.affineOpens) (hV : V.1 ≤ U.1)
    {ι : Type} (f : ι → Γ(X.left, U))
    (hEt : (MvPolynomial.eval₂Hom (X.hom.appLE ⊤ U.1 le_top).hom f).Etale) :
    (MvPolynomial.eval₂Hom (X.hom.appLE ⊤ V.1 le_top).hom
      (fun i => (X.left.presheaf.map (homOfLE hV).op).hom (f i))).Etale := by
  let r := (X.left.presheaf.map (homOfLE hV).op).hom
  have hr : r.Etale := by
    have H := HasRingHomProperty.appLE (P := @Etale) (𝟙 X.left) inferInstance U V
      (show V.1 ≤ (𝟙 X.left) ⁻¹ᵁ U.1 from hV)
    simpa only [Scheme.Hom.appLE, Scheme.Hom.id_app, Category.id_comp] using H
  have heq : r.comp (MvPolynomial.eval₂Hom (X.hom.appLE ⊤ U.1 le_top).hom f) =
      MvPolynomial.eval₂Hom (X.hom.appLE ⊤ V.1 le_top).hom (fun i => r (f i)) := by
    apply MvPolynomial.ringHom_ext
    · intro t
      rw [MvPolynomial.eval₂Hom_C, RingHom.comp_apply, MvPolynomial.eval₂Hom_C]
      change ((X.hom.appLE ⊤ U.1 le_top) ≫ X.left.presheaf.map (homOfLE hV).op) t = _
      rw [Scheme.Hom.appLE_map]
    · intro i
      rw [MvPolynomial.eval₂Hom_X', RingHom.comp_apply, MvPolynomial.eval₂Hom_X']
  rw [← heq]
  exact RingHom.Etale.stableUnderComposition _ _ hEt hr

end HodgeLean.Foundations.Program
