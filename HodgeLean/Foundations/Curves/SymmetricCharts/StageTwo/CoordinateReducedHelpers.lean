import HodgeLean.Foundations.Curves.SymmetricCharts.StageTwo.CoordinateHelpers
import HodgeLean.Foundations.Program.SchoenCycleS2
import HodgeLean.Foundations.Program.SchoenTowerI2aEtaleReduced

/-! # Reduced coordinate intersections under etale transport

HC no distance; AV milestone no distance.
-/
noncomputable section
open CategoryTheory AlgebraicGeometry
open HodgeLean.Foundations.Program
namespace HodgeLean.Foundations.Curves.SymmetricCharts.StageTwo
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 200000

/-- Any selected family of polynomial variables generates a prime ideal.
Source: Polynomial coordinate elimination; Hartshorne, Algebraic Geometry, II.2.
HC no distance; AV milestone no distance.
-/
theorem coordinate_variable_sum_prime (n k : ℕ) (f : Fin k → Fin n) :
    (⨆ i : Fin k, Ideal.span {MvPolynomial.X (R := ℂ) (f i)}).IsPrime := by
  classical
  let T := Finset.univ.image f
  have hT : (MvPolynomial.X (R := ℂ)) '' (↑T : Set (Fin n)) =
      Set.range (fun i => MvPolynomial.X (R := ℂ) (f i)) := by
    ext p
    constructor
    · rintro ⟨j, hj, rfl⟩
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hj
      exact ⟨i, rfl⟩
    · rintro ⟨i, rfl⟩
      exact ⟨f i, Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩, rfl⟩
  rw [← Ideal.span_range_eq_iSup, ← hT]
  obtain ⟨E, _⟩ := s2e_chain_residue_coordinate_quotient n T
  letI : IsDomain (MvPolynomial (Fin n) ℂ ⧸
      Ideal.span ((MvPolynomial.X (R := ℂ)) '' (↑T : Set (Fin n)))) :=
    E.toRingEquiv.toMulEquiv.isDomain _
  exact (Ideal.Quotient.isDomain_iff_prime _).mp inferInstance

/-- A finite sum of coordinate hyperplane ideals stays radical after etale pullback.
Source: Hartshorne, Algebraic Geometry, II.5; etale extension of a prime ideal.
HC no distance; AV milestone no distance.
-/
theorem etale_coordinate_sum_radical (X : Scheme) [IsAffine X] (n k : ℕ)
    (f : Fin k → Fin n) (t : X ⟶ (affine n).left) [Etale t] :
    ((⨆ i, (coordinateIdeal n (f i)).comap t).ideal ⟨⊤, isAffineOpen_top X⟩).IsRadical := by
  let P := MvPolynomial (Fin n) ℂ
  letI : IsAffine (affine n).left := by change IsAffine (Spec ↧P); infer_instance
  let φ : P →+* Γ(X, ⊤) := t.appTop.hom.comp (Scheme.ΓSpecIso ↧P).inv.hom
  have ht : t.appTop.hom.Etale := HasRingHomProperty.appTop (P := @Etale) t inferInstance
  have hφ : φ.Etale := RingHom.Etale.stableUnderComposition _ _
    (RingHom.Etale.of_bijective (Scheme.ΓSpecIso ↧P).symm.commRingCatIsoToRingEquiv.bijective) ht
  letI : Algebra P Γ(X, ⊤) := φ.toAlgebra
  letI : Algebra.Etale P Γ(X, ⊤) := hφ
  let J : Ideal P := ⨆ i : Fin k, Ideal.span {MvPolynomial.X (f i)}
  letI : J.IsPrime := coordinate_variable_sum_prime n k f
  have H := s2v_i2a_etale_prime_extension_radical P Γ(X, ⊤) J
  convert H using 1
  simp only [Scheme.IdealSheafData.ideal_iSup, iSup_apply, s2e_affine_comap_ideal,
    coordinateIdeal, Scheme.IdealSheafData.ofIdealTop_ideal, homOfLE_refl, op_id]
  rw [(affine n).left.presheaf.map_id]
  simp only [CommRingCat.hom_id, Ideal.map_id, J, Ideal.map_iSup,
    Ideal.map_span, Set.image_singleton]
  rfl

end HodgeLean.Foundations.Curves.SymmetricCharts.StageTwo
