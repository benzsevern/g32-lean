import HodgeLean.Foundations.Program.SchoenTowerL1bRotationCharacterFraction
import HodgeLean.Foundations.Program.SchoenTowerL1bRotationBinomial

noncomputable section
set_option maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- A specified character of the actual base-linear field symmetry gives rational
binomial data in the represented stalk, before any prime is selected. -/
theorem s2v_l1b_rotation_stalk_character
    (B : Over (Spec (CommRingCat.of ℂ))) [IsIntegral B.left]
    {K : Type} [Field K] (x : B.left) (κ : B.left.functionField ⟶ CommRingCat.of K)
    (R : Type) [CommRing R] [IsDomain R]
    (eR : R ≃+* B.left.presheaf.stalk x)
    (m : ℕ)
    (hfield : letI := κ.hom.toAlgebra
      Module.Finite B.left.functionField K ∧ IsGalois B.left.functionField K ∧
      Module.finrank B.left.functionField K = m)
    (τ : letI := κ.hom.toAlgebra; K ≃ₐ[B.left.functionField] K)
    (hτ : orderOf τ = m)
    (ζ : B.left.functionField) (hζ : IsPrimitiveRoot ζ m) :
    let ρ := (s2v_l1b_kval_stalkMap B.left x κ).comp eR.toRingHom
    ∃ (t : K) (a b : R), a ≠ 0 ∧ b ≠ 0 ∧ t ≠ 0 ∧
      Subfield.closure (Set.range ρ ∪ {t}) = ⊤ ∧
      t ^ m = ρ a / ρ b ∧ τ t = κ ζ * t := by
  letI := κ.hom.toAlgebra
  obtain ⟨hfinite, hgalois, hdegree⟩ := hfield
  letI := hfinite
  letI := hgalois
  letI : Algebra R B.left.functionField :=
    ((algebraMap (B.left.presheaf.stalk x) B.left.functionField).comp eR.toRingHom).toAlgebra
  letI : IsFractionRing R B.left.functionField :=
    IsFractionRing.of_ringEquiv_left eR (fun _ => rfl)
  obtain ⟨t, a, b, ha, hb, ht, hgen, hpow, heigen⟩ :=
    s2v_l1b_rotation_character_fraction (R := R) τ
      (hτ.trans hdegree.symm) (hdegree.symm ▸ hζ)
  refine ⟨t, a, b, ha, hb, ht, hgen, ?_, ?_⟩
  · rw [hdegree] at hpow
    exact hpow
  · exact heigen

end HodgeLean.Foundations.Program
