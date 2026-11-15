import HodgeLean.Foundations.Program.SchoenTowerI2aStrictTransformSupport

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- Every ideal of an actual reduced strict transform remains radical on an
open scheme chart.
Source: Mathlib, `Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion`,
`PrimeSpectrum.isRadical_vanishingIdeal` and `Ideal.IsRadical.comap`. -/
theorem s2v_i2a_strict_transform_open_ideal_radical
    {U X Y : Scheme} (u : U ⟶ X) [IsOpenImmersion u] (f : X ⟶ Y)
    (D K : Y.IdealSheafData) (V : U.affineOpens) :
    (((s2c_strictTransform f D K).comap u).ideal V).IsRadical := by
  rw [Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion]
  unfold s2c_strictTransform
  rw [Scheme.IdealSheafData.vanishingIdeal_ideal]
  apply Ideal.IsRadical.comap
  exact PrimeSpectrum.isRadical_vanishingIdeal _

/-- A reduced principal support calculation identifies the actual strict
transform ideal on an affine open chart.
Source: Mathlib, `Scheme.IdealSheafData.vanishingIdeal_support` and
`Scheme.IdealSheafData.equivOfIsAffine`. -/
theorem s2v_i2a_strict_transform_ideal_on_open
    {U X Y : Scheme} [IsAffine U] (u : U ⟶ X) [IsOpenImmersion u] (f : X ⟶ Y)
    (D K : Y.IdealSheafData) (J : Ideal Γ(U, ⊤)) (hJ : J.IsRadical)
    (hsupport : u ⁻¹' ((s2c_strictTransform f D K).support : Set X) =
      U.zeroLocus (U := ⊤) (J : Set Γ(U, ⊤))) :
    ((s2c_strictTransform f D K).comap u).ideal ⟨⊤, isAffineOpen_top U⟩ = J := by
  let T := (s2c_strictTransform f D K).comap u
  have hsup : T.support = (Scheme.IdealSheafData.ofIdealTop J).support := by
    ext p
    change p ∈ ((T.support : Set U)) ↔ p ∈ _
    rw [Scheme.IdealSheafData.support_comap]
    change p ∈ u ⁻¹' ((s2c_strictTransform f D K).support : Set X) ↔ p ∈ _
    rw [hsupport]
    rfl
  have H := congrArg (fun Z => (Scheme.IdealSheafData.vanishingIdeal Z).ideal
    ⟨⊤, isAffineOpen_top U⟩) hsup
  rw [Scheme.IdealSheafData.vanishingIdeal_support,
    Scheme.IdealSheafData.vanishingIdeal_support] at H
  change (T.ideal ⟨⊤, isAffineOpen_top U⟩).radical =
    ((Scheme.IdealSheafData.ofIdealTop J).ideal ⟨⊤, isAffineOpen_top U⟩).radical at H
  have hT := s2v_i2a_strict_transform_open_ideal_radical u f D K ⟨⊤, isAffineOpen_top U⟩
  have htop : (Scheme.IdealSheafData.ofIdealTop J).ideal ⟨⊤, isAffineOpen_top U⟩ = J :=
    Scheme.IdealSheafData.equivOfIsAffine.apply_symm_apply J
  rw [hT.radical, htop, hJ.radical] at H
  exact H

end HodgeLean.Foundations.Program
