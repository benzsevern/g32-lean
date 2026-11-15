import HodgeLean.Foundations.Program.SchoenTowerI2bChartScheme
import HodgeLean.Foundations.Program.SchoenTowerI2bUnpairedChartDensity

/-! Actual support calculations for the algebraic blowup charts.
HC no distance; AV milestone no distance. -/
noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry Polynomial
namespace HodgeLean.Foundations.Program

/-- The support pulled into a canonical affine chart is the zero locus of the extended ideal.
Source: affine support coordinates and the adjunction between extension and contraction of ideals. -/
theorem s2v_i2b_affine_chart_preimage_support
    (U : Scheme) [IsAffine U] (I : U.IdealSheafData)
    {A : Type*} [CommRing A] (c : Γ(U, ⊤) →+* A) :
    (Spec.map (CommRingCat.ofHom c) ≫ U.isoSpec.inv) ⁻¹' (I.support : Set U) =
      PrimeSpectrum.zeroLocus (Ideal.map c (I.ideal ⟨⊤, isAffineOpen_top U⟩) : Set A) := by
  change (PrimeSpectrum.comap c) ⁻¹' (U.isoSpec.inv ⁻¹' (I.support : Set U)) = _
  rw [s2e_affine_support_in_spectrum]
  ext p
  change I.ideal ⟨⊤, isAffineOpen_top U⟩ ≤ Ideal.comap c p.asIdeal ↔
    Ideal.map c (I.ideal ⟨⊤, isAffineOpen_top U⟩) ≤ p.asIdeal
  exact Ideal.map_le_iff_le_comap.symm

/-- The actual unpaired support pulls into the canonical chart as the closure of its nonexceptional part.
Source: extended-ideal support coordinates and density for a regular branch triple. -/
theorem s2v_i2b_actual_blowup_chart_support_density
    (U : Scheme) [IsAffine U] (D K : U.IdealSheafData) (u v z : Γ(U, ⊤))
    (hD : D.ideal ⟨⊤, isAffineOpen_top U⟩ = Ideal.span {z})
    (hK : K.ideal ⟨⊤, isAffineOpen_top U⟩ = Ideal.span {u, v})
    (hreg : RingTheory.Sequence.IsWeaklyRegular Γ(U, ⊤) [z, v, u]) :
    let q : Polynomial Γ(U, ⊤) →+* s2v_L1bChart u v := Ideal.Quotient.mk _
    let f := Spec.map (CommRingCat.ofHom (q.comp Polynomial.C)) ≫ U.isoSpec.inv
    closure (f ⁻¹' ((D.support : Set U) \ (K.support : Set U))) =
      f ⁻¹' (D.support : Set U) := by
  dsimp only
  let q : Polynomial Γ(U, ⊤) →+* s2v_L1bChart u v := Ideal.Quotient.mk _
  let c := q.comp Polynomial.C
  have hDmap : Ideal.map c (D.ideal ⟨⊤, isAffineOpen_top U⟩) = Ideal.span {q (C z)} := by
    rw [hD, Ideal.map_span, Set.image_singleton]
    rfl
  have hKmap : Ideal.map c (K.ideal ⟨⊤, isAffineOpen_top U⟩) = Ideal.span {q (C v)} := by
    rw [hK, Ideal.map_span, Set.image_pair]
    exact s2v_l1b_chart_centre_principal u v
  rw [Set.preimage_sdiff, s2v_i2b_affine_chart_preimage_support U D c,
    s2v_i2b_affine_chart_preimage_support U K c, hDmap, hKmap]
  simp only [PrimeSpectrum.zeroLocus_span]
  change closure (PrimeSpectrum.zeroLocus ({q (C z)} : Set (s2v_L1bChart u v)) ∩
    (PrimeSpectrum.zeroLocus ({q (C v)} : Set (s2v_L1bChart u v)))ᶜ) = _
  rw [← PrimeSpectrum.basicOpen_eq_zeroLocus_compl]
  exact s2v_i2b_unpaired_algebraic_chart_density u v z hreg

end HodgeLean.Foundations.Program
