import HodgeLean.Foundations.Program.SchoenCycleS3CoordinateConormal
import HodgeLean.Foundations.Program.SchoenCycleS3ConormalCharts

/-! # Actual conormals for the residue chart ideals -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 100000
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexProjectiveSpace MvPolynomial
namespace HodgeLean.Foundations.Program

/-- The quotient immersion for the exact residue chart ideal has the required conormal rank. -/
theorem s2e_residueChartActualConormal_free {k : ℕ}
    (T : Finset (Fin (k + 1))) (i : Fin (k + 1)) (hi : i ∉ T) :
    let I := Ideal.map (Scheme.ΓSpecIso
        ↧(MvPolynomial {j : Fin (k + 1) // j ≠ i} ℂ)).hom.hom
      (((s2e_s2b_intersectionIdeal k T).comap (s2e_s2b_chart i)).ideal ⟨⊤, isAffineOpen_top _⟩)
    let Q := CommRingCat.of (MvPolynomial {j : Fin (k + 1) // j ≠ i} ℂ ⧸ I)
    Nonempty (s2c_conormal (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) ≅
      (SheafOfModules.free (R := (Spec Q).ringCatSheaf) (Fin T.card) : (Spec Q).Modules)) := by
  obtain ⟨e⟩ := s2e_residueChartCotangentSheaf_free T i hi
  exact ⟨s2e_affineQuotientConormalIso (R := CommRingCat.of
    (MvPolynomial {j : Fin (k + 1) // j ≠ i} ℂ)) _ ≪≫ e⟩

end HodgeLean.Foundations.Program
