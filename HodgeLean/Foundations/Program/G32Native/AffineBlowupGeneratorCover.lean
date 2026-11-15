import HodgeLean.Foundations.Program.G32Native.BlowupGeneratorCover

/-! Affine blow-up covers indexed by a chosen list of generators. -/
noncomputable section
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- The indexed generator charts form an affine open cover of the affine blow-up. -/
def g32l4_affine_blowUp_generatorCover {R K : Type} [CommRing R]
    (I : Ideal R) (g : K → I)
    (hg : Ideal.span (Set.range (fun k => (g k : R))) = I) :
    (affineBlowUp I).AffineOpenCover where
  I₀ := K
  X k := .of (affineBlowUpAlgebra I (g k))
  f k := affineBlowUp.chart I (g k)
  idx x := (g32l4_affine_blowUp_generator_chart_covers I g hg x).choose
  covers x := (g32l4_affine_blowUp_generator_chart_covers I g hg x).choose_spec

end HodgeLean.Foundations.Program
