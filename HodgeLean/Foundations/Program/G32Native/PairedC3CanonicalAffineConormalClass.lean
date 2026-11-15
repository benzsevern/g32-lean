import HodgeLean.Foundations.Program.G32Native.PairedC3CanonicalChartObjects

noncomputable section
set_option maxHeartbeats 400000
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry MvPolynomial HomogeneousLocalization
namespace HodgeLean.Foundations.Program.G32Native
open HodgeLean.Foundations.Program
attribute [local instance] MvPolynomial.gradedAlgebra

/-- The natural chart conormal comparison keeps the canonical class of the
same transported original ideal generator. -/
theorem paired_c3_canonical_chart_conormal_generator {n k : ℕ}
    (e : Fin (k + 1) ↪ Fin (n + 1)) (i : Fin (k + 1))
    (j : {j : Fin (n + 1) // j ∉ Set.range e}) :
    let p := pairedC3PolynomialCoordinateInclusion (A := ℂ) e
    let R := pairedC3ChartRing n (e i)
    let S := pairedC3ChartRing k i
    let q : R ⟶ S := pairedC3ChartProjection e i
    let a : Spec R ⟶ pairedC3Proj n := pairedC3ChartInclusion n (e i)
    let b : Spec S ⟶ pairedC3Proj k := pairedC3ChartInclusion k i
    let h : b ≫ p = Spec.map q ≫ a := paired_c3_chart_diagram_commutes e i
    let U := ProjSpace.standardOpen ℂ n (e i)
    let V := ProjSpace.standardOpen ℂ k i
    let hv : p ⁻¹ᵁ U = V := paired_c3_chart_projection_preimage e i
    let ha : a ⁻¹ᵁ U = ⊤ := paired_c3_chart_inclusion_preimage n (e i)
    let hb : b ⁻¹ᵁ V = ⊤ := paired_c3_chart_inclusion_preimage k i
    let s : Γ(Conormal.idealModule p, U) :=
      pairedC3ProjectiveIdealGenerator e i j.val j.property
    (Conormal.comparisonMap p (Spec.map q) a b h).app ⊤
      (pairedC3ConormalChartSourceClass p b U V hv hb s) =
    pairedC3PullbackSection (Spec.map q) (Conormal.idealModule (Spec.map q)) ⊤
      (pairedC3AffineChartIdealSection p R S q a b h U ha s) := by
  intro p R S q a b h U V hv ha hb s
  exact paired_c3_conormal_chart_class_restricted p R S q a b h U V hv ha hb s

#print axioms paired_c3_canonical_chart_conormal_generator
end HodgeLean.Foundations.Program.G32Native
