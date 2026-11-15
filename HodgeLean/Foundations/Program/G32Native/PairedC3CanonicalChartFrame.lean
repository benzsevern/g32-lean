import HodgeLean.Foundations.Program.G32Native.PairedC3CanonicalChartBasis
import HodgeLean.Foundations.Program.G32Native.PairedC3ChartGeneratorFrame
import HodgeLean.Foundations.Program.G32Native.PairedC3CanonicalChartAffineModule
import HodgeLean.Foundations.Program.G32Native.PairedC3OpenFrameTransfer

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program.G32Native
open HodgeLean.Foundations.Program
attribute [local instance] Classical.propDecidable MvPolynomial.gradedAlgebra

/-- The original canonical conormal classes frame every affine chart subopen. -/
theorem paired_c3_canonical_affine_chart_frame {n k : ℕ}
    (e : Fin (k + 1) ↪ Fin (n + 1)) (i : Fin (k + 1))
    (W : (Spec (pairedC3ChartRing k i)).Opens) :
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
    let hq : Function.Surjective q := paired_c3_coordinate_chart_map_surjective e i
    let B : Module.Basis {j : Fin (n + 1) // j ∉ Set.range e}
        (R ⧸ RingHom.ker q.hom) (RingHom.ker q.hom).Cotangent :=
      pairedC3OriginalChartKernelBasis e i
    let x : {j : Fin (n + 1) // j ∉ Set.range e} → RingHom.ker q.hom :=
      fun j => ⟨ProjSpace.ratio ℂ n (e i) j.val,
        paired_c3_coordinate_chart_map_discarded_ratio e i j.val j.property⟩
    let hx : ∀ j, B j = (RingHom.ker q.hom).toCotangent (x j) :=
      paired_c3_original_chart_kernel_basis_apply e i
    let s : {j : Fin (n + 1) // j ∉ Set.range e} → Γ(Conormal.idealModule p, U) :=
      fun j => pairedC3ProjectiveIdealGenerator e i j.val j.property
    let hs : ∀ j, s2e_affine_ideal_sections_equiv R S q
        (pairedC3AffineChartIdealSection p R S q a b h U ha (s j)) = x j :=
      paired_c3_canonical_affine_ideal_generator_value e i
    let D : (Scheme.Modules.pullback b).obj (Conormal.sheaf p) ≅
        Conormal.sheaf (Spec.map q) := pairedC3CanonicalChartConormalIso e i
    let hD : D.hom = Conormal.comparisonMap p (Spec.map q) a b h :=
      paired_c3_canonical_chart_iso_hom e i
    Function.Bijective (pairedC3FiniteFrameSynthesis
      (fun j => pairedC3ConormalChartSourceClass p b U V hv hb (s j)) W le_top) := by
  intro p R S q a b h U V hv ha hb hq B x hx s hs D hD
  exact paired_c3_chart_generator_frame p R S q a b h U V hv ha hb hq B x hx s hs D hD W

#print axioms paired_c3_canonical_affine_chart_frame
end HodgeLean.Foundations.Program.G32Native
