import HodgeLean.Foundations.Program.G32Native.CanonicalAbelDescent
import HodgeLean.Foundations.Curves.AbelAdapter.StageFour.PrincipalPeriods

/-! # The original Abel class of canonical divisors -/
noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open HodgeLean.Adapters HodgeLean.Foundations.Curves.AbelAdapter
open HodgeLean.Foundations.Curves.AbelAdapter.StageFour
open scoped BigOperators Topology Manifold ContDiff
namespace HodgeLean.Foundations.Program.G32Native

variable {E C : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [FiniteDimensional ℂ E] [TopologicalSpace C] [ChartedSpace E C]
  [IsManifold 𝓘(ℂ, E) ω C] [T2Space C] [CompactSpace C] [ConnectedSpace C]

/-- The actual ratio of two nonzero meromorphic forms is not the zero function. -/
theorem canonical_form_ratio_nonzero (hE : Module.finrank ℂ E = 1)
    (v w : b4c_MeroForm E C hE)
    (hv : (v : TangentBundle 𝓘(ℂ, E) C → ℂ) ≠ 0)
    (hw : (w : TangentBundle 𝓘(ℂ, E) C → ℂ) ≠ 0)
    (hgv : ∃ x, meromorphicOrderAt (HurwitzPrymRR_loc hE v x) 0 ≠ ⊤)
    (hgw : ∃ x, meromorphicOrderAt (HurwitzPrymRR_loc hE w x) 0 ≠ ⊤) :
    ∃ x, b4c_formRatio (hE := hE) v w x ≠ (0 : ℂ) := by
  classical
  let S := (b4c_divForm (hE := hE) v).support ∪ (b4c_divForm (hE := hE) w).support
  let x₀ := Classical.choose hgv
  letI := RiemannRochAna_punctured_neBot hE x₀
  obtain ⟨x, hx⟩ := (RiemannRochAna_punctured_eventually_not_mem_finset S x₀).exists
  have hvo : meromorphicOrderAt (HurwitzPrymRR_loc hE v x) 0 = 0 := by
    rw [← RiemannRochAna_coe_divForm_apply hE v
      (b4c_meroForm_orderSupport_finite_aux hE v) x
      (RiemannRochAna_meroForm_order_ne_top hE v hv hgv x),
      Finsupp.notMem_support_iff.mp (fun h => hx (Finset.mem_union_left _ h))]
    rfl
  have hwo : meromorphicOrderAt (HurwitzPrymRR_loc hE w x) 0 = 0 := by
    rw [← RiemannRochAna_coe_divForm_apply hE w
      (b4c_meroForm_orderSupport_finite_aux hE w) x
      (RiemannRochAna_meroForm_order_ne_top hE w hw hgw x),
      Finsupp.notMem_support_iff.mp (fun h => hx (Finset.mem_union_right _ h))]
    rfl
  have hq : meromorphicOrderAt
      (fun z => HurwitzPrymRR_loc hE v x z / HurwitzPrymRR_loc hE w x z) 0 = 0 := by
    rw [b4c_formRatio_germ_order, hvo, hwo]
    rfl
  refine ⟨x, ?_⟩
  simp only [b4c_formRatio, hq, lt_self_iff_false, ite_false, ite_true]
  exact OnePoint.coe_injective.ne
    (((v.property.2 x).div (w.property.2 x)).meromorphicTrailingCoeffAt_ne_zero
      (by
        change meromorphicOrderAt (fun z => HurwitzPrymRR_loc hE v x z /
          HurwitzPrymRR_loc hE w x z) 0 ≠ ⊤
        rw [hq]
        simp))

/-- All nonzero canonical form divisors have the same original Abel sum. -/
theorem canonical_divisor_abel_sum_eq (hE : Module.finrank ℂ E = 1) (p : C)
    (θ η : b3_HolForm E C) (hθ : θ ≠ 0) (hη : η ≠ 0) :
    weightedSum (analyticAbel hE p) (b4c_divForm (hE := hE) θ) =
      weightedSum (analyticAbel hE p) (b4c_divForm (hE := hE) η) := by
  let v : b4c_MeroForm E C hE := ⟨θ, RiemannRochAna_hol_isMeroForm hE θ⟩
  let w : b4c_MeroForm E C hE := ⟨η, RiemannRochAna_hol_isMeroForm hE η⟩
  have hv : (v : TangentBundle 𝓘(ℂ, E) C → ℂ) ≠ 0 := fun hz => hθ (Subtype.ext hz)
  have hw : (w : TangentBundle 𝓘(ℂ, E) C → ℂ) ≠ 0 := fun hz => hη (Subtype.ext hz)
  have hgv : ∃ x, meromorphicOrderAt (HurwitzPrymRR_loc hE v x) 0 ≠ ⊤ :=
    ⟨p, RiemannRochAna_hol_order_ne_top hE θ hθ p⟩
  have hgw : ∃ x, meromorphicOrderAt (HurwitzPrymRR_loc hE w x) 0 ≠ ⊤ :=
    ⟨p, RiemannRochAna_hol_order_ne_top hE η hη p⟩
  let f : b4c_MeroFun E C := ⟨b4c_formRatio (hE := hE) v w,
    b4c_formRatio_isMeroFun_aux hE v w hv hw hgv hgw⟩
  have hd := b4c_divForm_sub hE v w hv hw hgv hgw
  have hs := analyticPrincipalPeriods hE p f (canonical_form_ratio_nonzero hE v w hv hw hgv hgw)
  apply sub_eq_zero.mp
  change weightedSum (analyticAbel hE p) (b4c_divForm (hE := hE) v) -
    weightedSum (analyticAbel hE p) (b4c_divForm (hE := hE) w) = 0
  rw [← map_sub, hd]
  exact hs

#print axioms canonical_form_ratio_nonzero
#print axioms canonical_divisor_abel_sum_eq
end HodgeLean.Foundations.Program.G32Native
