import HodgeLean.Foundations.Program.SchoenCycleSectionAlongNativeChart
import HodgeLean.Foundations.Program.SchoenCycleAnalyticCoordinateGerms

/-! # Native function pullbacks with exact coordinate products -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 200000
open CategoryTheory AlgebraicGeometry Filter Topology
open HodgeLean.Foundations.AnalyticDivisorAlgebraic11
namespace HodgeLean.Foundations.Program

/-- An analytic native function with an exact scalar coordinate-product evaluation has that reduced product as its analytic pullback up to a unit.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.4, printed p. 15;
Gunning–Rossi, Analytic Functions of Several Complex Variables, II.B. -/
theorem s2e_native_function_pullback_product
    (B : Over (Spec ↧ℂ)) (n d : ℕ) [SmoothOfRelativeDimension d B.hom]
    (y : ComplexPoint B) (Q : (Fin n → ℂ) → ComplexPoint B)
    (hQ : Tendsto Q (𝓝 0) (𝓝 y)) (hQ0 : Q 0 = y)
    (hqa : AnalyticAt ℂ (fun z => ComplexPoint.localChart B d y (Q z)) 0)
    (E : ComplexPoint B → ℂ)
    (hE : AnalyticAt ℂ (fun z => E ((ComplexPoint.localChart B d y).symm
      (ComplexPoint.localChart B d y y + z))) 0)
    (S : Finset (Fin n)) (scalar : ℂ) (hscalar : scalar ≠ 0)
    (he : ∀ᶠ z in 𝓝 0, E (Q z) = scalar * ∏ i ∈ S, z i) :
    ∃ v : (AnalyticGermAt n 0)ˣ,
      s2e_analyticGermPullback
        (fun z => ComplexPoint.localChart B d y (Q z) - ComplexPoint.localChart B d y y)
        (hqa.sub analyticAt_const) (by rw [hQ0]; exact sub_self _)
        (⟨Filter.Germ.ofFun (fun z => E ((ComplexPoint.localChart B d y).symm
          (ComplexPoint.localChart B d y y + z))), _, hE, rfl⟩ : AnalyticGermAt d 0) =
          (∏ i ∈ S, s2e_analyticCoordinateGerm n i) * (v : AnalyticGermAt n 0) := by
  let K : AnalyticGermAt n 0 :=
    ⟨Filter.Germ.ofFun (fun _ => scalar), fun _ => scalar, analyticAt_const, rfl⟩
  obtain ⟨v, hv⟩ := (s2e_analyticGermAt_isUnit_iff K).mpr hscalar
  refine ⟨v, ?_⟩
  rw [hv]
  apply Subtype.ext
  change Filter.Germ.ofFun (fun z => E ((ComplexPoint.localChart B d y).symm
    (ComplexPoint.localChart B d y y + (ComplexPoint.localChart B d y (Q z) -
      ComplexPoint.localChart B d y y)))) = _
  have hprod : (∏ i ∈ S, s2e_analyticCoordinateGerm n i).val =
      Filter.Germ.ofFun (fun z : Fin n → ℂ => ∏ i ∈ S, z i) := by
    clear he
    induction S using Finset.induction_on with
    | empty => rfl
    | @insert i S hi ih =>
      simp only [Finset.prod_insert hi, Subring.coe_mul, ih]
      rfl
  change _ = (∏ i ∈ S, s2e_analyticCoordinateGerm n i).val * K.val
  rw [hprod]
  apply Filter.Germ.coe_eq.mpr
  let C := ComplexPoint.localChart B d y
  filter_upwards [he, hQ (C.open_source.mem_nhds
    (ComplexPoint.mem_localChart_source B d y))] with z hz hcz
  change E (C.symm (C y + (C (Q z) - C y))) = (∏ i ∈ S, z i) * scalar
  have hh : C y + (C (Q z) - C y) = C (Q z) := by abel
  rw [hh, C.left_inv hcz, hz, mul_comm]

end HodgeLean.Foundations.Program
