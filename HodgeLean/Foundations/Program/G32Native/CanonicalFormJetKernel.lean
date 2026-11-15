import HodgeLean.Foundations.Program.G32Native.CanonicalAbelDifferentialDefs
import HodgeLean.Foundations.Program.SchoenCycleU1Variation

/-! # The form line detected by canonical divisor jets -/
noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Manifold Filter Topology
open scoped ContDiff
namespace HodgeLean.Foundations.Program.G32Native
attribute [local instance] b4cov_sphChartedSpace b4cov_sph_isManifold

/-- A holomorphic form vanishing to the canonical multiplicities belongs to the original form line. -/
theorem canonical_form_proportional_of_local_orders (G : CanonicalAbelGeometry)
    (θ δ : b3_HolForm (Fin 1 → ℂ) (AlgebraicGeometry.ComplexPoint G.Z)) (hθ : θ ≠ 0)
    (horder : ∀ p : AlgebraicGeometry.ComplexPoint G.Z, meromorphicOrderAt
        (HurwitzPrymRR_loc (Module.finrank_fin_fun (n := 1) ℂ) θ p) 0 ≤
      meromorphicOrderAt
        (HurwitzPrymRR_loc (Module.finrank_fin_fun (n := 1) ℂ) δ p) 0) :
    ∃ c : ℂ, δ = c • θ := by
  by_cases hδ : δ = 0
  · exact ⟨0, by rw [hδ, zero_smul]⟩
  let hE := Module.finrank_fin_fun (n := 1) ℂ
  let v : b4c_MeroForm (Fin 1 → ℂ) (AlgebraicGeometry.ComplexPoint G.Z) hE :=
    ⟨δ, RiemannRochAna_hol_isMeroForm hE δ⟩
  let w : b4c_MeroForm (Fin 1 → ℂ) (AlgebraicGeometry.ComplexPoint G.Z) hE :=
    ⟨θ, RiemannRochAna_hol_isMeroForm hE θ⟩
  have hv : (v : TangentBundle 𝓘(ℂ, Fin 1 → ℂ) (AlgebraicGeometry.ComplexPoint G.Z) → ℂ) ≠ 0 :=
    fun hz => hδ (Subtype.ext hz)
  have hw : (w : TangentBundle 𝓘(ℂ, Fin 1 → ℂ) (AlgebraicGeometry.ComplexPoint G.Z) → ℂ) ≠ 0 :=
    fun hz => hθ (Subtype.ext hz)
  let p₀ : AlgebraicGeometry.ComplexPoint G.Z := Classical.choice inferInstance
  have hgv : ∃ p, meromorphicOrderAt (HurwitzPrymRR_loc hE v p) 0 ≠ ⊤ :=
    ⟨p₀, RiemannRochAna_hol_order_ne_top hE δ hδ p₀⟩
  have hgw : ∃ p, meromorphicOrderAt (HurwitzPrymRR_loc hE w p) 0 ≠ ⊤ :=
    ⟨p₀, RiemannRochAna_hol_order_ne_top hE θ hθ p₀⟩
  have hnonneg (p : AlgebraicGeometry.ComplexPoint G.Z) :
      0 ≤ meromorphicOrderAt (fun z => HurwitzPrymRR_loc hE v p z / HurwitzPrymRR_loc hE w p z) 0 := by
    have hvn := RiemannRochAna_hol_order_ne_top hE δ hδ p
    have hwn := RiemannRochAna_hol_order_ne_top hE θ hθ p
    lift meromorphicOrderAt (HurwitzPrymRR_loc hE v p) 0 to ℤ using hvn with a ha
    lift meromorphicOrderAt (HurwitzPrymRR_loc hE w p) 0 to ℤ using hwn with b hb
    have hab : b ≤ a := by
      have ho := horder p
      change meromorphicOrderAt (HurwitzPrymRR_loc hE w p) 0 ≤
        meromorphicOrderAt (HurwitzPrymRR_loc hE v p) 0 at ho
      rw [← ha, ← hb] at ho
      exact_mod_cast ho
    change 0 ≤ meromorphicOrderAt (HurwitzPrymRR_loc hE v p / HurwitzPrymRR_loc hE w p) 0
    rw [meromorphicOrderAt_div (v.property.2 p) (w.property.2 p), ← ha, ← hb]
    exact_mod_cast sub_nonneg.mpr hab
  let F : b4c_MeroFun (Fin 1 → ℂ) (AlgebraicGeometry.ComplexPoint G.Z) :=
    ⟨b4c_formRatio (hE := hE) v w, b4c_formRatio_isMeroFun_aux hE v w hv hw hgv hgw⟩
  have hfinite (p : AlgebraicGeometry.ComplexPoint G.Z) : F p ≠ OnePoint.infty := by
    change b4c_formRatio (hE := hE) v w p ≠ OnePoint.infty
    simp only [b4c_formRatio, not_lt_of_ge (hnonneg p), ite_false]
    split_ifs <;> exact OnePoint.coe_ne_infty _
  have hconstant (p q : AlgebraicGeometry.ComplexPoint G.Z) : F p = F q := by
    by_contra hpq
    obtain ⟨r, hr⟩ := b4cov_surjective (by simp : Module.finrank ℂ ℂ = 1)
      F F.property.1 ⟨p, q, hpq⟩ OnePoint.infty
    exact hfinite r hr
  obtain ⟨c, hc⟩ := OnePoint.ne_infty_iff_exists.mp (hfinite p₀)
  have hratio (p : AlgebraicGeometry.ComplexPoint G.Z) :
      b4c_formRatio (hE := hE) v w p = (c : OnePoint ℂ) :=
    (hconstant p p₀).trans hc.symm
  refine ⟨c, ?_⟩
  apply RiemannRochEichler_holForm_germ_ext hE
  intro p
  exact s2e_constant_formRatio_germ hE v w hgv hgw c hratio p

#print axioms canonical_form_proportional_of_local_orders
end HodgeLean.Foundations.Program.G32Native
