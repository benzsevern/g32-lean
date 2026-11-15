import HodgeLean.Foundations.Program.SchoenTowerI2bChartScheme
import HodgeLean.Foundations.Program.SchoenTowerI2bChartIdeals

/-! Factoring actual affine neighborhoods through a selected blowup chart.
HC no distance; AV milestone no distance. -/
noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry Polynomial
namespace HodgeLean.Foundations.Program

/-- A ratio of the selected sections factors the actual affine map through its algebraic chart.
Source: the polynomial quotient mapping property and naturality of the affine spectrum isomorphism. -/
theorem s2v_i2b_affine_chart_ratio_factor
    {V U : Scheme} [IsAffine V] [IsAffine U] (t : V ⟶ U)
    (u v : Γ(U, ⊤)) (s : Γ(V, ⊤))
    (hs : t.appTop.hom u = s * t.appTop.hom v) :
    let Q := s2v_L1bChart u v
    let q : Polynomial Γ(U, ⊤) →+* Q := Ideal.Quotient.mk _
    let c := q.comp Polynomial.C
    ∃ l : V ⟶ Spec (CommRingCat.of Q),
      l ≫ (Spec.map (CommRingCat.ofHom c) ≫ U.isoSpec.inv) = t := by
  dsimp only
  let Q := s2v_L1bChart u v
  let q : Polynomial Γ(U, ⊤) →+* Q := Ideal.Quotient.mk _
  let c := q.comp Polynomial.C
  obtain ⟨φ, hφ, _⟩ := s2v_l1b_chart_lift u v t.appTop.hom s hs
  have hc : φ.comp c = t.appTop.hom := by
    change φ.comp (q.comp Polynomial.C) = _
    rw [← RingHom.comp_assoc, hφ]
    ext a
    change (Polynomial.C a).eval₂ t.appTop.hom s = t.appTop.hom a
    exact Polynomial.eval₂_C t.appTop.hom s
  refine ⟨V.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom φ), ?_⟩
  have hcat : CommRingCat.ofHom c ≫ CommRingCat.ofHom φ = t.appTop := by
    exact CommRingCat.hom_ext hc
  rw [Category.assoc, ← Category.assoc (Spec.map (CommRingCat.ofHom φ)),
    ← Spec.map_comp, hcat, ← Category.assoc, Scheme.isoSpec_hom_naturality,
    Category.assoc, Iso.hom_inv_id, Category.comp_id]

end HodgeLean.Foundations.Program
