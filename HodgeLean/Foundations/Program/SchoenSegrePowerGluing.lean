import HodgeLean.Foundations.Program.SchoenSegrePowerOverlaps

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MvPolynomial HomogeneousLocalization
open AlgebraicGeometry.ComplexProjectiveSpace HodgeLean.Foundations
open scoped BigOperators
namespace HodgeLean.Foundations.Program

attribute [local instance] MvPolynomial.gradedAlgebra

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The actual finite-factor Segre chart morphisms agree on their scheme overlaps. -/
theorem s2_segrePowerChartMap_compat (d n : ℕ) (a b : Fin n → Fin (d + 1)) :
    pullback.fst (s2_segrePowerChartι d n a) (s2_segrePowerChartι d n b) ≫
        s2_segrePowerChartMap d n a =
      pullback.snd (s2_segrePowerChartι d n a) (s2_segrePowerChartι d n b) ≫
        s2_segrePowerChartMap d n b := by
  classical
  let 𝒢 := homogeneousSubmodule (Fin n → Fin (d + 1)) (ULift.{0} ℤ)
  set p₁ := pullback.fst (s2_segrePowerChartι d n a) (s2_segrePowerChartι d n b)
  set p₂ := pullback.snd (s2_segrePowerChartι d n a) (s2_segrePowerChartι d n b)
  have h₁ : (HomogeneousIdeal.irrelevant 𝒢).toIdeal.map
      (p₁.appTop.hom.comp (s2_segrePowerSections d n a)) = ⊤ := by
    rw [← Ideal.map_map, s2_segrePowerSections_irrelevant, Ideal.map_top]
  have h₂ : (HomogeneousIdeal.irrelevant 𝒢).toIdeal.map
      (p₂.appTop.hom.comp (s2_segrePowerSections d n b)) = ⊤ := by
    rw [← Ideal.map_map, s2_segrePowerSections_irrelevant, Ideal.map_top]
  rw [s2_segrePowerChartMap, s2_segrePowerChartMap,
    spec_g3c_comp_fromOfGlobalSections_aux _ p₁ _ _ h₁,
    spec_g3c_comp_fromOfGlobalSections_aux _ p₂ _ _ h₂]
  set u := p₂.appTop.hom (∏ i, s2_segrePowerCoord d n b i (a i))
  set w := p₁.appTop.hom (∏ i, s2_segrePowerCoord d n a i (b i))
  have huw : u * w = 1 := by
    dsimp only [u, w]
    rw [map_prod, map_prod, ← Finset.prod_mul_distrib]
    apply Finset.prod_eq_one
    intro i _
    have H := (s2_segrePower_overlap_coord d n a b i (b i)).symm
    simpa only [s2_segrePowerCoord_self, map_one] using H
  refine spec_g3c_fromOfGlobalSections_unit_twist_aux _ _ _ h₁ h₂
    (Units.mkOfMulEqOne u w huw) (fun m r hr =>
      g3c_map_isHomogeneous_twist _ _ _ (fun c => ?_) hr)
  simp only [Units.val_mkOfMulEqOne, RingHom.comp_apply,
    s2_segrePowerSections_X, map_prod, u]
  calc
    _ = ∏ i, (p₂.appTop.hom (s2_segrePowerCoord d n b i (a i)) *
        p₁.appTop.hom (s2_segrePowerCoord d n a i (c i))) :=
      Finset.prod_congr rfl (fun i _ => s2_segrePower_overlap_coord d n a b i (c i))
    _ = _ := Finset.prod_mul_distrib

/-- The actual finite-factor integral Segre morphism obtained from its compatible affine chart morphisms. -/
def s2_segrePowerMap (d n : ℕ) :
    s2_segrePower d n ⟶ Proj (homogeneousSubmodule (Fin n → Fin (d + 1)) (ULift.{0} ℤ)) :=
  (s2_segrePowerCover d n).glueMorphisms (s2_segrePowerChartMap d n)
    (s2_segrePowerChartMap_compat d n)

/-- The actual global finite-factor Segre morphism retains its prescribed affine chart equations. -/
theorem s2_segrePowerChartι_map (d n : ℕ) (a : Fin n → Fin (d + 1)) :
    s2_segrePowerChartι d n a ≫ s2_segrePowerMap d n = s2_segrePowerChartMap d n a :=
  (s2_segrePowerCover d n).ι_glueMorphisms _ _ a

end HodgeLean.Foundations.Program
