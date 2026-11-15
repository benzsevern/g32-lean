import HodgeLean.Foundations.Program.SchoenTowerN2bPullbackCharts

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.ComplexProjectiveSpace HodgeLean.Foundations
namespace HodgeLean.Foundations.Program
attribute [local instance] MvPolynomial.gradedAlgebra

/-- The actual map from a source-chart overlap to the overlap of the standard target charts.
Source: Hartshorne, Algebraic Geometry, II.2.5. -/
def n2b_pullbackChartOverlapMap {X : Scheme.{0}} {n : ℕ}
    (ψ : X ⟶ g3c_P n) (i j : Fin (n + 1)) :
    pullback (n2b_pullbackChartι ψ i) (n2b_pullbackChartι ψ j) ⟶
      pullback (g3c_chartι n i) (g3c_chartι n j) :=
  pullback.lift
    (pullback.fst _ _ ≫ pullback.snd ψ (g3c_chartι n i))
    (pullback.snd _ _ ≫ pullback.snd ψ (g3c_chartι n j)) (by
      dsimp only [n2b_pullbackChartι]
      rw [Category.assoc, ← pullback.condition, ← Category.assoc,
        pullback.condition, Category.assoc, pullback.condition, Category.assoc])

/-- Normalized coordinates on the actual source charts obey the projective transition equation. -/
theorem n2b_pullbackChart_overlap_coord {X : Scheme.{0}} {n : ℕ}
    (ψ : X ⟶ g3c_P n) (i j k : Fin (n + 1)) :
    (pullback.snd (n2b_pullbackChartι ψ i) (n2b_pullbackChartι ψ j)).appTop.hom
        (n2b_pullbackChartCoord ψ j k) =
      (pullback.snd (n2b_pullbackChartι ψ i) (n2b_pullbackChartι ψ j)).appTop.hom
          (n2b_pullbackChartCoord ψ j i) *
        (pullback.fst (n2b_pullbackChartι ψ i) (n2b_pullbackChartι ψ j)).appTop.hom
          (n2b_pullbackChartCoord ψ i k) := by
  have hc {U V T : Scheme.{0}} (f : U ⟶ V) (g : V ⟶ T) (a : Γ(T, ⊤)) :
      f.appTop.hom (g.appTop.hom a) = (f ≫ g).appTop.hom a := by
    rw [Scheme.Hom.comp_appTop]
    rfl
  have h := congrArg (n2b_pullbackChartOverlapMap ψ i j).appTop.hom
    (g3c_overlap_coord n i j k)
  simp only [_root_.map_mul, hc, n2b_pullbackChartOverlapMap,
    pullback.lift_snd, pullback.lift_fst] at h
  simpa only [n2b_pullbackChartCoord, n2b_pullbackChart, n2b_pullbackChartι,
    Scheme.Hom.comp_appTop,
    CommRingCat.hom_comp, RingHom.comp_apply] using h

/-- The normalized transition coordinate is a unit on the actual chart intersection. -/
theorem n2b_pullbackChart_overlap_coordinate_isUnit
    {X : Scheme.{0}} {n : ℕ} (ψ : X ⟶ g3c_P n) (i j : Fin (n + 1)) :
    IsUnit ((pullback.snd (n2b_pullbackChartι ψ i)
      (n2b_pullbackChartι ψ j)).appTop.hom (n2b_pullbackChartCoord ψ j i)) := by
  let u := (pullback.snd (n2b_pullbackChartι ψ i)
    (n2b_pullbackChartι ψ j)).appTop.hom (n2b_pullbackChartCoord ψ j i)
  let v := (pullback.fst (n2b_pullbackChartι ψ i)
    (n2b_pullbackChartι ψ j)).appTop.hom (n2b_pullbackChartCoord ψ i j)
  have huv : u * v = 1 := by
    have h := n2b_pullbackChart_overlap_coord ψ i j j
    rw [n2b_pullbackChartCoord_self, map_one] at h
    exact h.symm
  exact ⟨Units.mkOfMulEqOne u v huv, rfl⟩

end HodgeLean.Foundations.Program
