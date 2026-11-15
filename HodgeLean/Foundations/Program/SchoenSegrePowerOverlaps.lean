import HodgeLean.Foundations.Program.SchoenSegrePowerSections

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MvPolynomial HomogeneousLocalization
open AlgebraicGeometry.ComplexProjectiveSpace HodgeLean.Foundations
namespace HodgeLean.Foundations.Program

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Each actual tuple-chart immersion has the prescribed equation with every projective factor projection. -/
theorem s2_segrePowerChartι_π (d n : ℕ) (a : Fin n → Fin (d + 1)) (i : Fin n) :
    s2_segrePowerChartι d n a ≫ s2_schemeProductπ n (fun _ => g3c_P d) i =
      s2_schemeProductπ n _ i ≫ g3c_chartι d (a i) :=
  s2_schemeProductMap_π n _ _ (fun i => g3c_chartι d (a i)) i

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Actual normalized factor coordinates have the expected multiplicative transition formula on tuple-chart overlaps. -/
theorem s2_segrePower_overlap_coord (d n : ℕ) (a b : Fin n → Fin (d + 1))
    (i : Fin n) (k : Fin (d + 1)) :
    (pullback.snd (s2_segrePowerChartι d n a) (s2_segrePowerChartι d n b)).appTop.hom
        (s2_segrePowerCoord d n b i k) =
      (pullback.snd (s2_segrePowerChartι d n a) (s2_segrePowerChartι d n b)).appTop.hom
          (s2_segrePowerCoord d n b i (a i)) *
        (pullback.fst (s2_segrePowerChartι d n a) (s2_segrePowerChartι d n b)).appTop.hom
          (s2_segrePowerCoord d n a i k) := by
  let p := pullback.fst (s2_segrePowerChartι d n a) (s2_segrePowerChartι d n b)
  let q := pullback.snd (s2_segrePowerChartι d n a) (s2_segrePowerChartι d n b)
  have hq : (p ≫ s2_schemeProductπ n _ i) ≫ g3c_chartι d (a i) =
      (q ≫ s2_schemeProductπ n _ i) ≫ g3c_chartι d (b i) := by
    have H := congrArg
      (fun f : pullback (s2_segrePowerChartι d n a) (s2_segrePowerChartι d n b) ⟶
        s2_segrePower d n => f ≫ s2_schemeProductπ n (fun _ => g3c_P d) i)
      (pullback.condition (f := s2_segrePowerChartι d n a) (g := s2_segrePowerChartι d n b))
    simpa only [Category.assoc, s2_segrePowerChartι_π] using H
  let l := pullback.lift (p ≫ s2_schemeProductπ n _ i)
    (q ≫ s2_schemeProductπ n _ i) hq
  have H := congrArg l.appTop.hom (g3c_overlap_coord d (a i) (b i) k)
  rw [map_mul] at H
  change (l ≫ pullback.snd _ _).appTop.hom _ =
    (l ≫ pullback.snd _ _).appTop.hom _ * (l ≫ pullback.fst _ _).appTop.hom _ at H
  simp only [l, pullback.lift_snd, pullback.lift_fst] at H
  exact H

end HodgeLean.Foundations.Program
