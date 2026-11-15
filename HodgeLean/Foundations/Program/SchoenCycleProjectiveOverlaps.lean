import HodgeLean.Foundations.Program.SchoenCycleProjectiveChartMaps

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.ComplexProjectiveSpace MvPolynomial HomogeneousLocalization
attribute [local instance] MvPolynomial.gradedAlgebra
namespace HodgeLean.Foundations.Program

/-- The normalized residue equations obey the actual transition formula on chart overlaps.
Source: Schoen (1988), Lemma 2.3(vi), printed pp. 13–14; Lemma 2.4 proof, printed p. 15. -/
theorem s2e_chart_overlap_coordinates {k : ℕ} (i j l : Fin (k + 1)) :
    (pullback.snd (s2e_s2b_chart i) (s2e_s2b_chart j) ≫
      Spec.map (CommRingCat.ofHom (s2e_s2b_chartHom j))).appTop.hom
        ((Scheme.ΓSpecIso _).inv.hom (chartCoordinate j l)) =
      (pullback.snd (s2e_s2b_chart i) (s2e_s2b_chart j) ≫
        Spec.map (CommRingCat.ofHom (s2e_s2b_chartHom j))).appTop.hom
          ((Scheme.ΓSpecIso _).inv.hom (chartCoordinate j i)) *
        (pullback.fst (s2e_s2b_chart i) (s2e_s2b_chart j) ≫
          Spec.map (CommRingCat.ofHom (s2e_s2b_chartHom i))).appTop.hom
          ((Scheme.ΓSpecIso _).inv.hom (chartCoordinate i l)) := by
  let F := pullback.fst (s2e_s2b_chart i) (s2e_s2b_chart j) ≫
    Spec.map (CommRingCat.ofHom (s2e_s2b_chartHom i))
  let G := pullback.snd (s2e_s2b_chart i) (s2e_s2b_chart j) ≫
    Spec.map (CommRingCat.ofHom (s2e_s2b_chartHom j))
  have hw : F ≫ HodgeLean.Foundations.g3c_chartι k i =
      G ≫ HodgeLean.Foundations.g3c_chartι k j := by
    have h := congrArg (fun f => f ≫ pullback.snd
      (terminal.from (Spec ↧ℂ)) (terminal.from (Proj (UniversalGrading k))))
      (pullback.condition (f := s2e_s2b_chart i) (g := s2e_s2b_chart j))
    simpa only [F, G, s2e_s2b_chart, Category.assoc, pullback.lift_snd,
      HodgeLean.Foundations.g3c_chartι] using h
  let t := pullback.lift F G hw
  have h := congrArg (fun s => t.appTop.hom s)
    (HodgeLean.Foundations.g3c_overlap_coord k i j l)
  simp only [map_mul] at h
  change (t ≫ pullback.snd _ _).appTop.hom _ =
    (t ≫ pullback.snd _ _).appTop.hom _ * (t ≫ pullback.fst _ _).appTop.hom _ at h
  simp only [t, pullback.lift_snd, pullback.lift_fst] at h
  exact h

end HodgeLean.Foundations.Program
