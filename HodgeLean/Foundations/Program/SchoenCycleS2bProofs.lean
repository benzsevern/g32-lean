import HodgeLean.Foundations.Program.SchoenCycleCoordinateImageIdeal
import HodgeLean.Foundations.Program.SchoenCycleResidueChartSum
import HodgeLean.Foundations.Program.SchoenCycleProjectiveOverlaps
import HodgeLean.Foundations.Program.SchoenCycleChartIdeals
import HodgeLean.Foundations.Program.SchoenCycleResidueHyperplanes
import HodgeLean.Foundations.Program.SchoenCycleResidueProjectivePoints

/-! # Projective residue intersections
Implication from distinct residue coordinates in an adapted coefficient basis to
scheme ideals on projective charts and their global intersections.
Cartier generators and blowup transport are later units.
HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexProjectiveSpace
open Manifold
open scoped ContDiff BigOperators
attribute [local instance] MvPolynomial.gradedAlgebra
namespace HodgeLean.Foundations.Program

/-- The local residue intersections glue as a projective scheme of the stated dimension.
Source: Schoen (1988), Lemma 2.3(vi), printed pp. 13–14; Lemma 2.4 proof, printed p. 15. -/
theorem s2e_chain_residue_projective_intersection_aux
    (k : ℕ) (T : Finset (Fin (k + 1))) (hT : T.card ≤ k) :
    Nonempty ((s2e_s2b_intersectionIdeal k T).subscheme ≅
      ProjectiveSpace (Fin (k - T.card + 1)) (Spec ↧ℂ)) :=
  by
    classical
    obtain ⟨e⟩ := s2e_retainedCoordinate_equiv k T hT
    obtain ⟨E⟩ := s2e_complexProjectiveSpace_iso_of_equiv e
    let f := s2e_coordinateSubspaceInclusion k T
    letI : IsClosedImmersion f := s2e_coordinateSubspaceInclusion_isClosedImmersion k T
    have hk : f.ker = s2e_s2b_intersectionIdeal k T :=
      s2e_coordinateSubspaceInclusion_kernel k T hT
    exact ⟨(eqToIso (congrArg
      (fun I : (ProjectiveSpace (Fin (k + 1)) (Spec ↧ℂ)).IdealSheafData => I.subscheme)
      hk)).symm ≪≫ (asIso f.toImage).symm ≪≫ E⟩

/-- All homogeneous coordinates vanishing gives an empty projective intersection.
Source: Schoen (1988), Lemma 2.3(vi), printed pp. 13–14; Lemma 2.4 proof, printed p. 15. -/
theorem s2e_chain_residue_projective_empty_aux
    (k : ℕ) (T : Finset (Fin (k + 1))) (hT : k < T.card) :
    IsEmpty (s2e_s2b_intersectionIdeal k T).subscheme :=
  by
    classical
    have hfull : T = Finset.univ := (Finset.card_eq_iff_eq_univ T).mp (by
      have hc := Finset.card_le_univ T
      simp only [Fintype.card_fin] at hc ⊢
      omega)
    subst T
    refine ⟨fun x => ?_⟩
    let I := s2e_s2b_intersectionIdeal k Finset.univ
    let y := I.subschemeι x
    have hy : y ∈ I.support := (Scheme.IdealSheafData.range_subschemeι I).le ⟨x, rfl⟩
    have hyj (j : Fin (k + 1)) : y ∉ projectiveSpaceBasicOpen k (MvPolynomial.X j) := by
      have hle : s2e_s2b_residueIdeal k j ≤ I :=
        le_iSup_of_le j (le_iSup_of_le (Finset.mem_univ j) le_rfl)
      have hj := Scheme.IdealSheafData.support_antitone hle hy
      change y ∈ ((s2e_s2b_residueIdeal k j).support : Set _) at hj
      rw [s2e_s2b_residueIdeal, Scheme.IdealSheafData.coe_support_vanishingIdeal] at hj
      exact hj
    have htop : (Limits.pullback.snd (Limits.terminal.from (Spec ↧ℂ))
        (Limits.terminal.from (Proj (UniversalGrading k)))) y ∈
        ⨆ j : Fin (k + 1), Proj.basicOpen (UniversalGrading k) (MvPolynomial.X j) := by
      rw [iSup_coordinateBasicOpen_eq_top]
      trivial
    obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.mp htop
    exact hyj j hj

/-- The vanishing ideal of the actual differential residue locus is the
coordinate hyperplane ideal in an explicitly adapted coefficient basis.
Source: Schoen (1988), Lemma 2.3(iv,vi), printed pp. 13–14. -/
theorem s2e_chain_differential_residue_ideal_aux
    (E C : Type) [NormedAddCommGroup E] [NormedSpace ℂ E]
    [TopologicalSpace C] [ChartedSpace E C] [IsManifold 𝓘(ℂ, E) ω C]
    (hE : Module.finrank ℂ E = 1) (k r : ℕ)
    (w : Fin r → b4c_MeroForm E C hE) (x : Fin r → C)
    (hres : ∀ i j, b4c_res (hE := hE) (w i) (x j) = if i = j then 1 else 0)
    (b : (Fin (k + 1) → ℂ) ≃ₗ[ℂ] (b3_HolForm E C × (Fin r → ℂ)))
    (ι : Fin r ↪ Fin (k + 1))
    (hb : ∀ v j, (b v).2 j = v (ι j)) (j : Fin r) :
    Scheme.IdealSheafData.vanishingIdeal (TopologicalSpace.Closeds.closure
      {p | ∃ (v : Fin (k + 1) → ℂ) (hv : v ≠ 0),
        b4c_res (hE := hE) (s2e_pairedDifferentialLinear hE w (b v)) (x j) = 0 ∧
        p = (vectorToComplexPoint v hv).underlying}) =
      s2e_s2b_residueIdeal k (ι j) :=
  by
    have hvres (v : Fin (k + 1) → ℂ) :
        b4c_res (hE := hE) (s2e_pairedDifferentialLinear hE w (b v)) (x j) = v (ι j) := by
      simpa only [mul_one, hb] using
        s2e_pairedDifferentialLinear_residue_coordinate hE w x 1 hres (b v).1 (b v).2 j
    simp_rw [hvres]
    unfold s2e_s2b_residueIdeal
    congr 1
    apply TopologicalSpace.Closeds.ext
    exact s2e_coordinate_hyperplane_closure k (ι j)

end HodgeLean.Foundations.Program
