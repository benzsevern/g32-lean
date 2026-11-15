import HodgeLean.Foundations.Program.SchoenTowerL1aPointSections
import HodgeLean.Foundations.Program.SchoenTowerL1aAffineCurveFirstJets
import HodgeLean.Foundations.Program.SchoenTowerL1aJetInterpolation

/-! # Interpolation at actual affine complex points

The actual maximal point kernels and prescribed nonzero first-order classes
supply a section with prescribed complex values.
HC no distance; AV milestone no distance.
-/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- Nonzero first-order classes at distinct actual complex points permit simultaneous prescribed values and nonzero point-ideal classes.
Source: Atiyah–Macdonald, Introduction to Commutative Algebra, Proposition 1.10; Hartshorne, Algebraic Geometry, II.2 and II.8. -/
theorem s2v_l1a_actual_point_jet_interpolation
    (Z : Over (Spec ↧ℂ)) [IsAffine Z.left] {κ : Type*} [Finite κ]
    (p : κ → ComplexPoint Z) (hp : Function.Injective p)
    (c : κ → ℂ) (u : κ → Γ(Z.left, ⊤))
    (hu : ∀ k, u k ∈ (p k).left.ker.ideal ⟨⊤, isAffineOpen_top _⟩)
    (hnu : ∀ k, u k ∉ ((p k).left.ker.ideal ⟨⊤, isAffineOpen_top _⟩) ^ 2) :
    ∃ f : Γ(Z.left, ⊤), ∀ k,
      Point.evaluate ⊤ f (p k) = c k ∧
      f - Z.hom.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom (c k)) ∉
        ((p k).left.ker.ideal ⟨⊤, isAffineOpen_top _⟩) ^ 2 := by
  let m (k : κ) := RingHom.ker (s2v_l1a_pointSectionEvaluation Z (p k))
  letI (k : κ) : (m k).IsMaximal := s2v_l1a_pointSectionEvaluation_maximal Z (p k)
  have hm : Function.Injective m := (s2v_l1a_pointSectionEvaluation_kernel_injective Z).comp hp
  have hmk (k : κ) : m k = (p k).left.ker.ideal ⟨⊤, isAffineOpen_top _⟩ :=
    s2v_l1a_pointSectionEvaluation_kernel Z (p k)
  let c' (k : κ) := Z.hom.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom (c k))
  obtain ⟨f, hf⟩ := s2v_l1a_nonzero_first_jet_interpolation m hm c' u
    (fun k => (hmk k).symm ▸ hu k) (fun k => by simpa only [hmk] using hnu k)
  refine ⟨f, fun k => ⟨?_, ?_⟩⟩
  · have H := (hf k).1
    change s2v_l1a_pointSectionEvaluation Z (p k) (f - c' k) = 0 at H
    rw [map_sub, s2v_l1a_pointSectionEvaluation_constant, sub_eq_zero] at H
    exact (s2v_l1a_pointSectionEvaluation_apply Z (p k) f).symm.trans H
  · simpa only [hmk] using (hf k).2

/-- On a smooth affine curve, prescribed values at finitely many distinct actual complex points can be interpolated with nonzero first-order classes.
Source: Atiyah–Macdonald, Introduction to Commutative Algebra, Proposition 1.10; Hartshorne, Algebraic Geometry, II.8 and III.10. -/
theorem s2v_l1a_affine_curve_jet_interpolation
    (Z : Over (Spec ↧ℂ)) [IsAffine Z.left] [SmoothOfRelativeDimension 1 Z.hom]
    {κ : Type*} [Finite κ] (p : κ → ComplexPoint Z) (hp : Function.Injective p)
    (c : κ → ℂ) :
    ∃ f : Γ(Z.left, ⊤), ∀ k,
      Point.evaluate ⊤ f (p k) = c k ∧
      f - Z.hom.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom (c k)) ∉
        ((p k).left.ker.ideal ⟨⊤, isAffineOpen_top _⟩) ^ 2 := by
  classical
  choose u hu hnu using fun k => s2v_l1a_affine_curve_point_first_jet Z (p k)
  exact s2v_l1a_actual_point_jet_interpolation Z p hp c u hu hnu

/-- A finite tuple on an actual smooth affine curve has one section vanishing at its first point, separating distinct support points and having nonzero first-order classes at all of them.
Source: Atiyah–Macdonald, Introduction to Commutative Algebra, Proposition 1.10; Hartshorne, Algebraic Geometry, II.8 and III.10. -/
theorem s2v_l1a_affine_curve_separating_first_jets
    (Z : Over (Spec ↧ℂ)) [IsAffine Z.left] [SmoothOfRelativeDimension 1 Z.hom]
    (n : ℕ) (p : Fin (n + 1) → ComplexPoint Z) :
    ∃ f : Γ(Z.left, ⊤), Point.evaluate ⊤ f (p 0) = 0 ∧
      (∀ j k, p j ≠ p k → Point.evaluate ⊤ f (p j) ≠ Point.evaluate ⊤ f (p k)) ∧
      (∀ j, f - Z.hom.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom
          (Point.evaluate ⊤ f (p j))) ∉ ((p j).left.ker.ideal ⟨⊤, isAffineOpen_top _⟩) ^ 2) := by
  classical
  let κ := Set.range p
  letI : Fintype κ := (Set.finite_range p).fintype
  let k₀ : κ := ⟨p 0, ⟨0, rfl⟩⟩
  let c (k : κ) : ℂ := ((Fintype.equivFin κ k).val : ℂ) -
    ((Fintype.equivFin κ k₀).val : ℂ)
  have hc : Function.Injective c := by
    intro i j hij
    apply (Fintype.equivFin κ).injective
    apply Fin.ext
    dsimp only [c] at hij
    exact_mod_cast (sub_left_inj.mp hij)
  obtain ⟨f, hf⟩ := s2v_l1a_affine_curve_jet_interpolation Z
    (fun k : κ => k.1) Subtype.val_injective c
  refine ⟨f, ?_, ?_, ?_⟩
  · simpa only [c, sub_self] using (hf k₀).1
  · intro j k hjk hval
    let j' : κ := ⟨p j, ⟨j, rfl⟩⟩
    let k' : κ := ⟨p k, ⟨k, rfl⟩⟩
    have hck : c j' = c k' := (hf j').1.symm.trans (hval.trans (hf k').1)
    exact hjk (congrArg Subtype.val (hc hck))
  · intro j
    let k : κ := ⟨p j, ⟨j, rfl⟩⟩
    rw [(hf k).1]
    exact (hf k).2

end HodgeLean.Foundations.Program
