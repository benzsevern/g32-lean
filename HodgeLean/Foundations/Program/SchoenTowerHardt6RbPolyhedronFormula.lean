import HodgeLean.Foundations.Program.SchoenTowerHardt6RbConvexHullFormula
import HodgeLean.Foundations.Program.SchoenTowerHardtCad5FiniteBooleanFamilies
import Mathlib.Analysis.Convex.SimplicialComplex.Basic

/-! Boolean descriptions of finite geometric simplex carriers. -/
noncomputable section
set_option maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

theorem s2v_hardt6rb_finite_convexHull_formula {n : ℕ}
    (S : Set (EuclideanSpace ℝ (Fin n))) (hS : S.Finite) :
    ∃ f : s2v_t11b_Formula n, f.realize = convexHull ℝ S := by
  letI : Fintype S := hS.fintype
  let e := Fintype.equivFin S
  let v : Fin (Fintype.card S) → EuclideanSpace ℝ (Fin n) := fun i => (e.symm i).val
  obtain ⟨f, hf⟩ := s2v_hardt6rb_convexHull_range_formula v
  have hrange : Set.range v = S := by
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      exact (e.symm i).property
    · intro hx
      exact ⟨e ⟨x, hx⟩, congrArg Subtype.val (e.symm_apply_apply ⟨x, hx⟩)⟩
  exact ⟨f, hrange ▸ hf⟩

theorem s2v_hardt6rb_complex_carrier_formula {n : ℕ}
    (K : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin n)))
    (hK : K.faces.Finite) :
    ∃ f : s2v_t11b_Formula n, f.realize = K.space := by
  classical
  letI : Fintype K.faces := hK.fintype
  have hface (s : K.faces) : ∃ f : s2v_t11b_Formula n,
      f.realize = convexHull ℝ (↑s.val : Set (EuclideanSpace ℝ (Fin n))) :=
    s2v_hardt6rb_finite_convexHull_formula _ s.val.finite_toSet
  choose F hF using hface
  obtain ⟨f, hf⟩ := s2v_hardt_cad5_finite_union_formula F
  refine ⟨f, ?_⟩
  rw [hf]
  simp_rw [hF]
  ext x
  simp only [Set.mem_iUnion, Geometry.SimplicialComplex.mem_space_iff]
  constructor
  · rintro ⟨s, hs⟩
    exact ⟨s.val, s.property, hs⟩
  · rintro ⟨s, hs, hx⟩
    exact ⟨⟨s, hs⟩, hx⟩

end HodgeLean.Foundations.Program
