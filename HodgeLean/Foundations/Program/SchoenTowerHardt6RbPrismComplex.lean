import HodgeLean.Foundations.Program.SchoenTowerHardt6RbPrismPieces
import HodgeLean.Foundations.Program.SchoenTowerHardt6RbPrismIntersection
import HodgeLean.Foundations.Program.SchoenTowerHardt6RbSubfaceIntersection
import HodgeLean.Foundations.Program.SchoenTowerHardt6RbComplexAssembly

/-! A finite geometric triangulation of a variable-height band over one simplex. -/
noncomputable section
set_option maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

theorem s2v_hardt6rb_prism_complex {E : Type*}
    [AddCommGroup E] [Module ℝ E] {m : ℕ}
    (v : Fin (m + 1) → E) (hv : AffineIndependent ℝ v)
    (l u : Fin (m + 1) → ℝ) (hlu : ∀ i, l i ≤ u i) :
    let S : Fin (m + 1) → Set (E × ℝ) := fun j =>
      ((fun i => (v i, l i)) '' {i | j ≤ i}) ∪
        ((fun i => (v i, u i)) '' {i | i ≤ j})
    ∃ K : Geometry.SimplicialComplex ℝ (E × ℝ), K.faces.Finite ∧
      (∀ s, s ∈ K.faces ↔ ∃ j, (↑s : Set (E × ℝ)) ⊆ S j ∧ s.Nonempty) ∧
      K.space = {p | ∃ w : stdSimplex ℝ (Fin (m + 1)),
        (∑ i, w.val i • v i) = p.1 ∧
        (∑ i, w.val i * l i) ≤ p.2 ∧ p.2 ≤ (∑ i, w.val i * u i)} := by
  classical
  intro S
  obtain ⟨C, hfaces, hfinite, hspace, hcover⟩ :=
    s2v_hardt6rb_prism_piece_complexes v hv l u hlu
  have hS (j) : (S j).Finite :=
    ((Set.toFinite {i : Fin (m + 1) | j ≤ i}).image _).union
      ((Set.toFinite {i : Fin (m + 1) | i ≤ j}).image _)
  let T : Fin (m + 1) → Finset (E × ℝ) := fun j => (hS j).toFinset
  have hind (j) : AffineIndependent ℝ (fun x : T j => (x : E × ℝ)) := by
    let e : T j ↪ S j :=
      ⟨fun x => ⟨x.val, (hS j).mem_toFinset.mp x.property⟩,
        fun a b h => Subtype.ext (congrArg (fun x : S j => x.val) h)⟩
    exact (s2v_hardt6rb_prism_staircase_independent v hv l u j).comp_embedding e
  have hcross : ∀ i j s t, s ∈ (C i).faces → t ∈ (C j).faces →
      convexHull ℝ (↑s : Set (E × ℝ)) ∩ convexHull ℝ (↑t : Set (E × ℝ)) ⊆
        convexHull ℝ ((↑s : Set (E × ℝ)) ∩ ↑t) := by
    intro i j s t hs ht
    have hsT : s ⊆ T i := fun x hx =>
      (hS i).mem_toFinset.mpr (((hfaces i s).mp hs).1 hx)
    have htT : t ⊆ T j := fun x hx =>
      (hS j).mem_toFinset.mpr (((hfaces j t).mp ht).1 hx)
    apply s2v_hardt6rb_subface_intersection (T i) (T j) s t (hind i) (hind j) hsT htT
    simpa only [T, Set.Finite.coe_toFinset] using
      (s2v_hardt6rb_prism_intersection v hv l u hlu i j).subset
  obtain ⟨K, hKfaces, hKfinite, hKspace⟩ :=
    s2v_hardt6rb_assemble_complex C hfinite hcross
  refine ⟨K, hKfinite, ?_, ?_⟩
  · intro s
    rw [hKfaces, Set.mem_iUnion]
    simp only [hfaces, S]
  · rw [hKspace]
    ext p
    constructor
    · intro hp
      obtain ⟨j, hpj⟩ := Set.mem_iUnion.mp hp
      rw [hspace j] at hpj
      obtain ⟨lo, up, hpos, hsum, hbase, hheight, hlo, hup⟩ :=
        s2v_hardt6rb_prism_point_weights v l u j p hpj
      let w : stdSimplex ℝ (Fin (m + 1)) :=
        ⟨(fun i => lo i + up i), (fun i => add_nonneg (hpos i).1 (hpos i).2), hsum⟩
      refine ⟨w, hbase, ?_, ?_⟩
      · rw [← hheight]
        apply Finset.sum_le_sum
        intro i hi
        change (lo i + up i) * l i ≤ lo i * l i + up i * u i
        nlinarith [mul_nonneg (hpos i).2 (sub_nonneg.mpr (hlu i))]
      · rw [← hheight]
        apply Finset.sum_le_sum
        intro i hi
        change lo i * l i + up i * u i ≤ (lo i + up i) * u i
        nlinarith [mul_nonneg (hpos i).1 (sub_nonneg.mpr (hlu i))]
    · rintro ⟨w, hw, hylo, hyhi⟩
      have hp := hcover w p.2 hylo hyhi
      have he : (∑ i, w.val i • v i, p.2) = p := Prod.ext hw rfl
      exact he ▸ hp

end HodgeLean.Foundations.Program
