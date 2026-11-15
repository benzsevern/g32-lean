import HodgeLean.Foundations.Program.SchoenTowerT11bDefs
import Mathlib.Analysis.Convex.SimplicialComplex.Basic

/-! Finite-carrier piece of relative set triangulation. HC no distance; AV milestone no distance. -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

theorem s2v_hardt6_formula_finset_inter {n : ℕ}
    (S : Finset (s2v_t11b_Formula n)) :
    ∃ f : s2v_t11b_Formula n, f.realize = ⋂ g ∈ S, g.realize := by
  classical
  induction S using Finset.induction_on with
  | empty =>
      exact ⟨.nonneg 0, by ext x; simp [s2v_t11b_Formula.realize]⟩
  | @insert a S ha ih =>
      obtain ⟨f, hf⟩ := ih
      exact ⟨.inter a f, by simp [s2v_t11b_Formula.realize, hf]⟩

theorem s2v_hardt6_singleton_formula {n : ℕ}
    (x : EuclideanSpace ℝ (Fin n)) :
    ∃ f : s2v_t11b_Formula n, f.realize = {x} := by
  classical
  let c : Fin n → s2v_t11b_Formula n := fun i =>
    .inter (.nonneg (MvPolynomial.X i - MvPolynomial.C (x i)))
      (.nonneg (MvPolynomial.C (x i) - MvPolynomial.X i))
  obtain ⟨f, hf⟩ := s2v_hardt6_formula_finset_inter (Finset.univ.image c)
  refine ⟨f, ?_⟩
  ext y
  rw [hf]
  simp only [Set.mem_iInter, Finset.mem_image, Finset.mem_univ, true_and,
    forall_exists_index, forall_apply_eq_imp_iff, Set.mem_singleton_iff]
  simp only [c, s2v_t11b_Formula.realize, Set.mem_inter_iff, Set.mem_ofPred_eq,
    map_sub, MvPolynomial.eval_X, MvPolynomial.eval_C]
  change (∀ i, 0 ≤ y i - x i ∧ 0 ≤ x i - y i) ↔ y = x
  constructor
  · intro h
    ext i
    have := h i
    dsimp at *
    linarith
  · rintro rfl i
    exact ⟨by simp, by simp⟩

theorem s2v_hardt6_finite_formula {n : ℕ}
    (A : Set (EuclideanSpace ℝ (Fin n))) (hA : A.Finite) :
    ∃ f : s2v_t11b_Formula n, f.realize = A := by
  classical
  induction A, hA using Set.Finite.induction_on with
  | empty =>
      exact ⟨.compl (.nonneg 0), by ext x; simp [s2v_t11b_Formula.realize]⟩
  | @insert x A hx hA ih =>
      obtain ⟨f, hf⟩ := ih
      obtain ⟨g, hg⟩ := s2v_hardt6_singleton_formula x
      exact ⟨.compl (.inter (.compl g) (.compl f)), by
        ext y; simp [s2v_t11b_Formula.realize, hf, hg]; tauto⟩

/-- Finite Boolean carriers have a singleton-face triangulation preserving every designated subset.
Source: Coste, Real Algebraic Sets (2005), Theorem 1.10, finite-carrier case. -/
theorem s2v_hardt6_finite_triangulation_aux {n m : ℕ}
    (f : s2v_t11b_Formula n) (hf : f.realize.Finite)
    (b : Fin m → s2v_t11b_Formula n) :
    ∃ K : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin n)),
      K.faces.Finite ∧ K.space = f.realize ∧
      (∀ s ∈ K.faces, ∃ x ∈ f.realize, s = {x}) ∧
      ∃ h : K.space ≃ₜ f.realize,
        (∀ x, (h x).val = x.val) ∧
        (∀ y, (h.symm y).val = y.val) ∧
        (∀ j, ∃ S : Finset (EuclideanSpace ℝ (Fin n)),
          (↑S : Set (EuclideanSpace ℝ (Fin n))) ⊆ K.vertices ∧
          f.realize ∩ (b j).realize = ⋃ x ∈ S, ({x} : Set _)) ∧
        ∃ g : s2v_t11b_Formula (n + n), ∀ z,
          z ∈ g.realize ↔ ∃ x : K.space,
            (∀ i, z (Fin.castAdd n i) = x.val i) ∧
            (∀ i, z (Fin.natAdd n i) = (h x).val i) := by
  classical
  let K : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin n)) :=
    { faces := {s | ∃ x ∈ f.realize, s = {x}}
      isRelLowerSet_faces := by
        intro s hs
        obtain ⟨x, hx, rfl⟩ := hs
        refine ⟨Finset.singleton_nonempty x, ?_⟩
        intro t ht hne
        exact ⟨x, hx, Finset.eq_singleton_iff_unique_mem.mpr
          ⟨by
              obtain ⟨y, hy⟩ := hne
              have hyx := Finset.mem_singleton.mp (ht hy)
              exact hyx ▸ hy,
            fun y hy => by simpa using ht hy⟩⟩
      indep := by
        rintro s ⟨x, hx, rfl⟩
        exact affineIndependent_of_subsingleton ℝ _
      inter_subset_convexHull := by
        rintro s t ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩
        by_cases hxy : x = y
        · subst y
          simp
        · simp [hxy] }
  have hspace : K.space = f.realize := by
    ext z
    simp [Geometry.SimplicialComplex.mem_space_iff, K]
  have hverts : K.vertices = f.realize := by
    ext z
    simp [Geometry.SimplicialComplex.vertices, K]
  let pair : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin (n + n)) :=
    fun x => WithLp.toLp 2 (Fin.append (fun i => x i) (fun i => x i))
  obtain ⟨g, hg⟩ := s2v_hardt6_finite_formula (pair '' f.realize) (hf.image pair)
  let h : K.space ≃ₜ f.realize := Homeomorph.setCongr hspace
  refine ⟨K, ?_, hspace, ?_, h, (fun _ => rfl), (fun _ => rfl), ?_, g, ?_⟩
  · have heq : K.faces = (fun x => ({x} : Finset _)) '' f.realize := by
      ext s
      simp [K, eq_comm]
    rw [heq]
    exact hf.image _
  · rintro s ⟨x, hx, rfl⟩
    exact ⟨x, hx, rfl⟩
  · intro j
    let S := (hf.inter_of_left (b j).realize).toFinset
    refine ⟨S, ?_, ?_⟩
    · intro x hx
      rw [hverts]
      exact ((hf.inter_of_left (b j).realize).mem_toFinset.mp hx).1
    · ext x
      simp [S]
  · intro z
    rw [hg]
    constructor
    · rintro ⟨x, hx, rfl⟩
      refine ⟨⟨x, hspace.symm ▸ hx⟩, ?_, ?_⟩
      · intro i
        exact Fin.append_left _ _ i
      · intro i
        exact Fin.append_right _ _ i
    · rintro ⟨x, hx, hy⟩
      change ∀ i, z (Fin.natAdd n i) = x.val i at hy
      refine ⟨x.val, hspace ▸ x.property, ?_⟩
      ext i
      refine Fin.addCases ?_ ?_ i
      · intro k
        simpa [pair] using (hx k).symm
      · intro k
        simpa only [pair, WithLp.ofLp_toLp, Fin.append_right] using (hy k).symm

end HodgeLean.Foundations.Program
