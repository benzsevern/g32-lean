import HodgeLean.Foundations.Program.SchoenTowerHardt6RbAdjoinConvexCell
import HodgeLean.Foundations.Program.SchoenTowerHardt6RbSubcomplexUnion
import HodgeLean.Foundations.Program.SchoenTowerHardt6RbDisjointComplexUnion
import HodgeLean.Foundations.Program.SchoenTowerHardt6RbSimplexComplex

/-! Finite ordered convex cell systems construct a shared geometric triangulation of every cell carrier. -/
noncomputable section
set_option maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

theorem s2v_hardt6rb_ordered_convex_cells {E : Type*} [DecidableEq E]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {N : ℕ} (C : Fin N → Set E) (D : Fin N → Finset (Fin N))
    (hD : ∀ i j, j ∈ D i → j.val < i.val)
    (hcompact : ∀ i, IsCompact (C i)) (hconv : ∀ i, Convex ℝ (C i))
    (a : Fin N → E) (ha : ∀ i, a i ∈ intrinsicInterior ℝ (C i))
    (hboundary : ∀ i, C i \ intrinsicInterior ℝ (C i) = ⋃ j : D i, C j.val)
    (hsep : ∀ i j, j.val < i.val → C j ∩ C i ⊆ C i \ intrinsicInterior ℝ (C i))
    (hcase : ∀ i, (∃ p, C i = {p}) ∨ (C i \ intrinsicInterior ℝ (C i)).Nonempty) :
    ∃ K : Geometry.SimplicialComplex ℝ E, K.faces.Finite ∧ K.space = ⋃ i, C i ∧
      ∀ i, ∃ P : Geometry.SimplicialComplex ℝ E,
        P.faces.Finite ∧ P.space = C i ∧ P.faces ⊆ K.faces := by
  classical
  have hprefix : ∀ k, k ≤ N → ∃ K : Geometry.SimplicialComplex ℝ E,
      K.faces.Finite ∧ K.space = {x | ∃ i, i.val < k ∧ x ∈ C i} ∧
      ∀ i, i.val < k → ∃ P : Geometry.SimplicialComplex ℝ E,
        P.faces.Finite ∧ P.space = C i ∧ P.faces ⊆ K.faces := by
    intro k
    induction k with
    | zero =>
      intro _
      refine ⟨⊥, Set.finite_empty, ?_, ?_⟩
      · simp [Geometry.SimplicialComplex.space_bot]
      · intro i hi
        omega
    | succ k ih =>
      intro hkN
      obtain ⟨K, hK, hKs, hprev⟩ := ih (Nat.le_of_succ_le hkN)
      let i : Fin N := ⟨k, lt_of_lt_of_le (Nat.lt_succ_self k) hkN⟩
      choose A hAf hAs hAK using fun j : D i => hprev j.val (hD i j.val j.property)
      obtain ⟨B, _, hB, hBs, hBK⟩ := s2v_hardt6rb_subcomplex_union K hK A hAK
      have hBC : B.space = C i \ intrinsicInterior ℝ (C i) := by
        rw [hBs, hboundary i]
        exact Set.iUnion_congr (fun j => hAs j)
      have hKC : K.space ∩ C i ⊆ C i \ intrinsicInterior ℝ (C i) := by
        rintro x ⟨hxK, hxi⟩
        obtain ⟨j, hj, hxj⟩ := (Set.ext_iff.mp hKs x).mp hxK
        exact hsep i j hj ⟨hxj, hxi⟩
      have hext : ∃ L P : Geometry.SimplicialComplex ℝ E,
          L.faces.Finite ∧ P.faces.Finite ∧ P.space = C i ∧
          L.faces = K.faces ∪ P.faces ∧ L.space = K.space ∪ C i := by
        rcases hcase i with ⟨p, hp⟩ | hne
        · haveI : Subsingleton (↑({p} : Finset E)) := ⟨fun x y => Subtype.ext
            ((Finset.mem_singleton.mp x.property).trans (Finset.mem_singleton.mp y.property).symm)⟩
          obtain ⟨P, _, hP, hPs⟩ := s2v_hardt6rb_simplex_complex ({p} : Finset E)
            (affineIndependent_of_subsingleton ℝ _)
          have hPC : P.space = C i := by simpa only [hp, Finset.coe_singleton, convexHull_singleton] using hPs
          have hdisj : Disjoint K.space P.space := by
            apply Set.disjoint_left.mpr
            intro x hxK hxP
            have hxi : x ∈ C i := hPC ▸ hxP
            have hxin : x ∈ intrinsicInterior ℝ (C i) := by
              simpa only [hp, intrinsicInterior_singleton] using hxi
            exact (hKC ⟨hxK, hxi⟩).2 hxin
          obtain ⟨L, hLf, hL, hLs⟩ := s2v_hardt6rb_disjoint_complex_union K P hK hP hdisj
          exact ⟨L, P, hL, hP, hPC, hLf, by simpa only [hPC] using hLs⟩
        · obtain ⟨L, P, hL, hP, hPC, hLf, hLs, _⟩ := s2v_hardt6rb_adjoin_convex_cell
            (C i) (hcompact i) (hconv i) (a i) (ha i) K B hK hBK hBC (hBC.symm ▸ hne) hKC
          exact ⟨L, P, hL, hP, hPC, hLf, hLs⟩
      obtain ⟨L, P, hL, hP, hPC, hLf, hLs⟩ := hext
      have hKL : K.faces ⊆ L.faces := by rw [hLf]; exact Set.subset_union_left
      have hPL : P.faces ⊆ L.faces := by rw [hLf]; exact Set.subset_union_right
      refine ⟨L, hL, ?_, ?_⟩
      · rw [hLs, hKs]
        ext x
        constructor
        · rintro (⟨j, hj, hxj⟩ | hxi)
          · exact ⟨j, Nat.lt_succ_of_lt hj, hxj⟩
          · exact ⟨i, Nat.lt_succ_self k, hxi⟩
        · rintro ⟨j, hj, hxj⟩
          by_cases hji : j = i
          · exact Or.inr (hji ▸ hxj)
          · left
            refine ⟨j, ?_, hxj⟩
            have hne : j.val ≠ k := fun h => hji (Fin.ext h)
            omega
      · intro j hj
        by_cases hji : j = i
        · subst j
          exact ⟨P, hP, hPC, hPL⟩
        · have hjk : j.val < k := by
            have hne : j.val ≠ k := fun h => hji (Fin.ext h)
            omega
          obtain ⟨Q, hQ, hQC, hQK⟩ := hprev j hjk
          exact ⟨Q, hQ, hQC, hQK.trans hKL⟩
  obtain ⟨K, hK, hKs, hP⟩ := hprefix N le_rfl
  refine ⟨K, hK, ?_, fun i => hP i i.isLt⟩
  rw [hKs]
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_iUnion]
  exact ⟨fun ⟨i, _, hi⟩ => ⟨i, hi⟩, fun ⟨i, hi⟩ => ⟨i, i.isLt, hi⟩⟩

end HodgeLean.Foundations.Program
