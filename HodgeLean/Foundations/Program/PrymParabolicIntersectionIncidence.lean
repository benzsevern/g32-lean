import HodgeLean.Foundations.Program.PrymParabolicIntersectionWindowTable

set_option linter.unusedSectionVars false

noncomputable section
namespace HodgeLean.Foundations.Program

/-! ## Outgoing and incoming triangles of a lifted edge -/

section Incidence

variable {G : Type} [Group G] (g : Fin 13 → G)

/-- The triangle on the outgoing side of the dual edge of `ε`: `B_i(x)` for `e_i(x)`, `A_i(x)` for
`f_i(x)`, `B_i(x g_i)` for `h_i(x)`; its spoke enters `hga_dualChain` with coefficient `−α ε`.
Source: `hga_dualChain`, `hg2_orient`, `hg2_face0/1/2`. -/
def hga_triOut : hg2_Edge G 13 → hg2_Tri G 13
  | Sum.inl (i, x) => Sum.inr (i, x)
  | Sum.inr (Sum.inl (i, x)) => Sum.inl (i, x)
  | Sum.inr (Sum.inr (i, x)) => Sum.inr (i, x * g i)

/-- The triangle on the incoming side of the dual edge of `ε`: `A_i(x)` for `e_i(x)` and `h_i(x)`,
`B_{i−1}(x)` for `f_i(x)`; its spoke enters `hga_dualChain` with coefficient `+α ε`.
Source: `hga_dualChain`, `hg2_orient`, `hg2_face0/1/2`. -/
def hga_triIn : hg2_Edge G 13 → hg2_Tri G 13
  | Sum.inl (i, x) => Sum.inl (i, x)
  | Sum.inr (Sum.inl (i, x)) => Sum.inr ((finRotate 13).symm i, x)
  | Sum.inr (Sum.inr (i, x)) => Sum.inl (i, x)

/-- The triangle carrying the straight part of `ε` used by its primal window.
Source: `hga_baseSpec`. -/
def hga_triArc : hg2_Edge G 13 → hg2_Tri G 13
  | Sum.inl (i, x) => Sum.inl (i, x)
  | Sum.inr (Sum.inl (i, x)) => if i = 12 then Sum.inr ((finRotate 13).symm i, x) else Sum.inl (i, x)
  | Sum.inr (Sum.inr (i, x)) => Sum.inl (i, x)

/-- The face index of an edge in its adjacent triangles: `2` for `e`, `1` for `f`, `0` for `h`.
Source: `hg2_face0/1/2`. -/
def hga_faceIdx : hg2_Edge G 13 → Fin 3
  | Sum.inl _ => 2
  | Sum.inr (Sum.inl _) => 1
  | Sum.inr (Sum.inr _) => 0

/-- The base edge under a lifted edge.
Source: `hg5_triBase`. -/
def hga_edgeBase : hg2_Edge G 13 → hg2_Edge Unit 13
  | Sum.inl (i, _) => Sum.inl (i, ())
  | Sum.inr (Sum.inl (i, _)) => Sum.inr (Sum.inl (i, ()))
  | Sum.inr (Sum.inr (i, _)) => Sum.inr (Sum.inr (i, ()))

/-- The face `k` of a triangle.
Source: `hg2_face0/1/2`. -/
def hga_faceEdge (k : Fin 3) (τ : hg2_Tri G 13) : hg2_Edge G 13 :=
  if k = 0 then hg2_face0 g τ else if k = 1 then hg2_face1 τ else hg2_face2 τ

theorem hga_faceEdge_out (ε : hg2_Edge G 13) :
    hga_faceEdge g (hga_faceIdx ε) (hga_triOut g ε) = ε := by
  rcases ε with ⟨i, x⟩ | ⟨i, x⟩ | ⟨i, x⟩ <;>
    simp [hga_faceEdge, hga_faceIdx, hga_triOut, hg2_face0, hg2_face1, hg2_face2]

theorem hga_faceEdge_in (ε : hg2_Edge G 13) :
    hga_faceEdge g (hga_faceIdx ε) (hga_triIn ε) = ε := by
  rcases ε with ⟨i, x⟩ | ⟨i, x⟩ | ⟨i, x⟩ <;>
    simp [hga_faceEdge, hga_faceIdx, hga_triIn, hg2_face0, hg2_face1, hg2_face2]

theorem hga_faceEdge_arc (ε : hg2_Edge G 13) :
    hga_faceEdge g (hga_faceIdx ε) (hga_triArc ε) = ε := by
  rcases ε with ⟨i, x⟩ | ⟨i, x⟩ | ⟨i, x⟩
  · simp [hga_faceEdge, hga_faceIdx, hga_triArc, hg2_face2]
  · by_cases h : i = 12
    · simp [hga_faceEdge, hga_faceIdx, hga_triArc, hg2_face1, h]
    · simp [hga_faceEdge, hga_faceIdx, hga_triArc, hg2_face1, h]
  · simp [hga_faceEdge, hga_faceIdx, hga_triArc, hg2_face0]

theorem hga_face_tri {T : Type} [TopologicalSpace T] (D : hg8_DeltaMap g T) (k : Fin 3)
    (τ : hg2_Tri G 13) : hg5_face (D.tri τ) k = D.edge (hga_faceEdge g k τ) := by
  obtain ⟨h0, h1, h2⟩ := D.faces τ
  fin_cases k
  · simpa [hga_faceEdge] using h0
  · simpa [hga_faceEdge] using h1
  · simpa [hga_faceEdge] using h2

end Incidence

/-! ## The window data of a lifted edge -/

theorem hga_specOfE_fields (i : Fin 13) :
    (hga_specOfE i).τo = Sum.inr (i, ()) ∧ (hga_specOfE i).τi = Sum.inl (i, ()) ∧
      (hga_specOfE i).τe = Sum.inl (i, ()) ∧ (hga_specOfE i).ko = 2 ∧
      (hga_specOfE i).ki = 2 ∧ (hga_specOfE i).ke = 2 := by
  unfold hga_specOfE
  split <;> exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem hga_specOfH_fields (i : Fin 13) :
    (hga_specOfH i).τo = Sum.inr (i, ()) ∧ (hga_specOfH i).τi = Sum.inl (i, ()) ∧
      (hga_specOfH i).τe = Sum.inl (i, ()) ∧ (hga_specOfH i).ko = 0 ∧
      (hga_specOfH i).ki = 0 ∧ (hga_specOfH i).ke = 0 := by
  unfold hga_specOfH
  split <;> exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem hga_specOfF_fields (i : Fin 13) :
    (hga_specOfF i).τo = Sum.inl (i, ()) ∧
      (hga_specOfF i).τi = Sum.inr ((finRotate 13).symm i, ()) ∧
      (hga_specOfF i).τe =
        (if i = 12 then Sum.inr ((finRotate 13).symm i, ()) else Sum.inl (i, ())) ∧
      (hga_specOfF i).ko = 1 ∧ (hga_specOfF i).ki = 1 ∧ (hga_specOfF i).ke = 1 := by
  unfold hga_specOfF
  split
  · next h0 =>
    have : i ≠ 12 := by rw [h0]; decide
    simp only [this, if_false]
    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  · split
    · next h0 h12 =>
      simp only [h12, if_true]
      subst h12
      exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
    · next h0 h12 =>
      simp only [h12, if_false]
      exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

section Lifted

variable {G : Type} [Group G] (g : Fin 13 → G)

theorem hga_spec_τo (ε : hg2_Edge G 13) :
    hg5_triBase (hga_triOut g ε) = (hga_baseSpec (hga_edgeBase ε)).τo := by
  rcases ε with ⟨i, x⟩ | ⟨i, x⟩ | ⟨i, x⟩
  · exact (hga_specOfE_fields i).1.symm
  · exact (hga_specOfF_fields i).1.symm
  · exact (hga_specOfH_fields i).1.symm

theorem hga_spec_τi (ε : hg2_Edge G 13) :
    hg5_triBase (hga_triIn ε) = (hga_baseSpec (hga_edgeBase ε)).τi := by
  rcases ε with ⟨i, x⟩ | ⟨i, x⟩ | ⟨i, x⟩
  · exact (hga_specOfE_fields i).2.1.symm
  · exact (hga_specOfF_fields i).2.1.symm
  · exact (hga_specOfH_fields i).2.1.symm

theorem hga_spec_τe (ε : hg2_Edge G 13) :
    hg5_triBase (hga_triArc ε) = (hga_baseSpec (hga_edgeBase ε)).τe := by
  rcases ε with ⟨i, x⟩ | ⟨i, x⟩ | ⟨i, x⟩
  · exact (hga_specOfE_fields i).2.2.1.symm
  · change _ = (hga_specOfF i).τe
    rw [(hga_specOfF_fields i).2.2.1]
    by_cases h : i = 12 <;> simp [hga_triArc, h, hg5_triBase]
  · exact (hga_specOfH_fields i).2.2.1.symm

theorem hga_spec_faces (ε : hg2_Edge G 13) :
    (hga_baseSpec (hga_edgeBase ε)).ko = hga_faceIdx ε ∧
      (hga_baseSpec (hga_edgeBase ε)).ki = hga_faceIdx ε ∧
      (hga_baseSpec (hga_edgeBase ε)).ke = hga_faceIdx ε := by
  rcases ε with ⟨i, x⟩ | ⟨i, x⟩ | ⟨i, x⟩
  · exact ⟨(hga_specOfE_fields i).2.2.2.1, (hga_specOfE_fields i).2.2.2.2.1,
      (hga_specOfE_fields i).2.2.2.2.2⟩
  · exact ⟨(hga_specOfF_fields i).2.2.2.1, (hga_specOfF_fields i).2.2.2.2.1,
      (hga_specOfF_fields i).2.2.2.2.2⟩
  · exact ⟨(hga_specOfH_fields i).2.2.2.1, (hga_specOfH_fields i).2.2.2.2.1,
      (hga_specOfH_fields i).2.2.2.2.2⟩

end Lifted

end HodgeLean.Foundations.Program
