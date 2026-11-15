import HodgeLean.Foundations.Program.SchoenTowerHardt6RbFacePivot

/-! A restricted staircase vertex family belongs to a staircase of the base face. -/
noncomputable section
namespace HodgeLean.Foundations.Program

theorem s2v_hardt6rb_restricted_staircase_vertices {ι E F : Type*} [LinearOrder ι]
    (v : ι → E) (hv : Function.Injective v) (l u : ι → F)
    (j : ι) (I : Finset ι) (hI : I.Nonempty) :
    ∃ k : I,
      ((((fun i => (v i, l i)) '' {i | j ≤ i}) ∪
        ((fun i => (v i, u i)) '' {i | i ≤ j})) ∩
          Prod.fst ⁻¹' (v '' (↑I : Set ι))) ⊆
        (((fun i : I => (v i.val, l i.val)) '' {i | k ≤ i}) ∪
          ((fun i : I => (v i.val, u i.val)) '' {i | i ≤ k})) := by
  classical
  obtain ⟨k, hk, hlo, hup⟩ := s2v_hardt6rb_face_pivot I hI j
  refine ⟨⟨k, hk⟩, ?_⟩
  rintro p ⟨hp, hpI⟩
  rcases hp with ⟨i, hi, rfl⟩ | ⟨i, hi, rfl⟩
  · obtain ⟨a, ha, hea⟩ := hpI
    have hai : a = i := hv hea
    subst a
    exact Or.inl ⟨⟨i, ha⟩, hlo i ha hi, rfl⟩
  · obtain ⟨a, ha, hea⟩ := hpI
    have hai : a = i := hv hea
    subst a
    exact Or.inr ⟨⟨i, ha⟩, hup i ha hi, rfl⟩

end HodgeLean.Foundations.Program
