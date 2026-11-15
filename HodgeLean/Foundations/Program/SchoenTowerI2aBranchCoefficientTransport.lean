import HodgeLean.Foundations.Program.SchoenTowerL1bKummerBranchUnits

/-! Transport of weighted branch equations and their generated fields.
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

/-- Enlarging the coefficient image preserves generation by a specified field element. -/
theorem s2v_i2a_generator_under_coefficient_map
    {R A K : Type*} [CommRing R] [CommRing A] [Field K]
    (f : R →+* A) (ρ : R →+* K) (τ : A →+* K)
    (hcomp : τ.comp f = ρ) (v : K)
    (hv : Subfield.closure (Set.range ρ ∪ {v}) = ⊤) :
    Subfield.closure (Set.range τ ∪ {v}) = ⊤ := by
  apply top_unique
  rw [← hv]
  apply Subfield.closure_mono
  apply Set.union_subset_union_left
  rintro _ ⟨r, rfl⟩
  exact ⟨f r, DFunLike.congr_fun hcomp r⟩

/-- A coefficient map and replacement principal equations retain both the weighted equation and its original generated field. -/
theorem s2v_i2a_branch_generator_transport
    {R A K : Type*} [CommRing R] [CommRing A] [IsDomain A] [Field K]
    (f : R →+* A) (ρ : R →+* K) (τ : A →+* K)
    (hcomp : τ.comp f = ρ) {J : Type*} [Fintype J]
    (z : J → R) (w : J → A) (n : J → ℕ)
    (hideal : ∀ j, Ideal.span {f (z j)} = Ideal.span {w j})
    (v : K) (m : ℕ) (ε : Rˣ)
    (hv : v ^ m = ρ (ε : R) * ∏ j, ρ (z j) ^ n j)
    (hgen : Subfield.closure (Set.range ρ ∪ {v}) = ⊤) :
    ∃ ε' : Aˣ, v ^ m = τ (ε' : A) * ∏ j, τ (w j) ^ n j ∧
      Subfield.closure (Set.range τ ∪ {v}) = ⊤ := by
  obtain ⟨ε', hε'⟩ := s2v_l1b_branch_equation_restrict f ρ τ hcomp z w n
    hideal v m ε hv
  exact ⟨ε', hε', s2v_i2a_generator_under_coefficient_map f ρ τ hcomp v hgen⟩

end HodgeLean.Foundations.Program
