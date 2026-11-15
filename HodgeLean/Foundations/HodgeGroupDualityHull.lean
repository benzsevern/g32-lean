import HodgeLean.Foundations.HodgeGroupDuality

/-! Rational algebraic hulls commute with the dual representation. -/

noncomputable section
namespace HodgeLean.Foundations
variable {n : ℕ}

@[simp] theorem g2_contragredient_twice (g : Matrix.GeneralLinearGroup (Fin n) ℂ) :
    g2_contragredient (g2_contragredient g) = g := by
  simp [g2_contragredient]

/-- Inversion does not change membership in an algebraic subgroup. -/
theorem g2_mem_inverse_iff {G : Set (Matrix.GeneralLinearGroup (Fin n) ℂ)}
    (hG : g2_IsRatAlgSubgroup G) (g : Matrix.GeneralLinearGroup (Fin n) ℂ) :
    g⁻¹ ∈ G ↔ g ∈ G :=
  ⟨fun h => by simpa only [inv_inv] using hG.2.2.2 _ h, hG.2.2.2 g⟩

/-- Rational algebraicity is preserved under the dual group representation. -/
theorem g2_isRatAlgSubgroup_contragredient {G : Set (Matrix.GeneralLinearGroup (Fin n) ℂ)}
    (hG : g2_IsRatAlgSubgroup G) : g2_IsRatAlgSubgroup (g2_contragredient ⁻¹' G) := by
  have heq : g2_contragredient ⁻¹' G = g2_dualTranspose ⁻¹' G := by
    ext g
    exact g2_mem_inverse_iff hG (g2_dualTranspose g)
  rw [heq]
  exact g2_isRatAlgSubgroup_transpose hG

/-- The smallest rational algebraic subgroup containing a set commutes with inverse transpose.
The input set need not itself be a subgroup. -/
theorem g2_contragredient_algebraicHull (S : Set (Matrix.GeneralLinearGroup (Fin n) ℂ)) :
    g2_contragredient '' (⋂₀ {G | g2_IsRatAlgSubgroup G ∧ S ⊆ G}) =
      ⋂₀ {G | g2_IsRatAlgSubgroup G ∧ g2_contragredient '' S ⊆ G} := by
  have forward (T : Set (Matrix.GeneralLinearGroup (Fin n) ℂ)) :
      g2_contragredient '' (⋂₀ {G | g2_IsRatAlgSubgroup G ∧ T ⊆ G}) ⊆
        ⋂₀ {G | g2_IsRatAlgSubgroup G ∧ g2_contragredient '' T ⊆ G} := by
    rintro _ ⟨g, hg, rfl⟩
    apply Set.mem_sInter.mpr
    rintro G ⟨hG, hT⟩
    exact Set.mem_sInter.mp hg (g2_contragredient ⁻¹' G)
      ⟨g2_isRatAlgSubgroup_contragredient hG, fun x hx => hT ⟨x, hx, rfl⟩⟩
  apply Set.Subset.antisymm (forward S)
  intro g hg
  refine ⟨g2_contragredient g, ?_, g2_contragredient_twice g⟩
  have ht := forward (g2_contragredient '' S) ⟨g, hg, rfl⟩
  have heq : g2_contragredient '' (g2_contragredient '' S) = S := by
    ext x
    constructor
    · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
      simpa only [g2_contragredient_twice] using hy
    · intro hx
      exact ⟨g2_contragredient x, ⟨x, hx, rfl⟩, g2_contragredient_twice x⟩
  rwa [heq] at ht

open scoped TensorProduct

/-- The Hodge group of the dual circle representation is the contragredient of the Hodge group.
Both sides are obtained by intersecting rational algebraic subgroups. -/
theorem g2_contragredient_hodgeGroup {V : Type*} [AddCommGroup V] [Module ℚ V]
    (H : ℤ × ℤ → Submodule ℂ (ℂ ⊗[ℚ] V)) (hH : DirectSum.IsInternal H)
    (b : Module.Basis (Fin n) ℚ V) :
    g2_contragredient '' g2_hodgeGroup H hH b =
      ⋂₀ {G | g2_IsRatAlgSubgroup G ∧
        g2_contragredient '' g2_circleImage H hH b ⊆ G} :=
  g2_contragredient_algebraicHull _

end HodgeLean.Foundations
