import HodgeLean.Foundations.Program.SchoenTowerT11bSimpleFibers

/-! Product coordinates for finite unions of distinct continuous graphs.
HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

/-- Finitely many distinct continuous real sections give product coordinates on their union.
Source: Coste, Real Algebraic Sets (2005), Theorem 1.3, root-section assembly step. -/
def s2v_t11b_finite_graph_homeomorph {B : Type*} [TopologicalSpace B] {m : ℕ}
    (ψ : Fin m → B → ℝ) (hψ : ∀ i, Continuous (ψ i))
    (hinj : ∀ b, Function.Injective (fun i => ψ i b)) :
    (Fin m × B) ≃ₜ {z : B × ℝ | ∃ i, z.2 = ψ i z.1} := by
  classical
  let T := {z : B × ℝ | ∃ i, z.2 = ψ i z.1}
  let F : Fin m × B → T := fun y => ⟨(y.2, ψ y.1 y.2), ⟨y.1, rfl⟩⟩
  have hF : Function.Bijective F := by
    constructor
    · rintro ⟨i, t⟩ ⟨j, s⟩ h
      have ht : t = s := congrArg (fun z : T => z.val.1) h
      subst s
      have hi : i = j := hinj t (congrArg (fun z : T => z.val.2) h)
      exact Prod.ext hi rfl
    · rintro ⟨⟨t, x⟩, i, hi⟩
      exact ⟨(i, t), Subtype.ext (Prod.ext rfl hi.symm)⟩
  have hc : Continuous F := by
    apply continuous_prod_of_discrete_left.mpr
    intro i
    exact (continuous_id.prodMk (hψ i)).subtype_mk _
  have hclosed : IsClosedMap F := by
    intro A hA
    have himage : F '' A = ⋃ i : Fin m,
        {z : T | (i, z.val.1) ∈ A ∧ z.val.2 = ψ i z.val.1} := by
      ext z
      constructor
      · rintro ⟨⟨i, t⟩, hy, rfl⟩
        exact Set.mem_iUnion.mpr ⟨i, hy, rfl⟩
      · intro hz
        obtain ⟨i, hi, heq⟩ := Set.mem_iUnion.mp hz
        exact ⟨(i, z.val.1), hi, Subtype.ext (Prod.ext rfl heq.symm)⟩
    rw [himage]
    apply isClosed_iUnion_of_finite
    intro i
    have h₁ : IsClosed {z : T | (i, z.val.1) ∈ A} :=
      hA.preimage (continuous_const.prodMk (continuous_fst.comp continuous_subtype_val))
    have h₂ : IsClosed {z : T | z.val.2 = ψ i z.val.1} :=
      isClosed_eq (continuous_snd.comp continuous_subtype_val)
        ((hψ i).comp (continuous_fst.comp continuous_subtype_val))
    exact h₁.inter h₂
  exact (Equiv.ofBijective F hF).toHomeomorphOfContinuousClosed hc hclosed

/-- The finite-graph chart preserves its base coordinate and evaluates its specified section.
Source: Coste, Real Algebraic Sets (2005), Theorem 1.3, root-section assembly step. -/
theorem s2v_t11b_finite_graph_homeomorph_apply {B : Type*} [TopologicalSpace B] {m : ℕ}
    (ψ : Fin m → B → ℝ) (hψ : ∀ i, Continuous (ψ i))
    (hinj : ∀ b, Function.Injective (fun i => ψ i b)) (i : Fin m) (b : B) :
    (s2v_t11b_finite_graph_homeomorph ψ hψ hinj (i, b)).val = (b, ψ i b) := by
  rfl

end HodgeLean.Foundations.Program
