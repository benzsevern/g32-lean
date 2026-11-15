module

public import HodgeLean.Foundations.Program.FiniteGroupLinearization

/-! # Invariant chart neighborhoods on a general source space
An equivariant coordinate map restricts to invariant convex model neighborhoods.
-/
public section
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open Filter TopologicalSpace
namespace HodgeLean.Foundations.Program

/-- Restrict an equivariant chart near a fixed point so that its image is invariant
and convex, while remaining in a prescribed source neighborhood.
Source: Takamura, Linearization of Quotient Families, J. Math. Sci. Univ.
Tokyo 26 (2019), pp. 380–382, invariant coordinate neighborhoods. -/
theorem equivariant_chart_invariant_neighborhood
    (G : Type*) [Group G] [Fintype G]
    {A E : Type*} [TopologicalSpace A] [NormedAddCommGroup E] [NormedSpace ℝ E]
    (a : G → A → A) (x₀ : A) (hfixed : ∀ g, a g x₀ = x₀)
    (hc : ∀ g, ContinuousAt (a g) x₀) (ρ : G →* (E ≃L[ℝ] E))
    (e : OpenPartialHomeomorph A E) (hx : x₀ ∈ e.source) (he0 : e x₀ = 0)
    (Q : Set A) (hQ : Q ∈ nhds x₀)
    (hequiv : ∀ g x, x ∈ Q → e (a g x) = ρ g (e x))
    (N : Set A) (hN : N ∈ nhds x₀) :
    ∃ V W, IsOpen V ∧ x₀ ∈ V ∧ V ⊆ N ∧ V ⊆ Q ∧ V ⊆ e.source ∧
      IsOpen W ∧ (0 : E) ∈ W ∧ Convex ℝ W ∧ e '' V = W ∧
      (∀ g x, x ∈ V → a g x ∈ V) ∧ (∀ g x, x ∈ W → ρ g x ∈ W) := by
  have hpre (g : G) : (a g) ⁻¹' e.source ∈ nhds x₀ :=
    (hc g).preimage_mem_nhds (by rw [hfixed g]; exact e.open_source.mem_nhds hx)
  have hb := inter_mem hN (inter_mem hQ (inter_mem (e.open_source.mem_nhds hx)
    (iInter_mem.mpr hpre)))
  obtain ⟨O, hOsub, hOo, hxO⟩ := mem_nhds_iff.mp hb
  have hOsource : O ⊆ e.source := fun _ hz => (hOsub hz).2.2.1
  have himage0 : (0 : E) ∈ e '' O := ⟨x₀, hxO, he0⟩
  obtain ⟨W, hWo, hW0, hWO, hWconv, hWinv⟩ :=
    finite_linear_action_invariant_convex_nhds G ρ (e '' O)
      ((e.isOpen_image_of_subset_source hOo hOsource).mem_nhds himage0)
  let V := e.source ∩ e ⁻¹' W
  have hVO : V ⊆ O := by
    intro x hv
    obtain ⟨z, hz, hez⟩ := hWO hv.2
    have hzx := e.injOn (hOsource hz) hv.1 hez
    simpa only [hzx] using hz
  refine ⟨V, W, e.isOpen_inter_preimage hWo, ⟨hx, ?_⟩,
    (fun _ hv => (hOsub (hVO hv)).1), (fun _ hv => (hOsub (hVO hv)).2.1),
    Set.inter_subset_left, hWo, hW0, hWconv, ?_, ?_, hWinv⟩
  · change e x₀ ∈ W
    rw [he0]
    exact hW0
  · apply Set.Subset.antisymm
    · rintro y ⟨x, hv, rfl⟩
      exact hv.2
    · intro y hy
      obtain ⟨z, hz, hez⟩ := hWO hy
      refine ⟨z, ⟨hOsource hz, ?_⟩, hez⟩
      change e z ∈ W
      rw [hez]
      exact hy
  · intro g x hv
    refine ⟨Set.mem_iInter.mp (hOsub (hVO hv)).2.2.2 g, ?_⟩
    change e (a g x) ∈ W
    rw [hequiv g x (hOsub (hVO hv)).2.1]
    exact hWinv g (e x) hv.2

end HodgeLean.Foundations.Program
