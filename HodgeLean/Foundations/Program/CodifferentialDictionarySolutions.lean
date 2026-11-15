import HodgeLean.Foundations.Program.CoverDictionarySolutions

/-! Solution supply retaining the absolute direction convention.
HC no distance; AV milestone no distance. -/

noncomputable section
open Set Metric Matrix Filter Manifold
open scoped Topology ContDiff
open HodgeLean.Papers
namespace HodgeLean.Foundations.Program
attribute [local instance] b4cov_sphChartedSpace b4cov_sph_isManifold
attribute [local instance] b65z_SharedFamily.topC b65z_SharedFamily.chartC
  b65z_SharedFamily.manC b65z_SharedFamily.t2C b65z_SharedFamily.compactC
  b65z_SharedFamily.connectedC b65z_SharedFamily.actionC b65z_SharedFamily.totalChart
  b65z_SharedFamily.totalMan b65z_SharedFamily.fibreChart b65z_SharedFamily.fibreMan
  b65z_SharedFamily.fibreT2 b65z_SharedFamily.fibreCompact b65z_SharedFamily.fibreConnected
  b65z_SharedFamily.fibreFaithful

/-- The cover solution supplier retains its conjugate representation convention.
Source: CoverDictionarySolutions.lean, b65g_cover_solutions_main and b65g_assemble. -/
theorem b66d_cover_solutions_conj (p : Fin 12 → ℂ) (O : b65p_Outputs p)
    {g : Fin 13 → b4b_Group} (D : b65z_SharedFamily (b65z_centre p) g)
    (e : b65s_sphere ≃ₜ b6t_punctured (b65z_centre p))
    (he : ∀ z, (e z : OnePoint ℂ) = b65p_mobius (p 10) (p 11) z)
    (x : b65s_regular) (u₀ : D.atlas.π ⁻¹' {e (b65s_inclusion x)})
    (C : ((Fin 4 → ℂ) →L[ℂ] (Fin 4 → ℂ))ˣ)
    (hT : ∀ η : Path x x,
      b65f_transport (Fin 4 → ℂ) b65r_pullback (fun t ↦ (η.extend t).val) =
        C.val * (b65s_column ((D.atlas.hπ.fundamentalGroupToMulOpposite u₀).comp
          (FundamentalGroup.map ((⟨e, e.continuous⟩ :
            C(b65s_sphere, b6t_punctured (b65z_centre p))).comp b65s_inclusion) x))
            (FundamentalGroup.fromPath ⟦η⟧)).val * (C⁻¹).val) :
    ∃ S : b65g_Solutions p O D, S.conj = true := by
  obtain ⟨ε, hε, hεO, hall⟩ := b65g_all_loop_transfer p O g D e he x u₀ C hT
  have h := fun θ (hθ : θ ∈ ball (0 : ℂ) ε)
      (t : b6t_polydisc (b65z_centre p)) (ht : t.val = b65p_curve p θ) ↦
    b65g_fibre_continuation_bar p O D θ (ball_subset_ball hεO hθ) t ht
      (hall θ hθ t ht).1 (hall θ hθ t ht).2
  classical
  choose Yf hYf using h
  let Y : ℂ → b6t_polydisc (b65z_centre p) × D.C → (Fin 4 → ℂ) →L[ℂ] (Fin 4 → ℂ) :=
    fun θ q ↦ if hq : θ ∈ ball (0 : ℂ) ε ∧ q.1.val = b65p_curve p θ then
      Yf θ hq.1 q.1 hq.2 ⟨q, rfl⟩ else 0
  have key : ∀ θ (hθ : θ ∈ ball (0 : ℂ) ε) (t : b6t_polydisc (b65z_centre p))
      (ht : t.val = b65p_curve p θ),
      (fun y : b65z_fibre (b65z_centre p) D.C t ↦ Y θ y.val) = Yf θ hθ t ht := by
    intro θ hθ t ht
    funext y
    obtain ⟨⟨q₁, q₂⟩, hq⟩ := y
    change q₁ = t at hq
    subst hq
    exact dite_eq_left (⟨hθ, ht⟩ : θ ∈ ball (0 : ℂ) ε ∧ q₁.val = b65p_curve p θ)
  have key' : ∀ θ (hθ : θ ∈ ball (0 : ℂ) ε) (t : b6t_polydisc (b65z_centre p))
      (ht : t.val = b65p_curve p θ) (y : b65z_fibre (b65z_centre p) D.C t),
      Y θ y.val = Yf θ hθ t ht y := fun θ hθ t ht y ↦ congrFun (key θ hθ t ht) y
  refine ⟨⟨ε, hε, hεO, true, Y, ?_, ?_, ?_⟩, rfl⟩
  · intro θ hθ t ht y hy
    rw [key' θ hθ t ht]
    exact (hYf θ hθ t ht y hy).1
  · intro θ hθ t ht y hy
    rw [key θ hθ t ht, key' θ hθ t ht]
    exact (hYf θ hθ t ht y hy).2.1
  · intro θ hθ t ht y hy k
    rw [key' θ hθ t ht, key' θ hθ t ht]
    exact (hYf θ hθ t ht y hy).2.2 k

example := @b66d_cover_solutions_conj

#print axioms b66d_cover_solutions_conj

end HodgeLean.Foundations.Program
