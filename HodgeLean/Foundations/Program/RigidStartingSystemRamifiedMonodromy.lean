import HodgeLean.Foundations.Program.RigidStartingSystemRamifiedLocalForm

noncomputable section
open Set Metric Filter
open scoped Topology
namespace HodgeLean.Foundations.Program

theorem b65r_ramified_local_conjugacy (E : Type*) [NormedAddCommGroup E] [NormedSpace ℂ E]
    [FiniteDimensional ℂ E]
    (R : E →L[ℂ] E) (B A : ℂ → E →L[ℂ] E) (d : ℝ) (hd : 0 < d)
    (hB : AnalyticOnNhd ℂ B (ball 0 d))
    (hnr : ∀ k : ℕ, 0 < k → Function.Bijective
      (fun T : E →L[ℂ] E ↦ (k : ℂ) • T-(R*T-T*R)))
    (φ g : ℂ → ℂ) (a : ℂ) (e : ℕ) (he : 0 < e)
    (hφ : AnalyticAt ℂ φ a) (hg : AnalyticAt ℂ g a) (hga : g a ≠ 0)
    (hfactor : ∀ z, φ z = (z-a)^e*g z)
    (hEq : A =ᶠ[𝓝[≠] a] fun z ↦ deriv φ z • ((φ z)⁻¹ • R+B (φ z))) :
    ∃ r : ℝ, 0 < r ∧ ∀ ρ : ℝ, 0 < ρ → ρ < r →
      ∃ C : (E →L[ℂ] E)ˣ, b65f_transport E A (b65f_circle a ρ) =
        (C : E →L[ℂ] E)*NormedSpace.exp ((2*Real.pi*Complex.I) • ((e : ℂ) • R))*↑(C⁻¹) := by
  obtain ⟨r0,hr0,K,hA0,hK0,hu,hgauge⟩ :=
    b65r_ramified_local_gauge E R B d hd hB hnr φ g a e he hφ hg hga hfactor
  have heq : ∀ᶠ z in 𝓝 a, z ∈ ({a}ᶜ : Set ℂ) →
      A z = deriv φ z • ((φ z)⁻¹ • R+B (φ z)) := eventually_nhdsWithin_iff.mp hEq
  obtain ⟨r1,hr1,hE⟩ := Metric.mem_nhds_iff.mp heq
  let r := min r0 r1
  have hs0 : ball a r ⊆ ball a r0 := ball_subset_ball (min_le_left _ _)
  have hs1 : ball a r ⊆ ball a r1 := ball_subset_ball (min_le_right _ _)
  have hA : AnalyticOnNhd ℂ A (ball a r \ {a}) := by
    intro z hz
    apply (hA0 z ⟨hs0 hz.1,hz.2⟩).congr
    filter_upwards [(isOpen_ball.sdiff isClosed_singleton).mem_nhds hz] with w hw
    exact (hE (hs1 hw.1) hw.2).symm
  have hG : ∀ z ∈ ball a r \ {a}, (z-a) • deriv K z =
      (z-a) • (A z*K z)-K z*((e : ℂ) • R) := by
    intro z hz
    have hh := hgauge z ⟨hs0 hz.1,hz.2⟩
    rw [← hE (hs1 hz.1) hz.2] at hh
    exact hh
  refine ⟨r,lt_min hr0 hr1,?_⟩
  intro ρ hρ hρr
  exact b65r_gauge_local_conjugacy E ((e : ℂ) • R) A K a r hA (hK0.mono hs0)
    (fun z hz ↦ hu z (hs0 hz)) hG ρ hρ hρr

end HodgeLean.Foundations.Program
