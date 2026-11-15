import HodgeLean.Foundations.Program.PullbackMonodromyFoundationsCovering

/-! # Assembly of the surjective pullback representation

The four steps of the specification: the pullback representation with its transport identity,
descent to the sphere, the index bound from the degree-six covering, and a conjugate of the first
reflection in the image, with `b65s_small_index`. The puncture filling enters as the hypothesis
`b65t_FillProp`, the statement of `b65t_puncture_fill`.
HC no distance; AV milestone no distance.
-/

noncomputable section
open Set Metric Filter
open scoped Topology
namespace HodgeLean.Foundations.Program

/-- The four-step assembly of the surjective pullback representation, from the puncture filling.
Source: G32 v0.16, §5.2, proof of Lemma surj. -/
theorem b65t_pullback_monodromy_of_fill (hfill : b65t_FillProp) (x : b65s_regular) :
    ∃ ρ : FundamentalGroup b65s_sphere (b65s_inclusion x) →* b4b_Group,
      Function.Surjective ρ ∧
      ∃ C : ((Fin 4 → ℂ) →L[ℂ] (Fin 4 → ℂ))ˣ,
        ∀ γ : Path x x,
          b65f_transport (Fin 4 → ℂ) b65r_pullback (fun t ↦ (γ.extend t).val) =
            (C : (Fin 4 → ℂ) →L[ℂ] (Fin 4 → ℂ)) *
              b65r_operator (b4b_toMatrix
                (ρ (FundamentalGroup.map b65s_inclusion x
                  (FundamentalGroup.fromPath ⟦γ⟧)))) * ↑(C⁻¹) := by
  obtain ⟨ρ₀, hρ₀, C, hC⟩ := b65r_four_point_monodromy (b65t_phiC x)
  let ρr := ρ₀.comp (FundamentalGroup.map b65t_phiC x)
  have hρr : ∀ γ : Path x x,
      b65f_transport (Fin 4 → ℂ) b65r_pullback (fun t ↦ (γ.extend t).val) =
        (C : (Fin 4 → ℂ) →L[ℂ] (Fin 4 → ℂ)) *
          b65r_operator (b4b_toMatrix (ρr (FundamentalGroup.fromPath ⟦γ⟧))) * ↑(C⁻¹) := by
    intro γ
    rw [b65t_pullback_transport_proof x x γ]
    exact hC (γ.map b65t_phiC.continuous)
  obtain ⟨σ, hσr, hσ⟩ := b65t_descent hfill x ρr C hρr
  have hidx := b65t_index_bound hfill x ρ₀ hρ₀
  have htop := b65s_small_index ρr.range hidx (b65t_reflection_in_image_proof x ρr C hρr)
  refine ⟨σ, ?_, C, fun γ ↦ ?_⟩
  · rw [← MonoidHom.range_eq_top, hσr, htop]
  · rw [hσ]
    exact hρr γ

end HodgeLean.Foundations.Program
