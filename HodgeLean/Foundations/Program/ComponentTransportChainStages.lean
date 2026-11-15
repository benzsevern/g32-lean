import HodgeLean.Foundations.Program.ComponentTransportChainStagesProofs

/-! # Chain stages S4 and S5: monodromy from generator values, the chain from the path (FROZEN SPEC)
Existence of the affine normalization map `M z = c₈ (1 - z)` fixing `∞` at a G32 centre in the
chart; implication from generator values under one common conjugator to the full monodromy
equality consumed by `b65u_chain_unlabelled_of_path` (stage S4); and implication from the
conclusion of the set-aside path statement `b65v_normalized_path`, taken as the explicit
hypothesis `hpath`, to the unlabelled certified chain from the retained reference chart to the
G32 centre (stage S5 with the path as a binder).

Not claimed: the normalized path itself. `b65v_normalized_path` has no body and is not on this
base (its signature is in `docs/specs/spec-chs.md`, "Set aside (2026-11-05)"), so the existence
of the unlabelled certified chain still waits on it. No body for
`b65y_certified_chain_unlabelled_aux`, which is off this base. No witness is taken from an open
statement. HC no distance; AV milestone no distance.
-/
noncomputable section
open Set Manifold Filter Topology HodgeLean.Papers
open scoped ContDiff
namespace HodgeLean.Foundations.Program
attribute [local instance] b4cov_sphChartedSpace b4cov_sph_isManifold
attribute [local instance] b65z_SharedFamily.topC b65z_SharedFamily.chartC
  b65z_SharedFamily.manC b65z_SharedFamily.t2C b65z_SharedFamily.compactC
  b65z_SharedFamily.connectedC b65z_SharedFamily.actionC b65z_SharedFamily.totalChart
  b65z_SharedFamily.totalMan b65z_SharedFamily.fibreChart b65z_SharedFamily.fibreMan
  b65z_SharedFamily.fibreT2 b65z_SharedFamily.fibreCompact b65z_SharedFamily.fibreConnected
  b65z_SharedFamily.fibreFaithful
attribute [local instance] rf8_SharedFamily.topC rf8_SharedFamily.chartC
  rf8_SharedFamily.manC rf8_SharedFamily.t2C rf8_SharedFamily.compactC
  rf8_SharedFamily.connectedC rf8_SharedFamily.actionC rf8_SharedFamily.totalChart
  rf8_SharedFamily.totalMan rf8_SharedFamily.fibreChart rf8_SharedFamily.fibreMan
  rf8_SharedFamily.fibreT2 rf8_SharedFamily.fibreCompact rf8_SharedFamily.fibreConnected
  rf8_SharedFamily.fibreFaithful

/-- At a G32 centre in the chart, there is a homeomorphism of the sphere that is the affine map
`z ↦ c₈ (1 - z)` on `ℂ` and fixes `∞`, with `c₈ = b65z_centre p 8`; this is the map `M` of
`b65v_relabel_normalization` and of the set-aside path statement.
Source: `b65v_relabel_normalization` (`c₈ ≠ 0`, since branch labels 8 and 10 of a chart point
differ); Mathlib `Homeomorph.onePointCongr`; G32 v0.16, §3.1. -/
theorem b65v_relabel_map_exists (p : Fin 12 → ℂ) (hc : b65z_centre p ∈ b6_chart) :
    ∃ M : OnePoint ℂ ≃ₜ OnePoint ℂ,
      (∀ z : ℂ, M z = ((b65z_centre p 8 * (1 - z) : ℂ) : OnePoint ℂ)) ∧
      M OnePoint.infty = OnePoint.infty :=
  b65v_relabel_map_exists_aux p hc

example := @b65v_relabel_map_exists

/-- Stage S4. If, at a lift over the image of the base point, the monodromy of `D` on the image
of every named loop is the conjugate of `b4b_root k` by one common element, and the reference
monodromy takes the named loops to `b4b_root`, then some lift over the same point carries the
reference monodromy exactly through `Ψ` (the hypothesis `hmon` of
`b65u_chain_unlabelled_of_path`).
Source: `b65u_lift_adjust` (Hatcher, *Algebraic Topology*, §1.3); `b65u_loops_closure`
(Völklein, *Groups as Galois Groups*, Theorem 4.3); `b65y_map_surjective`; spec-chs, planned
stage S4. -/
theorem b65v_hmon_of_values {c : Fin 10 → ℂ} {g : Fin 13 → b4b_Group}
    (D : b65z_SharedFamily c g) (R : rf8_SharedFamily) (v₀ : R.atlas.π ⁻¹' {b63gP_basePoint})
    (hroot : ∀ i, R.atlas.hπ.fundamentalGroupToMulOpposite v₀ (b63gP_loops i) =
      MulOpposite.op (b4b_root i))
    (Ψ : b6t_punctured mr_base ≃ₜ b6t_punctured c)
    (w₁ : D.atlas.π ⁻¹' {Ψ b63gP_basePoint}) (a : b4b_Group)
    (h : ∀ k, MulOpposite.unop ((D.atlas.hπ.fundamentalGroupToMulOpposite w₁)
        (FundamentalGroup.map ⟨Ψ, Ψ.continuous⟩ b63gP_basePoint (b63gP_loops k))) =
      a * b4b_root k * a⁻¹) :
    ∃ w : D.atlas.π ⁻¹' {Ψ b63gP_basePoint},
      (D.atlas.hπ.fundamentalGroupToMulOpposite w).comp
        (FundamentalGroup.map ⟨Ψ, Ψ.continuous⟩ b63gP_basePoint) =
      R.atlas.hπ.fundamentalGroupToMulOpposite v₀ :=
  b65v_hmon_of_values_aux D R v₀ hroot Ψ w₁ a h

example := @b65v_hmon_of_values

/-- Stage S5 with the path as a binder. The hypothesis `hpath` is the conclusion of the set-aside
statement `b65v_normalized_path` for these `p`, `e`, `x` and `δ`, verbatim, quantified over the
affine map `M`. From it, the certified lasso monodromy `hmono` and the reference values
`hroot`, there is an unlabelled certified chain from the retained reference chart to the chart
of `D` at the G32 centre, with the endpoints of the set-aside `b65y_certified_chain_unlabelled`.
This does not supply `hpath`.
Source: `b65v_relabel_map_exists`, `b65v_relabel_normalization`, `b65v_generator_values`,
`b65v_hmon_of_values`, `b65u_chain_unlabelled_of_path`; spec-chs, planned stage S5;
`docs/specs/ComponentTransport.md`, "Set aside (2026-11-05, unlabelled chain)". -/
theorem b65v_chain_of_normalized_path (p : Fin 12 → ℂ)
    (g : Fin 13 → b4b_Group) (D : b65z_SharedFamily (b65z_centre p) g)
    (e : b65s_sphere ≃ₜ b6t_punctured (b65z_centre p))
    (x : b65s_regular) (u₀ : D.atlas.π ⁻¹' {e (b65s_inclusion x)})
    (δ : Fin 13 → Path x x)
    (hmono : ∀ i, ((D.atlas.hπ.fundamentalGroupToMulOpposite u₀).comp
        (FundamentalGroup.map ((⟨e, e.continuous⟩ :
          C(b65s_sphere, b6t_punctured (b65z_centre p))).comp b65s_inclusion) x))
          (FundamentalGroup.fromPath ⟦δ i⟧) = MulOpposite.op (b65b_initial i)⁻¹)
    (R : rf8_SharedFamily)
    (v₀ : R.atlas.π ⁻¹' {b63gP_basePoint})
    (hroot : ∀ i, R.atlas.hπ.fundamentalGroupToMulOpposite v₀ (b63gP_loops i) =
      MulOpposite.op (b4b_root i))
    (hpath : ∀ M : OnePoint ℂ ≃ₜ OnePoint ℂ,
      (∀ z : ℂ, M z = ((b65z_centre p 8 * (1 - z) : ℂ) : OnePoint ℂ)) →
      M OnePoint.infty = OnePoint.infty →
      ∃ γ : C(unitInterval, Fin 10 → ℂ), (∀ τ, γ τ ∈ b6_chart) ∧ γ 0 = mr_base ∧
        γ 1 = b65v_relabelCentre p ∧
        ∀ N : ℕ, 0 < N →
          (∀ k < N, b65y_sample γ N (k + 1) ∈ b6t_polydisc (b65y_sample γ N k)) →
          ∀ Ψ : b6t_punctured mr_base ≃ₜ b6t_punctured (b65z_centre p),
            (∀ z, (Ψ z : OnePoint ℂ) = M (b65y_radial (b65y_sample γ N) N z)) →
            (∀ j, M (b65y_radial (b65y_sample γ N) N (b6_branch mr_base (b65u_endpointPerm j))) =
              b6_branch (b65z_centre p) j) ∧
            ∃ β : Path (Ψ b63gP_basePoint) (e (b65s_inclusion x)),
              ∀ ρ : (FundamentalGroup (b6t_punctured (b65z_centre p)) (e (b65s_inclusion x)))ᵐᵒᵖ →*
                  b4b_Group,
                b65s_word b65b_word (fun k ↦ ρ (MulOpposite.op
                  (FundamentalGroup.fundamentalGroupMulEquivOfPath β
                    (FundamentalGroup.map ⟨Ψ, Ψ.continuous⟩ b63gP_basePoint
                      (MulOpposite.unop (b66h_loop k)))))) =
                b65s_word b65b_pathWord (fun j ↦ (ρ (MulOpposite.op
                  (FundamentalGroup.map ((⟨e, e.continuous⟩ :
                    C(b65s_sphere, b6t_punctured (b65z_centre p))).comp b65s_inclusion) x
                    (FundamentalGroup.fromPath ⟦δ j⟧))))⁻¹)) :
    ∃ H : b65y_UnlabelledHurwitzChain,
      H.chart 0 = (⟨mr_base, b4b_root, b65z_ofRetained R⟩ : b65y_Chart) ∧
      H.chart (Fin.last H.n) = (⟨b65z_centre p, g, D⟩ : b65y_Chart) :=
  b65v_chain_of_normalized_path_aux p g D e x u₀ δ hmono R v₀ hroot hpath

example := @b65v_chain_of_normalized_path

end HodgeLean.Foundations.Program
