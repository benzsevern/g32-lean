import HodgeLean.Foundations.Program.ComponentTransportRelabelProofs

/-! # Relabelling edge, unlabelled chain from a path, certificate endpoint (FROZEN SPEC)
Implication from matching based monodromy through a biholomorphic sphere map to an unlabelled
edge of retained charts; implication from a path in `b6_chart` and full monodromy equality after
a relabelling map to the unlabelled chain from the reference chart to the G32 centre; the
composed certificate endpoint equation at the G32 centre, with its explicit label permutation
and its comparison with the class table; generation of the reference fundamental group by the
named loops; lift and base-point adjustment of covering monodromy.

Not claimed: that the realized braid path of the certificate induces `b65u_endpointPerm` on
branch labels, the normalized path, the Möbius normalization map, the comparison of radial and
ambient transport, or the monodromy hypothesis of the path statement for the certified data.
No statement here supplies `b65y_certified_chain_unlabelled`; no witness is taken from an open
statement. HC no distance; AV milestone no distance.
-/
noncomputable section
open Set Manifold Filter Topology HodgeLean.Papers
open scoped ContDiff TensorProduct
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

/-- Two retained charts whose based monodromies agree through the punctured restriction of a
biholomorphic map of the sphere are joined by an unlabelled edge at their centres; the glue
covers that map.
Source: `b6m_based_filling_comparison` (Hatcher, Theorem 1.38; Forster, Theorem 8.4) for the
cover of `D₂` pulled back along `Φ`; `b63g5_fibre_filling`; `b65y_homeomorph_comp_monodromy`;
review hlean-rev-ctpu (2026-11-05), planned stage `b65y_relabel_edge`. -/
theorem b65u_relabel_edge {c₁ c₂ : Fin 10 → ℂ} {g₁ g₂ : Fin 13 → b4b_Group}
    (D₁ : b65z_SharedFamily c₁ g₁) (D₂ : b65z_SharedFamily c₂ g₂)
    (M : OnePoint ℂ ≃ₜ OnePoint ℂ)
    (hM : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω M) (hM' : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω M.symm)
    (Φ : b6t_punctured c₁ ≃ₜ b6t_punctured c₂) (hΦ : ∀ x, (Φ x : OnePoint ℂ) = M x)
    (y : b6t_punctured c₁) (u₁ : D₁.atlas.π ⁻¹' {y}) (u₂ : D₂.atlas.π ⁻¹' {Φ y})
    (h : (D₂.atlas.hπ.fundamentalGroupToMulOpposite u₂).comp
        (FundamentalGroup.map ⟨Φ, Φ.continuous⟩ y) =
      D₁.atlas.hπ.fundamentalGroupToMulOpposite u₁) :
    ∃ E : b65y_UnlabelledEdge ⟨c₁, g₁, D₁⟩ ⟨c₂, g₂, D₂⟩,
      E.t₀ = b65z_s₀ c₁ ∧ E.t₁ = b65z_s₀ c₂ ∧
      ∀ z, b63d_projection c₂ D₂.C D₂.atlas.f (b6t_polydisc c₂) (Set.Subset.refl _) E.t₁
          (E.glue z) =
        M (b63d_projection c₁ D₁.C D₁.atlas.f (b6t_polydisc c₁) (Set.Subset.refl _) E.t₀ z) :=
  b65u_relabel_edge_aux D₁ D₂ M hM hM' Φ hΦ y u₁ u₂ h

example := @b65u_relabel_edge

/-- The unlabelled chain from the retained reference chart to a chart at the G32 centre, from a
path in `b6_chart` and a biholomorphic relabelling map, provided that after every valid uniform
subdivision the composite of the radial pushes and the relabelling map carries the based
monodromy of the reference family to that of `D` (full monodromy equality).
Source: `b65y_path_subdivision`, `b65y_radial_homeomorph`, `b65y_walk_radial`,
`b65y_map_surjective`, `b65u_relabel_edge`, `b65y_unlabelledWalk_of_walk`,
`b65y_unlabelled_chain_of_walk`; G32 v0.16, §3.1 and proof of Lemma 3.4; review
hlean-rev-ctpu (2026-11-05), planned stage `b65y_certified_chain_unlabelled_of_path`. -/
theorem b65u_chain_unlabelled_of_path (p : Fin 12 → ℂ)
    (g : Fin 13 → b4b_Group) (D : b65z_SharedFamily (b65z_centre p) g)
    (R : rf8_SharedFamily) (v₀ : R.atlas.π ⁻¹' {b63gP_basePoint})
    (c : Fin 10 → ℂ) (γ : C(unitInterval, Fin 10 → ℂ)) (hγ : ∀ τ, γ τ ∈ b6_chart)
    (hγ0 : γ 0 = mr_base) (hγ1 : γ 1 = c)
    (M : OnePoint ℂ ≃ₜ OnePoint ℂ)
    (hM : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω M) (hM' : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω M.symm)
    (hMc : M '' b6t_punctured c = b6t_punctured (b65z_centre p))
    (hmon : ∀ N : ℕ, 0 < N →
      (∀ k < N, b65y_sample γ N (k + 1) ∈ b6t_polydisc (b65y_sample γ N k)) →
      ∀ Ψ : b6t_punctured mr_base ≃ₜ b6t_punctured (b65z_centre p),
        (∀ x, (Ψ x : OnePoint ℂ) = M (b65y_radial (b65y_sample γ N) N x)) →
        ∃ w : D.atlas.π ⁻¹' {Ψ b63gP_basePoint},
          (D.atlas.hπ.fundamentalGroupToMulOpposite w).comp
            (FundamentalGroup.map ⟨Ψ, Ψ.continuous⟩ b63gP_basePoint) =
          R.atlas.hπ.fundamentalGroupToMulOpposite v₀) :
    ∃ H : b65y_UnlabelledHurwitzChain,
      H.chart 0 = (⟨mr_base, b4b_root, b65z_ofRetained R⟩ : b65y_Chart) ∧
      H.chart (Fin.last H.n) = (⟨b65z_centre p, g, D⟩ : b65y_Chart) :=
  b65u_chain_unlabelled_of_path_aux p g D R v₀ c γ hγ hγ0 hγ1 M hM hM' hMc hmon

example := @b65u_chain_unlabelled_of_path

/-- The composed certificate endpoint equation at the G32 centre. Let `μ i` be the monodromy
of `D` on the certified loop `δ i` of slot `i`. The 86-move word acting on `b65s_columnRoot`
equals, after the certificate conjugation, the two path moves acting on the inverted tuple
`(μ i)⁻¹`; and in branch-label coordinates `j = 12 - b65x_slot i`, the monodromy at certified
label `j` is conjugate to `b4b_root (b65u_endpointPerm j)`.
Source: `b65b_replay`, `b65b_path_replay` (B65-BRAIDCERT REPORT §1.5); `b65s_word`,
`b65s_step` (Völklein, *Groups as Galois Groups*, Chapters 9–10); `b65s_columnRoot`,
`b65b_lasso`, `b65x_slot`; review hlean-rev-ctpu (2026-11-05), endpoint equation. -/
theorem b65u_endpoint_equation (p : Fin 12 → ℂ)
    (hp : ∀ k : Fin 12,
      |(p (b65b_boxIndex k)).re - ((b65b_boxCentre k).1 : ℝ)| < (1/10000 : ℝ) ∧
      |(p (b65b_boxIndex k)).im - ((b65b_boxCentre k).2 : ℝ)| < (1/10000 : ℝ) ∧
      b65r_P (b65b_boxFibre k) (p (b65b_boxIndex k)) = 0)
    (g : Fin 13 → b4b_Group) (D : b65z_SharedFamily (b65z_centre p) g)
    (e : b65s_sphere ≃ₜ b6t_punctured (b65z_centre p))
    (he : ∀ z, (e z : OnePoint ℂ) = b65p_mobius (p 10) (p 11) z)
    (x : b65s_regular) (u₀ : D.atlas.π ⁻¹' {e (b65s_inclusion x)})
    (δ : Fin 13 → Path x x)
    (hδ : ∀ i s, (δ i s).val = b65b_inverseNormalization (b65b_lasso (b65x_slot i) s))
    (hmono : ∀ i, ((D.atlas.hπ.fundamentalGroupToMulOpposite u₀).comp
        (FundamentalGroup.map ((⟨e, e.continuous⟩ :
          C(b65s_sphere, b6t_punctured (b65z_centre p))).comp b65s_inclusion) x))
          (FundamentalGroup.fromPath ⟦δ i⟧) = MulOpposite.op (b65b_initial i)⁻¹) :
    let μ : Fin 13 → b4b_Group := fun i ↦ MulOpposite.unop
      (((D.atlas.hπ.fundamentalGroupToMulOpposite u₀).comp
        (FundamentalGroup.map ((⟨e, e.continuous⟩ :
          C(b65s_sphere, b6t_punctured (b65z_centre p))).comp b65s_inclusion) x))
          (FundamentalGroup.fromPath ⟦δ i⟧))
    b65s_word b65b_word b65s_columnRoot =
        b4_conjTuple (b4b_generators 1)⁻¹ (b65s_word b65b_pathWord (fun i ↦ (μ i)⁻¹)) ∧
      ∀ j : Fin 13, IsConj (μ (b65u_slotPerm.symm j.rev)) (b4b_root (b65u_endpointPerm j)) :=
  b65u_endpoint_equation_aux p hp g D e he x u₀ δ hδ hmono

example := @b65u_endpoint_equation

/-- The composed endpoint permutation against the class table: the word part is the recorded
column permutation `p`; the permutation has the explicit values `[4,1,0,9,2,7,3,6,10,5,11,8,12]`;
it matches the class sequence of the review's label permutation `σ` and the determinant of the
inverted certified entry at every label; and it is not `σ`.
Source: `b65u_endpointPerm`; `b65y_rootClasses`, `b65y_classLabelPerm`, `b65y_wordPerm`,
`b65y_root_classes`, `b65y_initial_classes` (`ComponentTransportUnlabelledClasses.lean`);
review hlean-rev-ctpu (2026-11-05), exact class table. -/
theorem b65u_endpoint_classes :
    (∀ k, b65u_movePerm b65b_word k = b65y_wordPerm k) ∧
    (∀ j, b65u_endpointPerm j =
      (![4, 1, 0, 9, 2, 7, 3, 6, 10, 5, 11, 8, 12] : Fin 13 → Fin 13) j) ∧
    (∀ j, b65y_rootClasses (b65u_endpointPerm j) = b65y_rootClasses (b65y_classLabelPerm j)) ∧
    (∀ j, (b4b_toMatrix (b4b_root (b65u_endpointPerm j))).det =
      (b4b_toMatrix (b65b_initial (b65u_slotPerm.symm j.rev))⁻¹).det) ∧
    b65u_endpointPerm 0 ≠ b65y_classLabelPerm 0 :=
  b65u_endpoint_classes_aux

example := @b65u_endpoint_classes

/-- The named loops `b63gP_loops` generate the fundamental group of the punctured sphere at
`mr_base`.
Source: `mr_loops_universal`, `mr_loops_product` (Völklein, *Groups as Galois Groups*,
Theorem 4.3); `b64b_peripheral_generates`. -/
theorem b65u_loops_closure : Subgroup.closure (Set.range b63gP_loops) = ⊤ :=
  b65u_loops_closure_aux

example := @b65u_loops_closure

/-- Lift adjustment: if the monodromy at a lift agrees on a generating family with a given
homomorphism up to one simultaneous conjugation, another lift over the same point has exactly
that monodromy.
Source: Mathlib `IsQuotientCoveringMap.fundamentalGroupToMulOpposite_toPermFiber`;
Hatcher, *Algebraic Topology*, §1.3. -/
theorem b65u_lift_adjust {X U G : Type} [TopologicalSpace X] [TopologicalSpace U]
    [Group G] [MulAction G U] (π : U → X) (hπ : IsQuotientCoveringMap π G)
    (y : X) (u : π ⁻¹' {y}) {r : ℕ} (γ : Fin r → FundamentalGroup X y)
    (hγ : Subgroup.closure (Set.range γ) = ⊤) (φ : FundamentalGroup X y →* Gᵐᵒᵖ) (a : G)
    (h : ∀ i, MulOpposite.unop (hπ.fundamentalGroupToMulOpposite u (γ i)) =
      a * MulOpposite.unop (φ (γ i)) * a⁻¹) :
    ∃ w : π ⁻¹' {y}, hπ.fundamentalGroupToMulOpposite w = φ :=
  b65u_lift_adjust_aux π hπ y u γ hγ φ a h

example := @b65u_lift_adjust

/-- Base-point adjustment: along a path `β` from `y` to `y'`, the end of the lift of `β` from
`u` is a lift over `y'` whose monodromy on `β⁻¹ η β` is the monodromy at `u` on `η`.
Source: Mathlib `IsCoveringMap.monodromy`, `IsCoveringMap.liftPath`; Hatcher, *Algebraic
Topology*, §1.3, Proposition 1.30. -/
theorem b65u_basepoint_adjust {X U G : Type} [TopologicalSpace X] [TopologicalSpace U]
    [Group G] [MulAction G U] (π : U → X) (hπ : IsQuotientCoveringMap π G)
    {y y' : X} (β : Path y y') (u : π ⁻¹' {y}) :
    ∃ u' : π ⁻¹' {y'}, ∀ η : Path y y,
      hπ.fundamentalGroupToMulOpposite u'
          (FundamentalGroup.fromPath ⟦β.symm.trans (η.trans β)⟧) =
        hπ.fundamentalGroupToMulOpposite u (FundamentalGroup.fromPath ⟦η⟧) :=
  b65u_basepoint_adjust_aux π hπ β u

example := @b65u_basepoint_adjust

end HodgeLean.Foundations.Program
