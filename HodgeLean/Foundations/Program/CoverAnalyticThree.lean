import HodgeLean.Foundations.Program.CoverAnalyticThreeProofs

/-! # The cover dictionary, stage 3: all-loop transfer (FROZEN SPEC)

Seven statements, prefixes `caf_` (general) and `b65g_` (cover family), on the route of
`docs/specs/CoverAnalyticTwo.md` (bridge (c) as amended), toward a body for
`b65g_cover_solutions_aux`. Specification: `docs/specs/CoverAnalyticThree.md`.

Claimed:
1. a quotient covering map pulls back along an equivariant open embedding of total spaces
   lying over an open embedding of bases, when the first embedding hits exactly the preimage of
   the image of the second;
2. the group-valued monodromy of quotient coverings is natural for equivariant maps over a
   continuous map of bases;
3. on the fibre over `b65p_curve p θ`, `θ` in the disc of a 5c record, the `s`-projection of the
   regular locus onto `ℂ` minus the poles is a quotient covering for the deck group;
4. the base of the system at `θ = 0`, `ℂ` minus the sixteen poles, is the printed regular domain
   `b65s_regular`;
5. implication from the identification `hT` of `b65g_cover_solutions` (an arbitrary
   identification `e`, `x`, `u₀`, `C`, all loops at `x`) to all-loop transfer
   (`b65g_loopTransfer`) on the actual fibre over `θ = 0`, in the `s`-coordinate;
6. implication from all-loop transfer at `θ = 0` to all-loop transfer at every small `θ`;
7. (`b65g_all_loop_transfer`) implication from `hT` to all-loop transfer at every small `θ`.

Not claimed: which of `ρ`, `ρ̄` the deck group uses; that the base point, the fibre point or
the operator at `θ` can be taken equal to `x`, `u₀`, `C`; the continuation of solutions to the
cover and the deck law (stage 5); the dictionary (stage 4); that `hT` holds for any particular
family (the named-loop supplier `b65z_schlesinger_identification` covers its selected family).
HC no distance; AV milestone no distance.
-/

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

/-- **Pulling back a quotient covering along open embeddings.** If `p : E → X` is a quotient
covering for `G`, `Φ : E' → E` is a `G`-equivariant open embedding, `ψ : X' → X` an open
embedding, `p ∘ Φ = ψ ∘ p'`, and the image of `Φ` is the preimage under `p` of the image of `ψ`,
then `p'` is a quotient covering for `G`. This covers restriction to the preimage of an open set
and a change of coordinates on either side.
Source: Hatcher, *Algebraic Topology*, §1.3 (covering spaces, restriction to open subsets, and
covering space actions); Mathlib `IsQuotientCoveringMap`, `IsQuotientCoveringMap.homeomorph_comp`. -/
theorem caf_isQuotientCoveringMap_of_isOpenEmbedding {E X E' X' G : Type*}
    [TopologicalSpace E] [TopologicalSpace X] [TopologicalSpace E'] [TopologicalSpace X']
    [Group G] [MulAction G E] [MulAction G E'] {p : E → X} {p' : E' → X'}
    (hp : IsQuotientCoveringMap p G) (Φ : E' → E) (ψ : X' → X)
    (hΦ : Topology.IsOpenEmbedding Φ) (hψ : Topology.IsOpenEmbedding ψ)
    (hequiv : ∀ (h : G) (e : E'), Φ (h • e) = h • Φ e)
    (hcomm : ∀ e, p (Φ e) = ψ (p' e)) (hrange : Set.range Φ = p ⁻¹' Set.range ψ) :
    IsQuotientCoveringMap p' G :=
  caf_isQuotientCoveringMap_of_isOpenEmbedding_aux hp Φ ψ hΦ hψ hequiv hcomm hrange

/-- The premises hold together for the identity maps on any quotient covering. -/
example {E X G : Type*} [TopologicalSpace E] [TopologicalSpace X] [Group G] [MulAction G E]
    {p : E → X} (_hp : IsQuotientCoveringMap p G) :
    Topology.IsOpenEmbedding (id : E → E) ∧ Topology.IsOpenEmbedding (id : X → X) ∧
      (∀ (h : G) (e : E), id (h • e) = h • id e) ∧ (∀ e, p (id e) = id (p e)) ∧
      Set.range (id : E → E) = p ⁻¹' Set.range (id : X → X) := by
  refine ⟨Topology.IsOpenEmbedding.id, Topology.IsOpenEmbedding.id, fun _ _ ↦ rfl,
    fun _ ↦ rfl, ?_⟩
  simp

/-- **Naturality of the deck monodromy.** For quotient coverings `p`, `p'` for the same group, a
continuous `G`-equivariant `Φ : E' → E` over a continuous `ψ : X' → X`, and fibre points `e'`
over `x'` and `e = Φ e'` over `ψ x'`, the group-valued monodromy of `p'` at `e'` is that of `p`
at `e` composed with `ψ_* : π₁(X', x') → π₁(X, ψ x')`: `Φ` maps the lift of `γ` at `e'` to the
lift of `ψ ∘ γ` at `e`.
Source: Hatcher, *Algebraic Topology*, §1.3 (path lifting, Proposition 1.30, and the deck
action on fibres); Mathlib `IsQuotientCoveringMap.fundamentalGroupToMulOpposite_apply_mk_eq`. -/
theorem caf_fundamentalGroupToMulOpposite_map {E X E' X' G : Type*}
    [TopologicalSpace E] [TopologicalSpace X] [TopologicalSpace E'] [TopologicalSpace X']
    [Group G] [MulAction G E] [MulAction G E'] {p : E → X} {p' : E' → X'}
    (hp : IsQuotientCoveringMap p G) (hp' : IsQuotientCoveringMap p' G)
    (Φ : E' → E) (ψ : C(X', X)) (hΦ : Continuous Φ)
    (hequiv : ∀ (h : G) (e : E'), Φ (h • e) = h • Φ e)
    (hcomm : ∀ e, p (Φ e) = ψ (p' e)) {x' : X'} (e' : p' ⁻¹' {x'}) (e : p ⁻¹' {ψ x'})
    (he : (e : E) = Φ e') (γ : FundamentalGroup X' x') :
    hp'.fundamentalGroupToMulOpposite e' γ =
      hp.fundamentalGroupToMulOpposite e (FundamentalGroup.map ψ x' γ) :=
  caf_fundamentalGroupToMulOpposite_map_aux hp hp' Φ ψ hΦ hequiv hcomm e' e he γ

/-- The premises hold together for the identity maps and the same fibre point. -/
example {E X G : Type*} [TopologicalSpace E] [TopologicalSpace X] [Group G] [MulAction G E]
    {p : E → X} (_hp : IsQuotientCoveringMap p G) {x : X} (e : p ⁻¹' {x}) :
    Continuous (id : E → E) ∧ (∀ (h : G) (e : E), id (h • e) = h • id e) ∧
      (∀ e, p (id e) = ContinuousMap.id X (p e)) ∧
      ∃ e₁ : p ⁻¹' {ContinuousMap.id X x}, (e₁ : E) = id e :=
  ⟨continuous_id, fun _ _ ↦ rfl, fun _ ↦ rfl, ⟨e, rfl⟩⟩

/-- **The regular locus covers the base.** For `θ` in the disc of a 5c record and `t` over
`b65p_curve p θ`, the `s`-projection of the regular locus of the fibre onto `ℂ` minus the
sixteen poles is a quotient covering for the deck group: the thirteen branch points of the fibre
are the images of the twelve moving poles and of `s = 0` (`O.normalization`), so the deck group
acts freely on the regular locus, its orbits are the fibres (`D.hgal`), and the projection is a
quotient map onto the base (`D.hsurj`, compactness).
Source: G32 v0.16, §5.5 (the covers `C_θ` over `ℙ¹_s`) and Definition 3.5; Forster, *Lectures on
Riemann Surfaces*, §4 (unbranched part of a Galois cover); `b65p_Outputs.normalization`,
`b65z_SharedFamily`. -/
theorem b65g_quotientCovering (p : Fin 12 → ℂ) (O : b65p_Outputs p)
    (g : Fin 13 → b4b_Group) (D : b65z_SharedFamily (b65z_centre p) g)
    (θ : ℂ) (hθ : θ ∈ ball (0 : ℂ) O.radius) (t : b6t_polydisc (b65z_centre p))
    (ht : t.val = b65p_curve p θ) :
    IsQuotientCoveringMap (b65g_sProj D t (b65p_moving p θ 10) (b65p_moving p θ 11)
      (b65p_poles p θ)) b4b_Group :=
  b65g_quotientCovering_aux p O g D θ hθ t ht

/-- The parameter binder `t` is available for every `θ` in the disc of the record. -/
example (p : Fin 12 → ℂ) (O : b65p_Outputs p) (θ : ℂ) (hθ : θ ∈ ball (0 : ℂ) O.radius) :
    ∃ t : b6t_polydisc (b65z_centre p), t.val = b65p_curve p θ :=
  ⟨⟨b65p_curve p θ, (O.curve_mem θ hθ).1⟩, rfl⟩

/-- **The base at `θ = 0`.** For a 5c record, `ℂ` minus the sixteen poles at `θ = 0` is the
printed regular domain `b65s_regular`: the fixed poles are `0, 3, 1, −2`; a moving pole in
`b65s_regular` would be a pole of the record's coefficient (nonzero residue) at a point where
`b65r_pullback` is analytic, and a root of `P₅` or `P₋₇` that is not a pole would be a pole of
`b65r_pullback` (residue a nonzero multiple of `B₅`, resp. `B₋₇`) where the record's coefficient
is analytic, against `O.base_coefficient`.
Source: G32 v0.16, §5.2 and §5.4 (the pullback system and its poles); `b65p_Outputs`,
`b65r_pullback`, `b65s_regular`. -/
theorem b65g_base_regular (p : Fin 12 → ℂ) (O : b65p_Outputs p) :
    b65g_U (b65p_poles p 0) = b65s_regular :=
  b65g_base_regular_aux p O

/-- The fixed pole `3` is excluded from both sides, for every `p`. -/
example (p : Fin 12 → ℂ) : (3 : ℂ) ∉ b65g_U (b65p_poles p 0) ∧ (3 : ℂ) ∉ b65s_regular := by
  refine ⟨fun h ↦ h ⟨Sum.inl 1, rfl⟩, fun h ↦ h.2.1 rfl⟩

/-- **Transfer at `θ = 0`.** Implication from an arbitrary identification of the family with
the printed base system (the homeomorphism `e`, the base point `x`, the fibre point `u₀`, the
operator `C`, and transport conjugate to the column monodromy along every loop at `x`) to
all-loop transfer on the actual fibre over `b65p_curve p 0`, for the system of `O` at `θ = 0` in
the `s`-coordinate: at `θ = 0` the fibre is the atlas surface (`b6t_sphere c c = id`), the
atlas embedding `D.atlas.ι` identifies the regular locus with an open part of the atlas cover,
and `O.base_coefficient` with `b65g_base_regular` identifies the systems.
Source: G32 v0.16, §5.5 (The direction) and §5.2; `rf7_HurwitzAtlas` (`hι`, `hproj`, `hequiv`);
`b65p_Outputs.base_coefficient`; `b65f_path_convergence`. -/
theorem b65g_base_transfer (p : Fin 12 → ℂ) (O : b65p_Outputs p) (g : Fin 13 → b4b_Group)
    (D : b65z_SharedFamily (b65z_centre p) g)
    (e : b65s_sphere ≃ₜ b6t_punctured (b65z_centre p))
    (he : ∀ z, (e z : OnePoint ℂ) = b65p_mobius (p 10) (p 11) z)
    (x : b65s_regular) (u₀ : D.atlas.π ⁻¹' {e (b65s_inclusion x)})
    (C : ((Fin 4 → ℂ) →L[ℂ] (Fin 4 → ℂ))ˣ)
    (hT : ∀ η : Path x x,
      b65f_transport (Fin 4 → ℂ) b65r_pullback (fun t ↦ (η.extend t).val) =
        C.val * (b65s_column ((D.atlas.hπ.fundamentalGroupToMulOpposite u₀).comp
          (FundamentalGroup.map ((⟨e, e.continuous⟩ :
            C(b65s_sphere, b6t_punctured (b65z_centre p))).comp b65s_inclusion) x))
            (FundamentalGroup.fromPath ⟦η⟧)).val * (C⁻¹).val)
    (t : b6t_polydisc (b65z_centre p)) (ht : t.val = b65p_curve p 0) :
    ∃ hπ : IsQuotientCoveringMap (b65g_sProj D t (b65p_moving p 0 10) (b65p_moving p 0 11)
        (b65p_poles p 0)) b4b_Group,
      b65g_loopTransfer D t (b65p_moving p 0 10) (b65p_moving p 0 11) (b65p_poles p 0)
        (O.residue 0) hπ :=
  b65g_base_transfer_aux p O g D e he x u₀ C hT t ht

/-- The binder `t` at `θ = 0` is the reference parameter of the polydisc. -/
example (p : Fin 12 → ℂ) : (b65z_s₀ (b65z_centre p)).val = b65p_curve p 0 := rfl

/-- **Transfer to nearby parameters.** Implication from all-loop transfer on the fibre over
`θ = 0` to all-loop transfer on the fibre over `b65p_curve p θ` for every small `θ`: the system
of `O` is isomonodromic (`O.schlesinger` is the integrability condition of
`dY = Σ_q A_q(θ) d log(s − t_q(θ)) · Y` in `(s, θ)`), the regular loci form a covering of the
complement of the moving poles in `(θ, s)` (the family over the polydisc), and this complement
fibres over the disc with connected fibres, so both monodromies extend from the fibre over
`θ = 0` and agree on every fibre, up to one conjugation.
Source: G32 v0.16, Lemma 5.6(2) and §5.5 (The direction); Jimbo–Miwa–Ueno, Physica D 2 (1981),
§2 (Schlesinger equations as isomonodromy); Malgrange, *Sur les déformations
isomonodromiques I*, 1983; `b6t_monodromy`. -/
theorem b65g_theta_transfer (p : Fin 12 → ℂ) (O : b65p_Outputs p)
    (g : Fin 13 → b4b_Group) (D : b65z_SharedFamily (b65z_centre p) g)
    (t₀ : b6t_polydisc (b65z_centre p)) (ht₀ : t₀.val = b65p_curve p 0)
    (h₀ : ∃ hπ : IsQuotientCoveringMap (b65g_sProj D t₀ (b65p_moving p 0 10)
        (b65p_moving p 0 11) (b65p_poles p 0)) b4b_Group,
      b65g_loopTransfer D t₀ (b65p_moving p 0 10) (b65p_moving p 0 11) (b65p_poles p 0)
        (O.residue 0) hπ) :
    ∃ ε : ℝ, 0 < ε ∧ ε ≤ O.radius ∧ ∀ θ ∈ ball (0 : ℂ) ε,
      ∀ t : b6t_polydisc (b65z_centre p), t.val = b65p_curve p θ →
      ∃ hπ : IsQuotientCoveringMap (b65g_sProj D t (b65p_moving p θ 10) (b65p_moving p θ 11)
          (b65p_poles p θ)) b4b_Group,
        b65g_loopTransfer D t (b65p_moving p θ 10) (b65p_moving p θ 11) (b65p_poles p θ)
          (O.residue θ) hπ :=
  b65g_theta_transfer_aux p O g D t₀ ht₀ h₀

example := @b65g_theta_transfer

/-- **All-loop transfer (bridge (c)).** Implication from an arbitrary identification `hT` of
the family with the printed base system, for all loops at `x`, to all-loop transfer on the
fibre over `b65p_curve p θ` for every small `θ`: the system of `O` at `θ`, in the
`s`-coordinate, has transport along every loop at some base point conjugate by one operator to
the column monodromy of the regular-locus covering at some fibre point.
Source: G32 v0.16, §5.5 (The direction: "for small `θ` the system at `θ` is the `ρ`-local
system of the cover `C_θ`") and Lemma 5.6(2); `b65g_base_transfer`, `b65g_theta_transfer`. -/
theorem b65g_all_loop_transfer (p : Fin 12 → ℂ) (O : b65p_Outputs p)
    (g : Fin 13 → b4b_Group) (D : b65z_SharedFamily (b65z_centre p) g)
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
    ∃ ε : ℝ, 0 < ε ∧ ε ≤ O.radius ∧ ∀ θ ∈ ball (0 : ℂ) ε,
      ∀ t : b6t_polydisc (b65z_centre p), t.val = b65p_curve p θ →
      ∃ hπ : IsQuotientCoveringMap (b65g_sProj D t (b65p_moving p θ 10) (b65p_moving p θ 11)
          (b65p_poles p θ)) b4b_Group,
        b65g_loopTransfer D t (b65p_moving p θ 10) (b65p_moving p θ 11) (b65p_poles p θ)
          (O.residue θ) hπ :=
  b65g_all_loop_transfer_aux p O g D e he x u₀ C hT

example := @b65g_all_loop_transfer

end HodgeLean.Foundations.Program
