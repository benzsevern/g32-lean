import HodgeLean.Foundations.Program.ComponentTransportNormalizedProofs

/-! # Normalized certificate path: endpoints, normalization, loop words (FROZEN SPEC)
Implication from the half-twist realization to explicit endpoint labels of realized signed words
and of the certificate word; the identification of that label permutation with
`b65u_endpointPerm`; the relabelled centre and the affine normalization `M z = c₈ (1 - z)` with
their properties; and implication from the Hurwitz loop-word identity and the certified
lasso monodromy to generator values under one common conjugator.

Not claimed: the monodromy hypothesis `hmon` of `b65u_chain_unlabelled_of_path` (stage S4), a
body for `b65y_certified_chain_unlabelled_aux` (stage S5), any comparison of individual
conjugacy classes, or a common conjugator for the raw `τ`-reindexed tuples (there is none).
No witness is taken from an open statement. HC no distance; AV milestone no distance.
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

/-- Finite signed words are realized by ambient isotopies whose endpoint carries mark `k` to
mark `(Fin.revPerm * b65u_movePerm w * Fin.revPerm) k`, fixing `∞` and the base point, with the
Hurwitz action on the based column loops. This strengthens the existential endpoint of
`b66h_word_realization`, which stays as it is.
Source: Völklein, *Groups as Galois Groups*, Chapters 9–10; `b66h_half_twist`,
`b66h_track_endpoints`, `b66h_cons` (`HalfTwistWord.lean`, list-order composition `H₁ ∘ H₂`,
`σ₁ ∘ σ₂`); review hlean-rev-rle (2026-11-05), Q5. -/
theorem b65v_word_endpoint (w : List b65s_Move)
    (hw : ∀ m ∈ w, ∃ i : Fin 12, i ≠ 0 ∧ (m = .positive i ∨ m = .negative i)) :
    ∃ H : unitInterval → OnePoint ℂ ≃ₜ OnePoint ℂ,
      Continuous (fun q : unitInterval × OnePoint ℂ ↦ H q.1 q.2) ∧
      H 0 = Homeomorph.refl _ ∧
      (∀ t, H t OnePoint.infty = OnePoint.infty) ∧
      (∀ t, H t (mr_basePoint : OnePoint ℂ) = (mr_basePoint : OnePoint ℂ)) ∧
      (∀ k : Fin 12, H 1 (mr_marks k : OnePoint ℂ) =
        b6_branch mr_base
          ((Fin.revPerm * b65u_movePerm w * Fin.revPerm : Equiv.Perm (Fin 13)) k.castSucc)) ∧
      ∃ h : b6t_punctured mr_base ≃ₜ b6t_punctured mr_base,
        (∀ z, (h z : OnePoint ℂ) = H 1 z) ∧
        ∃ hb : h b63gP_basePoint = b63gP_basePoint,
          ∀ ρ : (FundamentalGroup (b6t_punctured mr_base) b63gP_basePoint)ᵐᵒᵖ →* b4b_Group, ∀ k,
            ρ (MulOpposite.op ((FundamentalGroup.mapOfEq ⟨h, h.continuous⟩ hb)
            (MulOpposite.unop (b66h_loop k)))) =
              b65s_word w (fun i ↦ ρ (b66h_loop i)) k :=
  b65v_word_endpoint_aux w hw

example := @b65v_word_endpoint

/-- The certificate word realizes the literal final column tuple up to its specified
conjugation, by an ambient isotopy whose endpoint carries mark `k` to mark
`(Fin.revPerm * b65u_movePerm b65b_word * Fin.revPerm) k`. This strengthens the existential
endpoint of `b66h_certificate_realization`, which stays as it is.
Source: B65-BRAIDCERT REPORT §1.5; `b65b_word`, `b65b_replay`; `b66h_word_body`;
Völklein, *Groups as Galois Groups*, Chapters 9–10. -/
theorem b65v_certificate_endpoint
    (ρ : (FundamentalGroup (b6t_punctured mr_base) b63gP_basePoint)ᵐᵒᵖ →* b4b_Group)
    (hρ : ∀ i, ρ (b66h_loop i) = b65s_columnRoot i) :
    ∃ H : unitInterval → OnePoint ℂ ≃ₜ OnePoint ℂ,
      Continuous (fun q : unitInterval × OnePoint ℂ ↦ H q.1 q.2) ∧
      H 0 = Homeomorph.refl _ ∧
      (∀ t, H t OnePoint.infty = OnePoint.infty) ∧
      (∀ t, H t (mr_basePoint : OnePoint ℂ) = (mr_basePoint : OnePoint ℂ)) ∧
      (∀ k : Fin 12, H 1 (mr_marks k : OnePoint ℂ) =
        b6_branch mr_base
          ((Fin.revPerm * b65u_movePerm b65b_word * Fin.revPerm : Equiv.Perm (Fin 13)) k.castSucc)) ∧
      ∃ h : b6t_punctured mr_base ≃ₜ b6t_punctured mr_base,
        (∀ z, (h z : OnePoint ℂ) = H 1 z) ∧
        ∃ hb : h b63gP_basePoint = b63gP_basePoint,
          ∀ i, ρ (MulOpposite.op ((FundamentalGroup.mapOfEq ⟨h, h.continuous⟩ hb)
            (MulOpposite.unop (b66h_loop i)))) =
            b4_conjTuple (b4b_generators 1)⁻¹ b65b_final i :=
  b65v_certificate_endpoint_aux ρ hρ

example := @b65v_certificate_endpoint

/-- The label permutation of the realized certificate word is the composed endpoint
permutation `b65u_endpointPerm`; it fixes `∞`, and the certified labels it assigns to the
reference labels `10` and `11` (the points `0` and `1`) are `8` and `10`.
Source: `b65u_movePerm`, `b65u_endpointPerm`, `b65u_sourcePerm`, `b65u_slotPerm`
(`ComponentTransportRelabelDefs.lean`); finite computation. -/
theorem b65v_endpoint_word :
    Fin.revPerm * b65u_movePerm b65b_word * Fin.revPerm = b65u_endpointPerm ∧
      b65u_endpointPerm.symm 10 = 8 ∧ b65u_endpointPerm.symm 11 = 10 ∧
      b65u_endpointPerm 12 = 12 :=
  b65v_endpoint_word_aux

example := @b65v_endpoint_word

/-- The relabelled centre lies in the chart, and the affine map `M z = c₈ (1 - z)` fixing `∞`
carries its label `τ j` to label `j` of the G32 centre, is biholomorphic, and maps its punctured
sphere onto that of the G32 centre.
Source: `b65v_relabelCentre`, `b65u_endpointPerm`; G32 v0.16, §3.1 (normalization of three
branch points); Forster, *Lectures on Riemann Surfaces*, §1.3 (the chart at `∞`). -/
theorem b65v_relabel_normalization (p : Fin 12 → ℂ) (hc : b65z_centre p ∈ b6_chart)
    (M : OnePoint ℂ ≃ₜ OnePoint ℂ)
    (hMz : ∀ z : ℂ, M z = ((b65z_centre p 8 * (1 - z) : ℂ) : OnePoint ℂ))
    (hMinf : M OnePoint.infty = OnePoint.infty) :
    b65v_relabelCentre p ∈ b6_chart ∧
      (∀ j, M (b6_branch (b65v_relabelCentre p) (b65u_endpointPerm j)) =
        b6_branch (b65z_centre p) j) ∧
      ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω M ∧ ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω M.symm ∧
      M '' b6t_punctured (b65v_relabelCentre p) = b6t_punctured (b65z_centre p) :=
  b65v_relabel_normalization_aux p hc M hMz hMinf

example := @b65v_relabel_normalization

/-- Generator values from the loop-word identity: if the certificate word applied to the
transported column loops equals the two path moves applied to inverted loops whose monodromy is
`(b65b_initial i)⁻¹`, then, at a suitable lift over the image of the base point, the monodromy
of every named loop is the conjugate of `b4b_root k` by one common element.
Source: `b65b_replay`, `b65b_path_replay` (B65-BRAIDCERT REPORT §1.5); `b65s_word`
(Völklein, *Groups as Galois Groups*, Chapters 9–10); `b65u_basepoint_adjust` (Hatcher,
*Algebraic Topology*, §1.3, Proposition 1.30). -/
theorem b65v_generator_values {c : Fin 10 → ℂ} {g : Fin 13 → b4b_Group}
    (D : b65z_SharedFamily c g) (y : b6t_punctured c) (u₀ : D.atlas.π ⁻¹' {y})
    (ℓ : Fin 13 → FundamentalGroup (b6t_punctured c) y)
    (hmono : ∀ i, D.atlas.hπ.fundamentalGroupToMulOpposite u₀ (ℓ i) =
      MulOpposite.op (b65b_initial i)⁻¹)
    (Ψ : b6t_punctured mr_base ≃ₜ b6t_punctured c) (β : Path (Ψ b63gP_basePoint) y)
    (hword : ∀ ρ : (FundamentalGroup (b6t_punctured c) y)ᵐᵒᵖ →* b4b_Group,
      b65s_word b65b_word (fun k ↦ ρ (MulOpposite.op
        (FundamentalGroup.fundamentalGroupMulEquivOfPath β
          (FundamentalGroup.map ⟨Ψ, Ψ.continuous⟩ b63gP_basePoint
            (MulOpposite.unop (b66h_loop k)))))) =
      b65s_word b65b_pathWord (fun j ↦ (ρ (MulOpposite.op (ℓ j)))⁻¹)) :
    ∃ w₁ : D.atlas.π ⁻¹' {Ψ b63gP_basePoint}, ∃ a : b4b_Group, ∀ k,
      MulOpposite.unop ((D.atlas.hπ.fundamentalGroupToMulOpposite w₁)
        (FundamentalGroup.map ⟨Ψ, Ψ.continuous⟩ b63gP_basePoint (b63gP_loops k))) =
      a * b4b_root k * a⁻¹ :=
  b65v_generator_values_aux D y u₀ ℓ hmono Ψ β hword

example := @b65v_generator_values

end HodgeLean.Foundations.Program
