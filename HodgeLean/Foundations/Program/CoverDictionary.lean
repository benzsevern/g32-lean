import HodgeLean.Foundations.Program.CoverDictionaryProofs

/-! # B6-5 stage 5d, geometric part: the cover dictionary at the G32 centre

Implication from a 5c record `O : b65p_Outputs p`, a family `D : b65z_SharedFamily (b65z_centre p) g`
at the G32 centre and its identification with the base Schlesinger system (binders) to a record
of pulled-back fundamental solutions `Y` on the fibres `C_θ` over the path `b65p_curve p θ`; and,
from such a record, the differential dictionary on the covers (holomorphic `G`-maps from `σ`,
resp. `σ̄`, to `H⁰(K_{C_θ})` correspond to the kernel vectors of the 5d r-, resp. q-systems,
through `Y⁻¹ r ds` and `Yᵀ q ds`); for a tuple in the class datum, three-dimensional kernels
near `θ = 0`; the 5d frames as bases on the covers; the frame change `c = rFrame · c_F`,
`d = qFrame · d_F` of any geometric bases, with invertible `c_F`, `d_F`, analytic for analytic
coefficient families; the numerator array `b65q_numMatrix` as the matrix of the multiplication
`μ_{C_θ}`; the left unit `A θ = K(c_F⁻¹, d_F⁻¹)` with `b65q_numMatrix = A θ · G` for the numerator
array `G` of geometric bases; and the right unit `B θ`, the inverse of the branch-point
coordinate matrix.

The named-loop supplier `b65z_schlesinger_identification` (F-2276, `963534ae` on `main`)
supplies the identification binders for its selected family given the certified root-box
hypothesis `hp`; it does not identify an arbitrary supplied `D`. Not claimed here: which of
`ρ`, `ρ̄` the deck group uses (the record carries the choice); analyticity in
`θ` of any particular geometric bases, such as the B6-3 or 6e primitive frames; the comparison
of `G` with the residue array `b66m_jet` (6e), including the constant normalization between
cover residues and the branch-point coordinates here; the codifferential (B6-6).
HC no distance; AV milestone no distance.
-/

noncomputable section
open Set Metric Matrix Filter Polynomial Manifold
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

/-- **Pulled-back fundamental solutions along the path.** Implication from an identification of
the family `D` at the G32 centre with the base Schlesinger system (the Möbius homeomorphism `e`
of the `s`-sphere onto the punctured `z`-sphere, a base point, and transport of `b65r_pullback`
conjugate by one operator `C` to the column monodromy of the cover; outputs supplied by
`b65z_schlesinger_identification` for its selected family under `hp`, here binders) to a record
`b65g_Solutions p O D`:
for small `θ`, on the fibre over `b65p_curve p θ`, an invertible solution of the system of `O` at
`θ` in the `s`-coordinate with deck law `Y(h x) = Y(x) σ(h)ᵀ`, `σ ∈ {ρ, ρ̄}`.
Source: G32 v0.16, §5.5 (The direction: "for small θ the system at θ is the ρ-local system of
the cover C_θ"), Lemma 5.6(2) (isomonodromy), proof of Lemma 5.3 (single-valuedness of `Y` on
the cover, `g*Y = Y ρ'(g)`); `b6t_monodromy` (transport of the covering over the polydisc). -/
theorem b65g_cover_solutions (p : Fin 12 → ℂ) (O : b65p_Outputs p) (g : Fin 13 → b4b_Group)
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
            (FundamentalGroup.fromPath ⟦η⟧)).val * (C⁻¹).val) :
    Nonempty (b65g_Solutions p O D) :=
  b65g_cover_solutions_aux p O g D e he x u₀ C hT

example := @b65g_cover_solutions

/-- **The dictionary on the covers.** For a record of solutions, at every small `θ` and on the
fibre `C_θ` over `b65p_curve p θ`: every kernel vector `c` of the 5d r-system gives exactly one
`G`-map from `σ` to holomorphic `1`-forms whose values agree with `Y⁻¹ r ds`
(`r = b65q_principal c`) on the regular locus, and every such `G`-map comes from exactly one kernel
vector; likewise for the q-system, `σ̄`, and `Yᵀ q ds` (`q = b65q_qVector d`).
Source: G32 v0.16, Lemma 5.3 (The dictionary) and its proof, Lemma 5.4(1); `b65q_dictionary`
(the order conditions as the image of the kernels); unitarity of the G32 matrices
(`b63l_toMatrix_mem_unitary`), which makes `Yᵀ q ds` transform by `σ̄`. -/
theorem b65g_dictionary (p : Fin 12 → ℂ) (O : b65p_Outputs p) (g : Fin 13 → b4b_Group)
    (D : b65z_SharedFamily (b65z_centre p) g) (S : b65g_Solutions p O D) :
    ∃ ε : ℝ, 0 < ε ∧ ε ≤ S.radius ∧ ∀ θ ∈ ball (0 : ℂ) ε,
      ∀ t : b6t_polydisc (b65z_centre p), t.val = b65p_curve p θ →
      (∀ c : Fin 36 → ℂ, b65q_rFamily p O.residue θ *ᵥ c = 0 →
        ∃! φ : (Fin 4 → ℂ) →ₗ[ℂ] (TangentBundle 𝓘(ℂ, ℂ) (b65z_fibre (b65z_centre p) D.C t) → ℂ), φ ∈ b65g_homG D t S.conj ∧
          b65g_rRepresents D t (b65p_moving p θ 10) (b65p_moving p θ 11) (b65p_poles p θ) (b65g_Y S θ t) (b65q_principal (b65p_poles p θ) c) φ) ∧
      (∀ φ ∈ b65g_homG D t S.conj, ∃! c : Fin 36 → ℂ, b65q_rFamily p O.residue θ *ᵥ c = 0 ∧
          b65g_rRepresents D t (b65p_moving p θ 10) (b65p_moving p θ 11) (b65p_poles p θ) (b65g_Y S θ t) (b65q_principal (b65p_poles p θ) c) φ) ∧
      (∀ d : Fin 48 → ℂ, b65q_qFamily p O.residue θ *ᵥ d = 0 →
        ∃! ψ : (Fin 4 → ℂ) →ₗ[ℂ] (TangentBundle 𝓘(ℂ, ℂ) (b65z_fibre (b65z_centre p) D.C t) → ℂ), ψ ∈ b65g_homG D t (!S.conj) ∧
          b65g_qRepresents D t (b65p_moving p θ 10) (b65p_moving p θ 11) (b65p_poles p θ) (b65g_Y S θ t) (b65q_qVector (b65p_poles p θ) p (b65q_left O.residue θ) d) ψ) ∧
      ∀ ψ ∈ b65g_homG D t (!S.conj), ∃! d : Fin 48 → ℂ, b65q_qFamily p O.residue θ *ᵥ d = 0 ∧
          b65g_qRepresents D t (b65p_moving p θ 10) (b65p_moving p θ 11) (b65p_poles p θ) (b65g_Y S θ t) (b65q_qVector (b65p_poles p θ) p (b65q_left O.residue θ) d) ψ :=
  b65g_dictionary_aux p O g D S

example := @b65g_dictionary

/-- **Full kernels.** For a tuple in the class datum, near `θ = 0` both 5d family systems have
three-dimensional kernels, so the 5d frames solve the full systems.
Source: G32 v0.16, Lemma 5.4(2) ("it has dimension 3 by Lemma 3.6") and Lemma 3.6
(`dim Hom_G(ρ, H⁰(K_C)) = 3` for every `C` in the Hurwitz space); Chevalley–Weil
(`b63d_finite_holoCW`, `g32h_holoCW_of_nielsen`); `b65q_frames_kernel`. -/
theorem b65g_full_kernels (p : Fin 12 → ℂ) (O : b65p_Outputs p) (g : Fin 13 → b4b_Group)
    (hg : g32h_Nielsen (fun i ↦ b4b_toMatrix (g i))) (D : b65z_SharedFamily (b65z_centre p) g) (S : b65g_Solutions p O D) :
    ∃ ε : ℝ, 0 < ε ∧ ε ≤ S.radius ∧ ∀ θ ∈ ball (0 : ℂ) ε,
      Module.finrank ℂ (LinearMap.ker (b65q_rFamily p O.residue θ).mulVecLin) = 3 ∧
      Module.finrank ℂ (LinearMap.ker (b65q_qFamily p O.residue θ).mulVecLin) = 3 ∧
      b65q_rFamily p O.residue θ * b65q_rFrame p O.residue θ = 0 ∧
      b65q_qFamily p O.residue θ * b65q_qFrame p O.residue θ = 0 :=
  b65g_full_kernels_aux p O g hg D S

example := @b65g_full_kernels

/-- **The geometric frames.** Near `θ = 0`, the three columns of each 5d frame correspond under the
dictionary to `G`-maps forming a basis of `Hom_G(σ, H⁰(K_{C_θ}))`, resp. `Hom_G(σ̄, H⁰(K_{C_θ}))`.
Source: G32 v0.16, Lemma 5.4(3) (the `x_f` form a basis of `ker Φ`), §5.5(6) (the bases
`r_1, r_2, r_3` and `q_1, q_2, q_3`), Lemma 5.8 (the `x_f(θ)` span the kernel). -/
theorem b65g_frames (p : Fin 12 → ℂ) (O : b65p_Outputs p) (g : Fin 13 → b4b_Group)
    (hg : g32h_Nielsen (fun i ↦ b4b_toMatrix (g i))) (D : b65z_SharedFamily (b65z_centre p) g) (S : b65g_Solutions p O D) :
    ∃ ε : ℝ, 0 < ε ∧ ε ≤ S.radius ∧ ∀ θ ∈ ball (0 : ℂ) ε,
      ∀ t : b6t_polydisc (b65z_centre p), t.val = b65p_curve p θ →
      (∃ φ : Fin 3 → (Fin 4 → ℂ) →ₗ[ℂ] (TangentBundle 𝓘(ℂ, ℂ) (b65z_fibre (b65z_centre p) D.C t) → ℂ),
        (∀ a, φ a ∈ b65g_homG D t S.conj ∧ b65g_rRepresents D t (b65p_moving p θ 10) (b65p_moving p θ 11) (b65p_poles p θ) (b65g_Y S θ t)
          (b65q_principal (b65p_poles p θ) (fun i ↦ b65q_rFrame p O.residue θ i a)) (φ a)) ∧
        LinearIndependent ℂ φ ∧ Submodule.span ℂ (Set.range φ) = b65g_homG D t S.conj) ∧
      ∃ ψ : Fin 3 → (Fin 4 → ℂ) →ₗ[ℂ] (TangentBundle 𝓘(ℂ, ℂ) (b65z_fibre (b65z_centre p) D.C t) → ℂ),
        (∀ b, ψ b ∈ b65g_homG D t (!S.conj) ∧ b65g_qRepresents D t (b65p_moving p θ 10) (b65p_moving p θ 11) (b65p_poles p θ) (b65g_Y S θ t)
          (b65q_qVector (b65p_poles p θ) p (b65q_left O.residue θ) (fun i ↦ b65q_qFrame p O.residue θ i b)) (ψ b)) ∧
        LinearIndependent ℂ ψ ∧ Submodule.span ℂ (Set.range ψ) = b65g_homG D t (!S.conj) :=
  b65g_frames_aux p O g hg D S

example := @b65g_frames

/-- **Change of frames.** Near `θ = 0`, the coefficient matrix `c` of any basis of
`Hom_G(σ, H⁰(K_{C_θ}))` (its columns represent the basis on the regular locus) is
`c = rFrame · c_F` with `c_F = c` on the free rows `b65k_rFree`, invertible; likewise
`d = qFrame · d_F`. For a family of such coefficient matrices analytic in `θ`, `c_F` and `d_F`
are analytic and invertible on the whole ball.
Source: G32 v0.16, Lemma 5.4(3), Remark (The Smith form: analytic changes of the bases);
`b65q_frame_change`; `docs/specs/NumeratorJet.md`, amendment (the direction
`c = rFrame * c_F`, `d = qFrame * d_F`). -/
theorem b65g_frame_change (p : Fin 12 → ℂ) (O : b65p_Outputs p) (g : Fin 13 → b4b_Group)
    (hg : g32h_Nielsen (fun i ↦ b4b_toMatrix (g i))) (D : b65z_SharedFamily (b65z_centre p) g) (S : b65g_Solutions p O D) :
    ∃ ε : ℝ, 0 < ε ∧ ε ≤ S.radius ∧
      (∀ θ ∈ ball (0 : ℂ) ε, ∀ t : b6t_polydisc (b65z_centre p), t.val = b65p_curve p θ →
        (∀ (β : Fin 3 → (Fin 4 → ℂ) →ₗ[ℂ] (TangentBundle 𝓘(ℂ, ℂ) (b65z_fibre (b65z_centre p) D.C t) → ℂ)) (c : Matrix (Fin 36) (Fin 3) ℂ),
          (∀ a, β a ∈ b65g_homG D t S.conj) → LinearIndependent ℂ β →
          (∀ a, b65g_rRepresents D t (b65p_moving p θ 10) (b65p_moving p θ 11) (b65p_poles p θ) (b65g_Y S θ t) (b65q_principal (b65p_poles p θ) (fun i ↦ c i a)) (β a)) →
          IsUnit (c.submatrix b65k_rFree id) ∧
            c = b65q_rFrame p O.residue θ * c.submatrix b65k_rFree id) ∧
        ∀ (β : Fin 3 → (Fin 4 → ℂ) →ₗ[ℂ] (TangentBundle 𝓘(ℂ, ℂ) (b65z_fibre (b65z_centre p) D.C t) → ℂ)) (d : Matrix (Fin 48) (Fin 3) ℂ),
          (∀ b, β b ∈ b65g_homG D t (!S.conj)) → LinearIndependent ℂ β →
          (∀ b, b65g_qRepresents D t (b65p_moving p θ 10) (b65p_moving p θ 11) (b65p_poles p θ) (b65g_Y S θ t) (b65q_qVector (b65p_poles p θ) p (b65q_left O.residue θ) (fun i ↦ d i b)) (β b)) →
          IsUnit (d.submatrix b65k_qFree id) ∧
            d = b65q_qFrame p O.residue θ * d.submatrix b65k_qFree id) ∧
      (∀ c : ℂ → Matrix (Fin 36) (Fin 3) ℂ,
        (∀ i f, AnalyticOnNhd ℂ (fun θ ↦ c θ i f) (ball 0 ε)) →
        (∀ θ ∈ ball (0 : ℂ) ε, ∀ t : b6t_polydisc (b65z_centre p), t.val = b65p_curve p θ →
          ∃ β : Fin 3 → (Fin 4 → ℂ) →ₗ[ℂ] (TangentBundle 𝓘(ℂ, ℂ) (b65z_fibre (b65z_centre p) D.C t) → ℂ), (∀ a, β a ∈ b65g_homG D t S.conj) ∧ LinearIndependent ℂ β ∧
            ∀ a, b65g_rRepresents D t (b65p_moving p θ 10) (b65p_moving p θ 11) (b65p_poles p θ) (b65g_Y S θ t) (b65q_principal (b65p_poles p θ) (fun i ↦ c θ i a)) (β a)) →
        (∀ a f, AnalyticOnNhd ℂ (fun θ ↦ (c θ).submatrix b65k_rFree id a f) (ball 0 ε)) ∧
          ∀ θ ∈ ball (0 : ℂ) ε, IsUnit ((c θ).submatrix b65k_rFree id)) ∧
      ∀ d : ℂ → Matrix (Fin 48) (Fin 3) ℂ,
        (∀ i f, AnalyticOnNhd ℂ (fun θ ↦ d θ i f) (ball 0 ε)) →
        (∀ θ ∈ ball (0 : ℂ) ε, ∀ t : b6t_polydisc (b65z_centre p), t.val = b65p_curve p θ →
          ∃ β : Fin 3 → (Fin 4 → ℂ) →ₗ[ℂ] (TangentBundle 𝓘(ℂ, ℂ) (b65z_fibre (b65z_centre p) D.C t) → ℂ), (∀ b, β b ∈ b65g_homG D t (!S.conj)) ∧ LinearIndependent ℂ β ∧
            ∀ b, b65g_qRepresents D t (b65p_moving p θ 10) (b65p_moving p θ 11) (b65p_poles p θ) (b65g_Y S θ t) (b65q_qVector (b65p_poles p θ) p (b65q_left O.residue θ) (fun i ↦ d θ i b)) (β b)) →
        (∀ b f, AnalyticOnNhd ℂ (fun θ ↦ (d θ).submatrix b65k_qFree id b f) (ball 0 ε)) ∧
          ∀ θ ∈ ball (0 : ℂ) ε, IsUnit ((d θ).submatrix b65k_qFree id) :=
  b65g_frame_change_aux p O g hg D S

example := @b65g_frame_change

/-- **The numerator matrix is the matrix of multiplication.** Near `θ = 0`, for the `G`-maps of the
5d frame columns `a` (r) and `b` (q), the contraction of the two vectors of forms is, on the
regular locus, the pullback of `N_{ab}(s) ds² / D_θ(s)`, where `N_{ab}` has the coefficients of
row `3a + b` of `b65q_numMatrix`.
Source: G32 v0.16, Lemma 5.8 ("𝐌(θ) is the matrix of `μ_{C_θ}` in the bases `(r_a)`, `(q_b)` and in
numerator coordinates"), Lemma 5.3 (`μ_C(r ⊗ q) = qᵀr ds²`), Lemma 5.5 (numerators);
`b65q_family_numerators`. -/
theorem b65g_numerator_matrix (p : Fin 12 → ℂ) (O : b65p_Outputs p) (g : Fin 13 → b4b_Group)
    (hg : g32h_Nielsen (fun i ↦ b4b_toMatrix (g i))) (D : b65z_SharedFamily (b65z_centre p) g) (S : b65g_Solutions p O D) :
    ∃ ε : ℝ, 0 < ε ∧ ε ≤ S.radius ∧ ∀ θ ∈ ball (0 : ℂ) ε,
      ∀ t : b6t_polydisc (b65z_centre p), t.val = b65p_curve p θ →
      ∀ (a b : Fin 3) (φ ψ : (Fin 4 → ℂ) →ₗ[ℂ] (TangentBundle 𝓘(ℂ, ℂ) (b65z_fibre (b65z_centre p) D.C t) → ℂ)),
        φ ∈ b65g_homG D t S.conj → ψ ∈ b65g_homG D t (!S.conj) →
        b65g_rRepresents D t (b65p_moving p θ 10) (b65p_moving p θ 11) (b65p_poles p θ) (b65g_Y S θ t)
          (b65q_principal (b65p_poles p θ) (fun i ↦ b65q_rFrame p O.residue θ i a)) φ →
        b65g_qRepresents D t (b65p_moving p θ 10) (b65p_moving p θ 11) (b65p_poles p θ) (b65g_Y S θ t)
          (b65q_qVector (b65p_poles p θ) p (b65q_left O.residue θ) (fun i ↦ b65q_qFrame p O.residue θ i b)) ψ →
        ∀ u : TangentBundle 𝓘(ℂ, ℂ) (b65z_fibre (b65z_centre p) D.C t), u.1 ∈ b65g_good D t (b65p_moving p θ 10) (b65p_moving p θ 11) (b65p_poles p θ) →
          b65g_contract φ ψ u = b65g_quadratic D t (b65p_moving p θ 10) (b65p_moving p θ 11) (b65p_poles p θ)
            (b65q_numMatrix p O.residue θ (finProdFinEquiv (a, b))) u :=
  b65g_numerator_matrix_aux p O g hg D S

example := @b65g_numerator_matrix

/-- **The left unit `A θ`.** Near `θ = 0`, for any bases `βr`, `βq` of the two `Hom_G` spaces of
`C_θ` with coefficient matrices `c`, `d`: their numerator array (the `9 × 10` matrix `G` whose row
`3a + b` gives the numerator of the contraction of `βr a` and `βq b`) exists and is unique,
`A θ = K(c_F⁻¹, d_F⁻¹)` (`b65g_A c d`) is a unit, and `b65q_numMatrix = A θ * G`.
Source: G32 v0.16, Lemma 5.8, Remark (The Smith form); bilinearity of the contraction;
`b66e_productChange`, `b66e_productChange_unit`; `docs/specs/NumeratorJet.md`, amendment
(`A θ = K(c_F⁻¹, d_F⁻¹)`). -/
theorem b65g_units (p : Fin 12 → ℂ) (O : b65p_Outputs p) (g : Fin 13 → b4b_Group)
    (hg : g32h_Nielsen (fun i ↦ b4b_toMatrix (g i))) (D : b65z_SharedFamily (b65z_centre p) g) (S : b65g_Solutions p O D) :
    ∃ ε : ℝ, 0 < ε ∧ ε ≤ S.radius ∧ ∀ θ ∈ ball (0 : ℂ) ε,
      ∀ t : b6t_polydisc (b65z_centre p), t.val = b65p_curve p θ →
      ∀ (βr βq : Fin 3 → (Fin 4 → ℂ) →ₗ[ℂ] (TangentBundle 𝓘(ℂ, ℂ) (b65z_fibre (b65z_centre p) D.C t) → ℂ)) (c : Matrix (Fin 36) (Fin 3) ℂ)
        (d : Matrix (Fin 48) (Fin 3) ℂ),
        (∀ a, βr a ∈ b65g_homG D t S.conj) → (∀ b, βq b ∈ b65g_homG D t (!S.conj)) →
        LinearIndependent ℂ βr → LinearIndependent ℂ βq →
        (∀ a, b65g_rRepresents D t (b65p_moving p θ 10) (b65p_moving p θ 11) (b65p_poles p θ) (b65g_Y S θ t) (b65q_principal (b65p_poles p θ) (fun i ↦ c i a)) (βr a)) →
        (∀ b, b65g_qRepresents D t (b65p_moving p θ 10) (b65p_moving p θ 11) (b65p_poles p θ) (b65g_Y S θ t) (b65q_qVector (b65p_poles p θ) p (b65q_left O.residue θ) (fun i ↦ d i b)) (βq b)) →
        (∃! G : Matrix (Fin 9) (Fin 10) ℂ, (fun G : Matrix (Fin 9) (Fin 10) ℂ ↦ ∀ (a b : Fin 3) (u : TangentBundle 𝓘(ℂ, ℂ) (b65z_fibre (b65z_centre p) D.C t)),
            u.1 ∈ b65g_good D t (b65p_moving p θ 10) (b65p_moving p θ 11) (b65p_poles p θ) →
            b65g_contract (βr a) (βq b) u = b65g_quadratic D t (b65p_moving p θ 10) (b65p_moving p θ 11) (b65p_poles p θ) (G (finProdFinEquiv (a, b))) u) G) ∧
        IsUnit (b65g_A c d) ∧
        ∀ G : Matrix (Fin 9) (Fin 10) ℂ, (fun G : Matrix (Fin 9) (Fin 10) ℂ ↦ ∀ (a b : Fin 3) (u : TangentBundle 𝓘(ℂ, ℂ) (b65z_fibre (b65z_centre p) D.C t)),
            u.1 ∈ b65g_good D t (b65p_moving p θ 10) (b65p_moving p θ 11) (b65p_poles p θ) →
            b65g_contract (βr a) (βq b) u = b65g_quadratic D t (b65p_moving p θ 10) (b65p_moving p θ 11) (b65p_poles p θ) (G (finProdFinEquiv (a, b))) u) G →
          b65q_numMatrix p O.residue θ = b65g_A c d * G :=
  b65g_units_aux p O g hg D S

example := @b65g_units

/-- **The right unit `B θ`.** Near `θ = 0`, the branch-point coordinate matrix is invertible, its
inverse `B θ = b65g_B p θ` is analytic, and for every numerator row `N` the branch-point coordinate
`(N ᵥ* V θ) k` is the residue at the chart branch point `s_k` of `N(s) / (D_θ(s) m_θ'(s))`, the
pairing of `N ds² / D_θ` with `∂/∂z_k` in the chart coordinate `z_k = m_θ(s_k)`.
Source: G32 v0.16, §5.1 (Serre duality of the tangent space with `H⁰(ℙ¹, K²(B_C))`), Lemma 5.5;
Vandermonde; `O.poles_injective`; `docs/specs/NumeratorJet.md`, amendment (`B θ` maps
branch-point row coordinates to monomial coordinates). -/
theorem b65g_branch_coordinates (p : Fin 12 → ℂ) (O : b65p_Outputs p) :
    ∃ ε : ℝ, 0 < ε ∧ ε ≤ O.radius ∧
      (∀ j k : Fin 10, AnalyticOnNhd ℂ (fun θ ↦ b65g_B p θ j k) (ball 0 ε)) ∧
      ∀ θ ∈ ball (0 : ℂ) ε, IsUnit (b65g_branchMatrix p θ) ∧
        ∀ (N : Fin 10 → ℂ) (k : Fin 10),
          Tendsto (fun s : ℂ ↦ (s - b65p_moving p θ (Fin.castLE (by norm_num) k)) *
              (∑ j : Fin 10, N j * s ^ j.val) /
              ((b65q_denominator (b65p_poles p θ)).eval s *
                deriv (b65s_normalize (b65p_moving p θ 10) (b65p_moving p θ 11)) s))
            (𝓝[≠] (b65p_moving p θ (Fin.castLE (by norm_num) k)))
            (𝓝 ((N ᵥ* b65g_branchMatrix p θ) k)) :=
  b65g_branch_coordinates_aux p O

example := @b65g_branch_coordinates

/-- **The contraction convention.** For invertible `Y`, the vectors `Y⁻¹ r` and `Yᵀ q` contract to
`qᵀ r`: the pointwise identity behind `μ_C(r ⊗ q) = qᵀ r ds²`. With `Y⁻¹` on both sides (or `Yᵀ`
on both) the identity fails in general. -/
example (Y : Matrix (Fin 4) (Fin 4) ℂ) (hY : IsUnit Y.det) (r q : Fin 4 → ℂ) :
    ∑ i : Fin 4, (Y⁻¹ *ᵥ r) i * (Yᵀ *ᵥ q) i = q ⬝ᵥ r := by
  have h : ∑ i : Fin 4, (Y⁻¹ *ᵥ r) i * (Yᵀ *ᵥ q) i = (Yᵀ *ᵥ q) ⬝ᵥ (Y⁻¹ *ᵥ r) := by
    simp only [dotProduct]; exact Finset.sum_congr rfl fun i _ ↦ mul_comm _ _
  rw [h, ← vecMul_transpose, transpose_transpose, ← dotProduct_mulVec, mulVec_mulVec,
    mul_nonsing_inv _ hY, one_mulVec]

/-- **The 5d frames have `A = 1`.** The free blocks of the 5d frames are the identity at every
parameter, so the left factor attached to the frames themselves is the identity (and the
units statement for these bases reduces to the numerator statement). -/
example (p : Fin 12 → ℂ) (R : ℂ → Fin 4 ⊕ Fin 12 → (Fin 4 → ℂ) →L[ℂ] (Fin 4 → ℂ)) (θ : ℂ) :
    b65g_A (b65q_rFrame p R θ) (b65q_qFrame p R θ) = 1 := by
  have hr : (b65q_rFrame p R θ).submatrix b65k_rFree id = 1 := by
    ext a f; fin_cases a <;> fin_cases f <;>
      norm_num [b65q_rFrame, b65k_rFree, b65k_rPivot, Fin.sum_univ_succ, Matrix.one_apply]
    all_goals decide
  have hq : (b65q_qFrame p R θ).submatrix b65k_qFree id = 1 := by
    ext a f; fin_cases a <;> fin_cases f <;>
      norm_num [b65q_qFrame, b65k_qFree, b65k_qPivot, Fin.sum_univ_succ, Matrix.one_apply]
    all_goals decide
  rw [b65g_A, hr, hq, inv_one]
  ext u w
  obtain ⟨⟨i, j⟩, rfl⟩ := (finProdFinEquiv : Fin 3 × Fin 3 ≃ Fin 9).surjective u
  obtain ⟨⟨a, b⟩, rfl⟩ := (finProdFinEquiv : Fin 3 × Fin 3 ≃ Fin 9).surjective w
  simp only [b66e_productChange, Matrix.one_apply, Equiv.symm_apply_apply,
    EmbeddingLike.apply_eq_iff_eq, Prod.mk.injEq]
  split_ifs <;> simp_all

/-- **Invertible free blocks give an invertible `A`** (`b66e_productChange_unit`, a statement
with a body). -/
example (c : Matrix (Fin 36) (Fin 3) ℂ) (d : Matrix (Fin 48) (Fin 3) ℂ)
    (hc : IsUnit (c.submatrix b65k_rFree id)) (hd : IsUnit (d.submatrix b65k_qFree id)) :
    IsUnit (b65g_A c d) := by
  apply b66e_productChange_unit
  · exact Matrix.isUnit_nonsing_inv_iff.mpr hc
  · exact Matrix.isUnit_nonsing_inv_iff.mpr hd

/-- **Consumer compatibility check toward 6e.** If `M = A · G` and the branch-point coordinate
matrix `V` is invertible, then with the branch-point array `C = G · V` and `B = V⁻¹`,
`M = A · C · B`: the shape `J θ = A θ * (geometric array in branch-point coordinates) * B θ`
of `docs/specs/NumeratorJet.md`. This derives neither factor. -/
example (M G : Matrix (Fin 9) (Fin 10) ℂ) (A : Matrix (Fin 9) (Fin 9) ℂ)
    (V : Matrix (Fin 10) (Fin 10) ℂ) (hV : IsUnit V) (h : M = A * G) :
    M = A * (G * V) * V⁻¹ := by
  rw [Matrix.mul_assoc A, Matrix.mul_assoc G,
    Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det V).mp hV), Matrix.mul_one, h]

/-- A twice-scaled r-frame has inverse product-change entry `1/2`, not `2`. -/
example :
    let c : Matrix (Fin 36) (Fin 3) ℂ := fun i j ↦ if i = b65k_rFree j then 2 else 0
    let d : Matrix (Fin 48) (Fin 3) ℂ := fun i j ↦ if i = b65k_qFree j then 1 else 0
    b65g_A c d 0 0 = (1 / 2 : ℂ) ∧
      b66e_productChange (c.submatrix b65k_rFree id) (d.submatrix b65k_qFree id) 0 0 = 2 := by
  dsimp only
  have hr : Matrix.submatrix (fun i j ↦ if i = b65k_rFree j then (2 : ℂ) else 0)
      b65k_rFree id = Matrix.diagonal (fun _ : Fin 3 ↦ (2 : ℂ)) := by
    ext i j; fin_cases i <;> fin_cases j <;> norm_num [b65k_rFree, Matrix.submatrix, Matrix.diagonal]
  have hq : Matrix.submatrix (fun i j ↦ if i = b65k_qFree j then (1 : ℂ) else 0)
      b65k_qFree id = Matrix.diagonal (fun _ : Fin 3 ↦ (1 : ℂ)) := by
    ext i j; fin_cases i <;> fin_cases j <;> norm_num [b65k_qFree, Matrix.submatrix, Matrix.diagonal]
  have hi : (Matrix.diagonal (fun _ : Fin 3 ↦ (2 : ℂ)))⁻¹ =
      Matrix.diagonal (fun _ : Fin 3 ↦ (1 / 2 : ℂ)) := by
    apply Matrix.inv_eq_left_inv
    rw [Matrix.diagonal_mul_diagonal]
    ext i j
    by_cases h : i = j <;> simp [Matrix.one_apply, h]
  have hiq : (Matrix.diagonal (fun _ : Fin 3 ↦ (1 : ℂ)))⁻¹ = 1 := by simp
  simp only [b65g_A, hr, hq, hi, hiq]
  norm_num [hr, hq, b66e_productChange,
    finProdFinEquiv, Fin.divNat, Fin.modNat, Matrix.diagonal]

/-- Normalization and row permutation change the left factor. -/
example (J G C : Matrix (Fin 9) (Fin 10) ℂ) (A P : Matrix (Fin 9) (Fin 9) ℂ)
    (V : Matrix (Fin 10) (Fin 10) ℂ) (l : ℂ) (hl : l ≠ 0)
    (hP : IsUnit P) (hV : IsUnit V) (hJ : J = A * G)
    (hC : C = l • (P * G * V)) :
    J = (l⁻¹ • (A * P⁻¹)) * C * V⁻¹ := by
  rw [hC, Matrix.smul_mul, Matrix.mul_smul, smul_smul, inv_mul_cancel₀ hl, one_smul]
  simp only [Matrix.mul_assoc]
  rw [Matrix.mul_nonsing_inv V
    ((Matrix.isUnit_iff_isUnit_det V).mp hV), Matrix.mul_one,
    ← Matrix.mul_assoc P⁻¹ P, Matrix.nonsing_inv_mul P
    ((Matrix.isUnit_iff_isUnit_det P).mp hP), Matrix.one_mul, hJ]

end HodgeLean.Foundations.Program
