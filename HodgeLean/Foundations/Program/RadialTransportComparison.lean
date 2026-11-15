import HodgeLean.Foundations.Program.RadialTransportComparisonProofs

/-! # Radial and ambient configuration transport
Implication from explicit arc control and ambient motion to endpoint comparison.
Based-loop conclusions use restrictions of the comparison maps.
Ambient class selection and quantitative reparametrization remain planned in
`docs/specs/spec-rtc.md`; this module freezes the first transport stage.
HC no distance; AV milestone no distance.
-/
noncomputable section
namespace HodgeLean.Foundations.Program

/-- Radial and ambient endpoints are joined through maps preserving the endpoint labels.
Source: Birman, Braids, Links, and Mapping Class Groups (1974), Chapter 1, §1.4;
Hatcher, Algebraic Topology (2002), §1.1; `docs/notes/chs-1.md`, items 1–4. -/
theorem rtc_segment_comparison (γ : C(unitInterval, Fin 10 → ℂ))
    (hγ : ∀ t, γ t ∈ b6_chart)
    (H : C(unitInterval × OnePoint ℂ, OnePoint ℂ))
    (hH : ∀ t, Function.Bijective (fun z ↦ H (t, z)))
    (h0 : ∀ z, H (0, z) = z)
    (hmarks : ∀ t j, H (t, b6_branch (γ 0) j) = b6_branch (γ t) j)
    (V : Set (Fin 10 → ℂ)) (hV : Convex ℝ V)
    (hsub : V ⊆ b6t_polydisc (γ 0)) (harc : ∀ t, γ t ∈ V)
    (R A : b6t_punctured (γ 0) ≃ₜ b6t_punctured (γ 1))
    (hR : ∀ z, (R z : OnePoint ℂ) = b6t_sphere (γ 0) (γ 1) z)
    (hA : ∀ z, (A z : OnePoint ℂ) = H (1, z))
    (x : b6t_punctured (γ 0)) :
    (∃ K : C(unitInterval × OnePoint ℂ, OnePoint ℂ),
      (∀ t, Function.Bijective (fun z ↦ K (t, z))) ∧
      (∀ z, K (0, z) = b6t_sphere (γ 0) (γ 1) z) ∧
      (∀ z, K (1, z) = H (1, z)) ∧
      (∀ t j, K (t, b6_branch (γ 0) j) = b6_branch (γ 1) j)) ∧
    ∃ β : Path (R x) (A x), ∀ η : FundamentalGroup (b6t_punctured (γ 0)) x,
      FundamentalGroup.fundamentalGroupMulEquivOfPath β
        (FundamentalGroup.map ⟨R, R.continuous⟩ x η) =
        FundamentalGroup.map ⟨A, A.continuous⟩ x η :=
  rtc_segment_comparison_aux γ hγ H hH h0 hmarks V hV hsub harc R A hR hA x

example := @rtc_segment_comparison

/-- An arc in a convex chart region has its chord in the same relative path class.
Source: Birman, Braids, Links, and Mapping Class Groups (1974), Chapter 1, §1.4;
Hatcher, Algebraic Topology (2002), §1.1; `docs/notes/chs-1.md`, items 1–4. -/
theorem rtc_arc_to_chord {a b : b6_chart} (α : Path a b)
    (V : Set (Fin 10 → ℂ)) (hV : Convex ℝ V) (hsub : V ⊆ b6_chart)
    (harc : ∀ t, (α t).val ∈ V) :
    ∃ χ : Path a b, (∀ t, (χ t).val =
      (1 - (t : ℝ)) • a.val + (t : ℝ) • b.val) ∧ α.Homotopic χ :=
  rtc_arc_to_chord_aux α V hV hsub harc

example := @rtc_arc_to_chord

/-- Arcwise control compares the radial composite with the ambient endpoint.
Source: Birman, Braids, Links, and Mapping Class Groups (1974), Chapter 1, §1.4;
Hatcher, Algebraic Topology (2002), §1.1; `docs/notes/chs-1.md`, items 1–4. -/
theorem rtc_composition (γ : C(unitInterval, Fin 10 → ℂ))
    (hγ : ∀ t, γ t ∈ b6_chart)
    (H : C(unitInterval × OnePoint ℂ, OnePoint ℂ))
    (hH : ∀ t, Function.Bijective (fun z ↦ H (t, z)))
    (h0 : ∀ z, H (0, z) = z)
    (hmarks : ∀ t j, H (t, b6_branch (γ 0) j) = b6_branch (γ t) j)
    (N : ℕ) (hN : 0 < N)
    (hsteps : ∀ k < N, b65y_sample γ N (k + 1) ∈
      b6t_polydisc (b65y_sample γ N k))
    (harcs : ∀ k < N, ∃ V : Set (Fin 10 → ℂ), Convex ℝ V ∧ V ⊆ b6_chart ∧
      ∀ t : unitInterval, (k : ℝ) / N ≤ (t : ℝ) →
        (t : ℝ) ≤ ((k : ℝ) + 1) / N → γ t ∈ V)
    (R A : b6t_punctured (γ 0) ≃ₜ b6t_punctured (γ 1))
    (hR : ∀ z, (R z : OnePoint ℂ) = b65y_radial (b65y_sample γ N) N z)
    (hA : ∀ z, (A z : OnePoint ℂ) = H (1, z))
    (x : b6t_punctured (γ 0)) :
    (∃ K : C(unitInterval × OnePoint ℂ, OnePoint ℂ),
      (∀ t, Function.Bijective (fun z ↦ K (t, z))) ∧
      (∀ z, K (0, z) = b65y_radial (b65y_sample γ N) N z) ∧
      (∀ z, K (1, z) = H (1, z)) ∧
      (∀ t j, K (t, b6_branch (γ 0) j) = b6_branch (γ 1) j)) ∧
    ∃ β : Path (R x) (A x), ∀ η : FundamentalGroup (b6t_punctured (γ 0)) x,
      FundamentalGroup.fundamentalGroupMulEquivOfPath β
        (FundamentalGroup.map ⟨R, R.continuous⟩ x η) =
        FundamentalGroup.map ⟨A, A.continuous⟩ x η :=
  rtc_composition_aux γ hγ H hH h0 hmarks N hN hsteps harcs R A hR hA x

example := @rtc_composition

/-- Avoid a product of discs inside a larger convex chart region while retaining the path class.
Source: Hatcher, Algebraic Topology (2002), §1.2, van Kampen;
`docs/notes/chs-1.md`, item 2 (the real twenty-dimensional detour). -/
theorem rtc_avoidance (c : Fin 10 → ℂ) (r : ℝ) (hr : 0 < r)
    (V : Set (Fin 10 → ℂ)) (hV : IsOpen V) (hconv : Convex ℝ V)
    (hchart : V ⊆ b6_chart)
    (hK : {z | ∀ i, dist (z i) (c i) ≤ r} ⊆ V)
    {a b : b6_chart} (α : Path a b)
    (ha : ¬ ∀ i, dist (a.val i) (c i) ≤ r)
    (hb : ¬ ∀ i, dist (b.val i) (c i) ≤ r) :
    ∃ α' : Path a b, α.Homotopic α' ∧
      ∀ t, ¬ ∀ i, dist ((α' t).val i) (c i) ≤ r :=
  rtc_avoidance_aux c r hr V hV hconv hchart hK α ha hb

example := @rtc_avoidance

/-- Moving affine normalization gives a continuous collision-free chart track and its endpoint.
Source: Forster, Lectures on Riemann Surfaces (1981), §1, affine coordinates;
`b6_chart_coordinates`; `docs/notes/chs-1.md`, item 1. -/
theorem rtc_normalized_tracks (P : C(unitInterval, Fin 12 → ℂ))
    (hinj : ∀ t, Function.Injective (P t))
    (c : Fin 10 → ℂ)
    (hend : ∀ k : Fin 10,
      (P 1 (k.castAdd 2) - P 1 10) / (P 1 11 - P 1 10) = c k) :
    ∃ γ : C(unitInterval, Fin 10 → ℂ),
      (∀ t k, γ t k = (P t (k.castAdd 2) - P t 10) / (P t 11 - P t 10)) ∧
      (∀ t, γ t ∈ b6_chart) ∧ γ 1 = c :=
  rtc_normalized_tracks_aux P hinj c hend

example := @rtc_normalized_tracks

/-- Homotopic ordered configuration paths give the same based-loop action along the base-point track.
Source: Birman, Braids, Links, and Mapping Class Groups (1974), Chapter 1, §1.4;
Hatcher, Algebraic Topology (2002), §1.1; `docs/notes/chs-1.md`, items 1–4. -/
theorem rtc_homotopic_transport {a b : b6_chart} (α α' : Path a b) (hα : α.Homotopic α')
    (H G : C(unitInterval × OnePoint ℂ, OnePoint ℂ))
    (hH : ∀ t, Function.Bijective (fun z ↦ H (t, z)))
    (hG : ∀ t, Function.Bijective (fun z ↦ G (t, z)))
    (hH0 : ∀ z, H (0, z) = z) (hG0 : ∀ z, G (0, z) = z)
    (hHm : ∀ t j, H (t, b6_branch a.val j) = b6_branch (α t).val j)
    (hGm : ∀ t j, G (t, b6_branch a.val j) = b6_branch (α' t).val j)
    (A B : b6t_punctured a.val ≃ₜ b6t_punctured b.val)
    (hA : ∀ z, (A z : OnePoint ℂ) = H (1, z))
    (hB : ∀ z, (B z : OnePoint ℂ) = G (1, z))
    (x : b6t_punctured a.val) :
    ∃ β : Path (A x) (B x), ∀ η : FundamentalGroup (b6t_punctured a.val) x,
      FundamentalGroup.fundamentalGroupMulEquivOfPath β
        (FundamentalGroup.map ⟨A, A.continuous⟩ x η) =
        FundamentalGroup.map ⟨B, B.continuous⟩ x η :=
  rtc_homotopic_transport_aux α α' hα H G hH hG hH0 hG0 hHm hGm A B hA hB x

example := @rtc_homotopic_transport

end HodgeLean.Foundations.Program
