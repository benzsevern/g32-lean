import HodgeLean.Foundations.Program.G32ContractionSupplierProofs

/-! # The restored supplier character of the G32 contraction (FROZEN SPEC)

`g32c_supplier_character`, set aside from `G32Contraction.lean` on 2026-11-05 and restored with
its former signature (`docs/specs/G32Contraction.md`, sections "Set aside (2026-11-05)" and
"Restored (2026-11-05): `g32c_supplier_character`"). It is an implication from the fields of
`g32p_Cover` and `g32p_Part` and from an enumeration satisfying `g32c_Enumeration`, through stages
A–G of `G32RepStages.lean` and `G32RepTransport.lean`.

Not claimed: the existence of a realization `g32p_Cover` or of a concrete enumeration, the Weil
character `g32c_weil_character`, or the `U`-invariance `g32c_gamma_invariant` (both wait for
stage H). HC no distance; AV milestone no distance.
-/

noncomputable section
set_option maxHeartbeats 400000

open scoped TensorProduct CategoryTheory.MonObj
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open HodgeLean.RealDefs HodgeLean.Adapters HodgeLean.Papers HodgeLean.Foundations

namespace HodgeLean.Foundations.Program

variable {A : g32t_Sixfold}

/-- **The `U`-characters of a supplier part.** For `u ∈ U`, the induced map on `H¹(P_χ; ℂ)` has
determinant one, so `U` acts trivially on the top cohomology of `P_χ`; and on the determinant
line `det V_t` of the embedding `t` with `t(ζ_m) = exp(2πi/m)^k` it acts by the character of `T`
with coordinates `a(χ^k)`, the vector of `papersA` for the complex character `χ^k`, in the
enumeration `τ, τ̄, θ`.
Source: G32 v0.16, Subsection 4.2 (`U(ℂ) = ∏ GL(M_τ) × ∏ O(M_τ) × ∏ Sp(M_τ)`, `X*(T)`, and
`V_χ = ⊕_τ Hom_{H′}(χ, τ|_{H′}) ⊗ M_τ`), and proof of Proposition 4.6, paragraph "The
correspondence" ("`∏_t z_{i,t}` spans the top cohomology of `P_i`, on which `U` acts
trivially"); Serre, *Linear representations of finite groups*, §2.6. -/
theorem g32c_supplier_character (X : g32p_Cover A) (S : g32p_Supplier)
    (hS : g32p_Admissible X.aut S) (χc : S.H →* ℂˣ)
    (hχc : ∀ h, ((χc h : ℂˣ) : ℂ) = g32p_root S.m ^ (Multiplicative.toAdd (S.χ h)).val)
    {I K : Type*} [Fintype I] [Fintype K] (τ τbar : I → FDRep ℂ g32p_G)
    (θ : K → FDRep ℂ g32p_G) (hE : g32c_Enumeration τ τbar θ)
    (u : Module.End ℂ (ℂ ⊗[ℚ] HQ X.J 1)) (hu : u ∈ g32c_U X)
    (k : ℤ) (t : cyc_Field S.m →ₐ[ℚ] ℂ) (ht : t (g32p_zeta S) = g32p_root S.m ^ k) :
    LinearMap.det (g32c_restrict (X.part S hS).incl (X.part S hS).proj (X.part S hS).N u) = 1 ∧
    ∀ z ∈ cyc_line (X.part S hS).act.cyc_coordinates t,
      exteriorPower.map (2 * (X.part S hS).k)
          (g32c_restrict (X.part S hS).incl (X.part S hS).proj (X.part S hS).N u) z =
        g32c_charOf X τ θ u hu (papersA τ τbar θ S.H (χc ^ k)) • z :=
  g32c_supplier_character_aux X S hS χc hχc τ τbar θ hE u hu k t ht

/-- Two elements of `U`, applied one after the other on the line `cyc_line e t`, act by the
product of their characters. -/
example (X : g32p_Cover A) (S : g32p_Supplier)
    (hS : g32p_Admissible X.aut S) (χc : S.H →* ℂˣ)
    (hχc : ∀ h, ((χc h : ℂˣ) : ℂ) = g32p_root S.m ^ (Multiplicative.toAdd (S.χ h)).val)
    {I K : Type*} [Fintype I] [Fintype K] (τ τbar : I → FDRep ℂ g32p_G)
    (θ : K → FDRep ℂ g32p_G) (hE : g32c_Enumeration τ τbar θ)
    (u v : Module.End ℂ (ℂ ⊗[ℚ] HQ X.J 1)) (hu : u ∈ g32c_U X) (hv : v ∈ g32c_U X)
    (k : ℤ) (t : cyc_Field S.m →ₐ[ℚ] ℂ) (ht : t (g32p_zeta S) = g32p_root S.m ^ k)
    (z : ⋀[ℂ]^(2 * (X.part S hS).k) (ℂ ⊗[ℚ] HQ (X.part S hS).P 1))
    (hz : z ∈ cyc_line (X.part S hS).act.cyc_coordinates t) :
    exteriorPower.map (2 * (X.part S hS).k)
        (g32c_restrict (X.part S hS).incl (X.part S hS).proj (X.part S hS).N v)
        (exteriorPower.map (2 * (X.part S hS).k)
          (g32c_restrict (X.part S hS).incl (X.part S hS).proj (X.part S hS).N u) z) =
      (g32c_charOf X τ θ v hv (papersA τ τbar θ S.H (χc ^ k)) *
        g32c_charOf X τ θ u hu (papersA τ τbar θ S.H (χc ^ k))) • z := by
  rw [(g32c_supplier_character X S hS χc hχc τ τbar θ hE u hu k t ht).2 z hz, map_smul,
    (g32c_supplier_character X S hS χc hχc τ τbar θ hE v hv k t ht).2 z hz, smul_smul,
    mul_comm (g32c_charOf X τ θ u hu _)]

end HodgeLean.Foundations.Program
