import HodgeLean.Foundations.Program.GaussManinToriLattice
import HodgeLean.Foundations.Program.GaussManinToriProofs

/-!
# The weight-one VHS associated to a marked period presentation (FROZEN SPEC)

Track D2. This module freezes statements about the weight-one polarized variation of Hodge
structure associated to marked holomorphic period data (`d2_MarkedPeriodFamily`, a holomorphic
map to period matrices), its period map, and the differential of the period map. The data
presents a torus `ℂ^g / Λ_b` at each point; no total space and no family of complex manifolds is
constructed here (that is Track B2's `b2_totalSpace`; the adapter is the next stage, D2b).

Claimed:
* a Riemann form is the imaginary part of a positive definite `HermitianForm` in the
  repository's convention; the statements on a single period matrix that need only Mathlib
  (the lattice is discrete and full, the marking is injective, a Riemann form forces a period
  matrix, `dim F¹ = g`, the elliptic witnesses) are frozen in `GaussManinToriLattice.lean`;
* `F¹ = H^{1,0}` gives a Hodge filtration of weight one, polarized by the form dual to a Riemann
  form (the Riemann bilinear relations);
* `F¹` is a holomorphic subbundle and transversality holds, so the period data carries the
  polarized variation `d2_toriVHS`; its D1 period map, chart domain and chart period are the ones
  of the period data (`d2_chartPeriod`), as the implication from the D1 definitions;
* the kernel of the differential of the chart period map is the kernel of the Kodaira--Spencer
  map `T_b B → Hom(H^{1,0}, H¹/F¹)`, so the two ranks agree; rank equal to `dim B` makes the
  differential injective and `b ↦ F¹_b` injective near `b`;
* witnesses: the elliptic period data `τ ↦ (1, τ)` over the upper half plane, with the standard
  Riemann form exactly when `Im τ > 0`, an injective Kodaira--Spencer map, and agreement with
  `d1_constVHS` at `τ = i`; constant period data has Kodaira--Spencer map `0`;
* G32: for period data over an open set of `ℂ¹⁰` and a coordinate change `κ` to `ℂ⁹`, the period
  map `κ ∘ d2_chartPeriod` is analytic on an open chart, and its derivative has the rank of the
  Kodaira--Spencer map when `dκ` is injective on the image of the differential; in particular
  rank nine, the form of `g32r_period_rank_nine`. The adapter `d2_g32PeriodMap` supplies the
  fields `V`, `isOpen_V`, `period`, `analytic` of `g32r_PeriodMap`.

Not claimed: a total space or a family of complex manifolds carrying the tori; families with
monodromy (the local system here is trivialized by the marking); algebraicity of the tori; the
identification of the coordinate change `κ` with the bounded realization of `𝓗₃` for a Prym
family of Weil type; the fields `mapsTo`, `isog`, `curve`, `jet`,
`jet_certified`, `codiff` of `g32r_PeriodMap`, which stay inputs of the adapter; any rank
computation for geometric period data; nilpotent orbits and limit mixed Hodge structures.
HC no distance; AV milestone no distance.
-/

noncomputable section

open CategoryTheory Manifold
open scoped TensorProduct ContDiff Matrix Topology

namespace HodgeLean.Foundations.Program

open HodgeBlocks HodgeLean.Foundations.AppellHumbert HodgeLean.Papers

section EllipticWitnesses

/-- The polarization dual to the standard Riemann form is D1's symplectic form.
Source: Birkenhake--Lange, *Complex Abelian Varieties*, 2nd ed., §3.1; `d1_sympForm`. -/
theorem d2_dualForm_stdRiemann : d2_dualForm d2_stdRiemann = d1_sympForm :=
  d2_dualForm_stdRiemann_aux

example : d2_dualForm d2_stdRiemann (Pi.single 0 1) (Pi.single 1 1) = 1 := by
  rw [d2_dualForm_stdRiemann]; simp

/-- At `τ = i`, `H^{1,0}` is D1's line `ℂ · (e₀ + i e₁)`: the constant variation `d1_constVHS`
is the variation of the constant period data of the Gaussian elliptic curve.
Source: Birkenhake--Lange, *Complex Abelian Varieties*, 2nd ed., §1.4; `d1_weightOneFiltration`. -/
theorem d2_hodgeOne_gauss : d2_hodgeOne (d2_ellipticPeriod Complex.I) = ℂ ∙ d1_hodgeVector :=
  d2_hodgeOne_gauss_aux

example : d2_filtration (d2_ellipticPeriod Complex.I) 1 = d1_weightOneFiltration 1 := by
  simp [d2_filtration, d1_weightOneFiltration, d2_hodgeOne_gauss]

/-- `τ ↦ (1, τ)` is holomorphic on the upper half plane.
Source: Birkenhake--Lange, *Complex Abelian Varieties*, 2nd ed., §8.1. -/
theorem d2_ellipticPeriod_holomorphic :
    ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, Fin 1 → Fin (2 * 1) → ℂ) ω
      (fun τ : d2_upperHalf ↦ d2_ellipticPeriod τ) :=
  d2_ellipticPeriod_holomorphic_aux

end EllipticWitnesses

section Lattice

variable {g : ℕ} {P : Fin g → Fin (2 * g) → ℂ}

/-- For a period matrix, a Riemann form is exactly the imaginary part, on `ℝ^{2g} ≅ ℂ^g`, of a
positive definite Hermitian form in the repository's convention (`HermitianForm`).
Source: Birkenhake--Lange, *Complex Abelian Varieties*, 2nd ed., Lemma 1.3.1 and §4.1;
`spec_exists_hermitian_iff_riemann`. -/
theorem d2_isRiemannForm_iff_hermitian (hP : d2_IsPeriodMatrix P)
    (A : Matrix (Fin (2 * g)) (Fin (2 * g)) ℤ) :
    d2_IsRiemannForm P A ↔ ∃ H : HermitianForm (V := Fin g → ℂ), H.IsPositiveDefinite ∧
      ∀ s t, H.imaginary (d2_realMap P s) (d2_realMap P t) = d2_riemannReal A s t :=
  d2_isRiemannForm_iff_hermitian_aux hP A

example {τ : ℂ} (hτ : 0 < τ.im) : ∃ H : HermitianForm (V := Fin 1 → ℂ), H.IsPositiveDefinite ∧
    ∀ s t, H.imaginary (d2_realMap (d2_ellipticPeriod τ) s) (d2_realMap (d2_ellipticPeriod τ) t) =
      d2_riemannReal d2_stdRiemann s t :=
  (d2_isRiemannForm_iff_hermitian (d2_ellipticPeriod_isPeriodMatrix hτ.ne')
    d2_stdRiemann).1 (d2_ellipticPeriod_isRiemannForm hτ)

end Lattice

section Hodge

variable {g : ℕ} {P : Fin g → Fin (2 * g) → ℂ}

/-- `H¹ = H^{1,0} ⊕ \bar H^{1,0}` for a complex torus: the filtration is a Hodge filtration of
weight one.
Source: Birkenhake--Lange, *Complex Abelian Varieties*, 2nd ed., §1.4; Griffiths--Harris,
*Principles of Algebraic Geometry*, ch. 2, §6. -/
theorem d2_filtration_isHodge (hP : d2_IsPeriodMatrix P) :
    d1_IsHodgeFiltration 1 (d2_filtration P) :=
  d2_filtration_isHodge_aux hP

example {τ : ℂ} (hτ : τ.im ≠ 0) : d1_IsHodgeFiltration 1 (d2_filtration (d2_ellipticPeriod τ)) :=
  d2_filtration_isHodge (d2_ellipticPeriod_isPeriodMatrix hτ)

/-- The Riemann bilinear relations: the form dual to a Riemann form polarizes the weight-one
Hodge structure of the torus.
Source: Birkenhake--Lange, *Complex Abelian Varieties*, 2nd ed., §4.2 (Riemann relations);
Griffiths--Harris, *Principles of Algebraic Geometry*, ch. 2, §6; Deligne, *Théorie de Hodge
II*, §4.4. -/
theorem d2_filtration_isPolarized {A : Matrix (Fin (2 * g)) (Fin (2 * g)) ℤ}
    (hA : d2_IsRiemannForm P A) :
    d1_IsPolarizedFiltration 1 (d2_dualForm A) (d2_filtration P) :=
  d2_filtration_isPolarized_aux hA

example {τ : ℂ} (hτ : 0 < τ.im) :
    d1_IsPolarizedFiltration 1 (d2_dualForm d2_stdRiemann) (d2_filtration (d2_ellipticPeriod τ)) :=
  d2_filtration_isPolarized (d2_ellipticPeriod_isRiemannForm hτ)

end Hodge

section Family

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
variable {B : Type*} [TopologicalSpace B] [ChartedSpace E B]
variable {g : ℕ}

/-- Every step of the filtration of marked holomorphic period data is a holomorphic subbundle of
`H¹ ⊗ 𝒪_B`; `F¹` has the holomorphic frame `b ↦ (dz_i(P_b e_k))_k`.
Source: Griffiths, Publ. Math. IHES 38 (1970), §1; Birkenhake--Lange, §1.4 and §8.1. -/
theorem d2_filtration_holomorphic [IsManifold 𝓘(ℂ, E) ω B] (X : d2_MarkedPeriodFamily E B g)
    (p : ℤ) :
    (d2_localSystem B g).IsHolomorphicSubbundle E (fun b ↦ d2_filtration (X.period b) p) :=
  d2_filtration_holomorphic_aux X p

example (P : Fin g → Fin (2 * g) → ℂ) (hP : d2_IsPeriodMatrix P) :
    (d2_localSystem E g).IsHolomorphicSubbundle E (fun _ ↦ d2_filtration P 1) :=
  d2_filtration_holomorphic (d2_constFamily E E P hP) 1

/-- Griffiths transversality holds for marked period data; in weight one it is automatic, since
`F⁰` is everything and `F²` is zero.
Source: Griffiths, *Periods of integrals on algebraic manifolds II*, Amer. J. Math. 90 (1968),
§1; Voisin, *Hodge Theory I*, ch. 10. -/
theorem d2_filtration_transversal [IsManifold 𝓘(ℂ, E) ω B] (X : d2_MarkedPeriodFamily E B g) :
    (d2_localSystem B g).IsTransversal E (fun p b ↦ d2_filtration (X.period b) p) :=
  d2_filtration_transversal_aux X

example (P : Fin g → Fin (2 * g) → ℂ) (hP : d2_IsPeriodMatrix P) :
    (d2_localSystem E g).IsTransversal E (fun p _ ↦ d2_filtration P p) :=
  d2_filtration_transversal (d2_constFamily E E P hP)

/-- **The weight-one VHS associated to a marked period presentation**: the polarized variation
of weight one with local system `H¹ = Hom(Λ_b, ℚ)` in marked coordinates, `F¹ = H^{1,0}`, and
the polarization dual to a Riemann form which is constant along the base.
Source: Griffiths, Publ. Math. IHES 38 (1970), §§1--3; Birkenhake--Lange, *Complex Abelian
Varieties*, 2nd ed., §§4.2 and 8.1. -/
def d2_toriVHS [IsManifold 𝓘(ℂ, E) ω B] (X : d2_MarkedPeriodFamily E B g)
    (A : Matrix (Fin (2 * g)) (Fin (2 * g)) ℤ) (hA : ∀ b, d2_IsRiemannForm (X.period b) A) :
    d1_PolarizedVHS E B :=
  d2_mkVHS X A (d2_filtration_holomorphic X) (d2_filtration_transversal X)
    (fun b ↦ d2_filtration_isPolarized (hA b))

example [IsManifold 𝓘(ℂ, E) ω B] (X : d2_MarkedPeriodFamily E B g)
    (A : Matrix (Fin (2 * g)) (Fin (2 * g)) ℤ) (hA : ∀ b, d2_IsRiemannForm (X.period b) A) :
    (d2_toriVHS X A hA).weight = 1 := rfl

/-- On a simply connected set, the D1 period map of the variation is the filtration of the data:
transport is the identity in marked coordinates.
Source: Griffiths, Publ. Math. IHES 38 (1970), §1; Carlson--Müller-Stach--Peters, ch. 4. -/
theorem d2_toriVHS_periodMap [IsManifold 𝓘(ℂ, E) ω B] (X : d2_MarkedPeriodFamily E B g)
    (A : Matrix (Fin (2 * g)) (Fin (2 * g)) ℤ) (hA : ∀ b, d2_IsRiemannForm (X.period b) A)
    (U : Set B) (hU : IsSimplyConnected U) (b₀ : U) (b : B) (hb : b ∈ U) (p : ℤ) :
    d1_periodMap (d2_toriVHS X A hA) U hU b₀ b p = d2_filtration (X.period b) p :=
  d2_mkVHS_periodMap_aux X A _ _ _ U hU b₀ b hb p

example [IsManifold 𝓘(ℂ, E) ω B] (X : d2_MarkedPeriodFamily E B g)
    (A : Matrix (Fin (2 * g)) (Fin (2 * g)) ℤ) (hA : ∀ b, d2_IsRiemannForm (X.period b) A)
    (U : Set B) (hU : IsSimplyConnected U) (b₀ : U) :
    d1_periodMap (d2_toriVHS X A hA) U hU b₀ b₀ 1 = d2_hodgeOne (X.period b₀) := by
  rw [d2_toriVHS_periodMap X A hA U hU b₀ b₀ b₀.2 1]
  simp [d2_filtration]
  rfl

/-- On a simply connected open set, the D1 chart domain at the step `F¹` is the chart domain of
the period data, cut down to the set.
Source: Griffiths, Publ. Math. IHES 38 (1970), §1; Carlson--Müller-Stach--Peters, ch. 4. -/
theorem d2_toriVHS_chartDomain [IsManifold 𝓘(ℂ, E) ω B] (X : d2_MarkedPeriodFamily E B g)
    (A : Matrix (Fin (2 * g)) (Fin (2 * g)) ℤ) (hA : ∀ b, d2_IsRiemannForm (X.period b) A)
    (U : Set B) (hU : IsSimplyConnected U) (hUo : IsOpen U) (b₀ : U) :
    d1_chartDomain (d2_toriVHS X A hA) U hU b₀ 1 1 = U ∩ d2_chartDomain X b₀ :=
  d2_mkVHS_chartDomain_aux X A _ _ _ U hU hUo b₀

example [IsManifold 𝓘(ℂ, E) ω B] (X : d2_MarkedPeriodFamily E B g)
    (A : Matrix (Fin (2 * g)) (Fin (2 * g)) ℤ) (hA : ∀ b, d2_IsRiemannForm (X.period b) A)
    (U : Set B) (hU : IsSimplyConnected U) (hUo : IsOpen U) (b₀ : U) :
    d1_chartDomain (d2_toriVHS X A hA) U hU b₀ 1 1 ⊆ d2_chartDomain X b₀ := by
  rw [d2_toriVHS_chartDomain X A hA U hU hUo b₀]
  exact Set.inter_subset_right

/-- On a simply connected set, the D1 chart period map at the step `F¹` is the period data's
`d2_chartPeriod`.
Source: Griffiths, Publ. Math. IHES 38 (1970), §1; Carlson--Müller-Stach--Peters, ch. 4. -/
theorem d2_toriVHS_chartPeriod [IsManifold 𝓘(ℂ, E) ω B] (X : d2_MarkedPeriodFamily E B g)
    (A : Matrix (Fin (2 * g)) (Fin (2 * g)) ℤ) (hA : ∀ b, d2_IsRiemannForm (X.period b) A)
    (U : Set B) (hU : IsSimplyConnected U) (b₀ : U) (b : B) (hb : b ∈ U) :
    d1_chartPeriod (d2_toriVHS X A hA) U hU b₀ 1 1 b = d2_chartPeriod X b₀ b :=
  d2_mkVHS_chartPeriod_aux X A _ _ _ U hU b₀ b hb

example [IsManifold 𝓘(ℂ, E) ω B] (X : d2_MarkedPeriodFamily E B g)
    (A : Matrix (Fin (2 * g)) (Fin (2 * g)) ℤ) (hA : ∀ b, d2_IsRiemannForm (X.period b) A)
    (U : Set B) (hU : IsSimplyConnected U) (b₀ : U) :
    d1_chartPeriod (d2_toriVHS X A hA) U hU b₀ 1 1 b₀ = d2_chartPeriod X b₀ b₀ :=
  d2_toriVHS_chartPeriod X A hA U hU b₀ b₀ b₀.2

end Family

section Differential

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
variable {B : Type*} [TopologicalSpace B] [ChartedSpace E B]
variable {g : ℕ}

/-- The reference point lies in the chart domain: `F¹_{b₀}` is a complement of `\bar F¹_{b₀}`,
an open condition.
Source: Griffiths, Publ. Math. IHES 38 (1970), §1; Carlson--Müller-Stach--Peters, ch. 4. -/
theorem d2_mem_chartDomain [IsManifold 𝓘(ℂ, E) ω B] (X : d2_MarkedPeriodFamily E B g) (b₀ : B) :
    b₀ ∈ d2_chartDomain X b₀ :=
  d2_mem_chartDomain_aux X b₀

example [IsManifold 𝓘(ℂ, E) ω B] (X : d2_MarkedPeriodFamily E B g) (b₀ : B) :
    d2_chartDomain X b₀ ∈ 𝓝 b₀ :=
  isOpen_interior.mem_nhds (d2_mem_chartDomain X b₀)

/-- The chart period map of marked period data is holomorphic on the chart domain.
Source: Griffiths, Publ. Math. IHES 38 (1970), §1; Carlson--Müller-Stach--Peters, ch. 4. -/
theorem d2_chartPeriod_holomorphic [IsManifold 𝓘(ℂ, E) ω B] (X : d2_MarkedPeriodFamily E B g)
    (b₀ : B) :
    ContMDiffOn 𝓘(ℂ, E) 𝓘(ℂ, d2_ChartTarget g) ω (d2_chartPeriod X b₀)
      (d2_chartDomain X b₀) :=
  d2_chartPeriod_holomorphic_aux X b₀

example [IsManifold 𝓘(ℂ, E) ω B] (X : d2_MarkedPeriodFamily E B g) (b₀ : B) :
    ContMDiffAt 𝓘(ℂ, E) 𝓘(ℂ, d2_ChartTarget g) ω (d2_chartPeriod X b₀) b₀ :=
  (d2_chartPeriod_holomorphic X b₀).contMDiffAt
    (isOpen_interior.mem_nhds (d2_mem_chartDomain X b₀))

/-- **The differential of the period map is the Kodaira--Spencer map.** At a point of the chart
domain, a tangent vector is killed by the differential of the chart period map exactly when its
Kodaira--Spencer map `H^{1,0} → H¹/F¹` is zero: the chart `F ↦ (projection onto F along
\bar F¹_{b₀})` is an immersion of the open set of complements, with differential
`ψ ↦ ψ ∘ π_F` on `Hom(F, H¹/F)`.
Source: Griffiths, *Periods of integrals on algebraic manifolds I*, Amer. J. Math. 90 (1968),
§1 and Proposition 1.20; Voisin, *Hodge Theory I*, Theorem 10.21; Carlson--Müller-Stach--Peters,
ch. 5. -/
theorem d2_ker_mfderiv_chartPeriod [IsManifold 𝓘(ℂ, E) ω B] (X : d2_MarkedPeriodFamily E B g)
    (b₀ b : B) (hb : b ∈ d2_chartDomain X b₀) :
    LinearMap.ker (show E →L[ℂ] d2_ChartTarget g from
      mfderiv 𝓘(ℂ, E) 𝓘(ℂ, d2_ChartTarget g) (d2_chartPeriod X b₀) b).toLinearMap =
      LinearMap.ker (d2_kodairaSpencer X b) :=
  d2_ker_mfderiv_chartPeriod_aux X b₀ b hb

example [IsManifold 𝓘(ℂ, E) ω B] (X : d2_MarkedPeriodFamily E B g) (b₀ : B) :
    LinearMap.ker (show E →L[ℂ] d2_ChartTarget g from
      mfderiv 𝓘(ℂ, E) 𝓘(ℂ, d2_ChartTarget g) (d2_chartPeriod X b₀) b₀).toLinearMap =
      LinearMap.ker (d2_kodairaSpencer X b₀) :=
  d2_ker_mfderiv_chartPeriod X b₀ b₀ (d2_mem_chartDomain X b₀)

/-- The rank of the differential of the period map is the rank of the Kodaira--Spencer map
(rank--nullity, from the equality of kernels).
Source: Griffiths, Amer. J. Math. 90 (1968), §1; Voisin, *Hodge Theory I*, Theorem 10.21. -/
theorem d2_finrank_range_mfderiv [IsManifold 𝓘(ℂ, E) ω B] [FiniteDimensional ℂ E]
    (X : d2_MarkedPeriodFamily E B g) (b₀ b : B) (hb : b ∈ d2_chartDomain X b₀) :
    Module.finrank ℂ (LinearMap.range (show E →L[ℂ] d2_ChartTarget g from
      mfderiv 𝓘(ℂ, E) 𝓘(ℂ, d2_ChartTarget g) (d2_chartPeriod X b₀) b).toLinearMap) =
      Module.finrank ℂ (LinearMap.range (d2_kodairaSpencer X b)) :=
  d2_finrank_range_mfderiv_aux X b₀ b hb

example [IsManifold 𝓘(ℂ, E) ω B] [FiniteDimensional ℂ E] (X : d2_MarkedPeriodFamily E B g)
    (b₀ : B) :
    Module.finrank ℂ (LinearMap.range (show E →L[ℂ] d2_ChartTarget g from
      mfderiv 𝓘(ℂ, E) 𝓘(ℂ, d2_ChartTarget g) (d2_chartPeriod X b₀) b₀).toLinearMap) =
      Module.finrank ℂ (LinearMap.range (d2_kodairaSpencer X b₀)) :=
  d2_finrank_range_mfderiv X b₀ b₀ (d2_mem_chartDomain X b₀)

/-- **The rank criterion.** If the Kodaira--Spencer map has rank `dim B` at `b`, the
differential of the period map at `b` is injective: the period map is an immersion there.
Source: Griffiths, Amer. J. Math. 90 (1968), §1; Carlson--Müller-Stach--Peters, ch. 5
(infinitesimal Torelli). -/
theorem d2_mfderiv_injective_of_rank [IsManifold 𝓘(ℂ, E) ω B] [FiniteDimensional ℂ E]
    (X : d2_MarkedPeriodFamily E B g) (b₀ b : B) (hb : b ∈ d2_chartDomain X b₀)
    (hrank : Module.finrank ℂ (LinearMap.range (d2_kodairaSpencer X b)) =
      Module.finrank ℂ E) :
    Function.Injective (show E →L[ℂ] d2_ChartTarget g from
      mfderiv 𝓘(ℂ, E) 𝓘(ℂ, d2_ChartTarget g) (d2_chartPeriod X b₀) b) :=
  d2_mfderiv_injective_of_rank_aux X b₀ b hb hrank

example [IsManifold 𝓘(ℂ, E) ω B] [FiniteDimensional ℂ E] (X : d2_MarkedPeriodFamily E B g) (b : B)
    (hrank : Module.finrank ℂ (LinearMap.range (d2_kodairaSpencer X b)) =
      Module.finrank ℂ E) :
    Function.Injective (show E →L[ℂ] d2_ChartTarget g from
      mfderiv 𝓘(ℂ, E) 𝓘(ℂ, d2_ChartTarget g) (d2_chartPeriod X b) b) :=
  d2_mfderiv_injective_of_rank X b b (d2_mem_chartDomain X b) hrank

/-- If the Kodaira--Spencer map has rank `dim B` at `b`, then `b' ↦ F¹_{b'}` is injective near
`b`: the immersion theorem applied to the chart period map centred at `b`.
Source: Griffiths, Amer. J. Math. 90 (1968), §1; Lang, *Fundamentals of Differential Geometry*,
ch. I, §5 (immersions are locally injective). -/
theorem d2_hodgeOne_injOn_of_rank [IsManifold 𝓘(ℂ, E) ω B] [FiniteDimensional ℂ E]
    (X : d2_MarkedPeriodFamily E B g) (b : B)
    (hrank : Module.finrank ℂ (LinearMap.range (d2_kodairaSpencer X b)) =
      Module.finrank ℂ E) :
    ∃ W ∈ 𝓝 b, Set.InjOn (fun b' ↦ d2_hodgeOne (X.period b')) W :=
  d2_hodgeOne_injOn_of_rank_aux X b hrank

example [IsManifold 𝓘(ℂ, E) ω B] [FiniteDimensional ℂ E] (X : d2_MarkedPeriodFamily E B g) (b : B)
    (hrank : Module.finrank ℂ (LinearMap.range (d2_kodairaSpencer X b)) =
      Module.finrank ℂ E) :
    ∃ W ∈ 𝓝 b, ∀ b' ∈ W, d2_hodgeOne (X.period b') = d2_hodgeOne (X.period b) → b' = b :=
  let ⟨W, hW, hinj⟩ := d2_hodgeOne_injOn_of_rank X b hrank
  ⟨W, hW, fun _ hb' h ↦ hinj hb' (mem_of_mem_nhds hW) h⟩

/-- Constant period data has Kodaira--Spencer map zero (the degenerate case of the rank
criterion).
Source: Kodaira, *Complex Manifolds and Deformation of Complex Structures*, §4.1 (trivial
families). -/
theorem d2_kodairaSpencer_const [IsManifold 𝓘(ℂ, E) ω B] (P : Fin g → Fin (2 * g) → ℂ)
    (hP : d2_IsPeriodMatrix P) (b : B) : d2_kodairaSpencer (d2_constFamily E B P hP) b = 0 :=
  d2_kodairaSpencer_const_aux P hP b

example (P : Fin g → Fin (2 * g) → ℂ) (hP : d2_IsPeriodMatrix P) (b : E) :
    Module.finrank ℂ (LinearMap.range (d2_kodairaSpencer (d2_constFamily E E P hP) b)) = 0 := by
  rw [d2_kodairaSpencer_const P hP b, LinearMap.range_zero, finrank_bot]

end Differential

section Witnesses

/-- **The elliptic period data** `τ ↦ (1, τ)` over the upper half plane, presenting the tori
`ℂ / (ℤ + ℤ τ)`.
Source: Birkenhake--Lange, *Complex Abelian Varieties*, 2nd ed., §8.1; Kodaira, *Complex
Manifolds and Deformation of Complex Structures*, §2.3. -/
def d2_ellipticPeriodFamily : d2_MarkedPeriodFamily ℂ d2_upperHalf 1 where
  period τ := d2_ellipticPeriod τ
  holomorphic := d2_ellipticPeriod_holomorphic
  isPeriod τ := d2_ellipticPeriod_isPeriodMatrix (ne_of_gt τ.2)

example (τ : d2_upperHalf) : d2_ellipticPeriodFamily.period τ = d2_ellipticPeriod τ := rfl

/-- The elliptic period data has injective Kodaira--Spencer map at every point, so its period map is
an immersion (`d2_mfderiv_injective_of_rank` applies with rank one).
Source: Kodaira, *Complex Manifolds and Deformation of Complex Structures*, §4.1; Griffiths,
Amer. J. Math. 90 (1968), §1. -/
theorem d2_kodairaSpencer_elliptic_injective (τ : d2_upperHalf) :
    Function.Injective (d2_kodairaSpencer d2_ellipticPeriodFamily τ) :=
  d2_kodairaSpencer_elliptic_injective_aux _ _ τ

example (τ : d2_upperHalf) :
    Module.finrank ℂ (LinearMap.range (d2_kodairaSpencer d2_ellipticPeriodFamily τ)) =
      Module.finrank ℂ ℂ := by
  rw [LinearMap.finrank_range_of_inj (d2_kodairaSpencer_elliptic_injective τ)]

/-- The elliptic period data carries the associated variation of weight one, polarized by the
standard form.
Source: Birkenhake--Lange, *Complex Abelian Varieties*, 2nd ed., §8.1. -/
def d2_ellipticVHS : d1_PolarizedVHS ℂ d2_upperHalf :=
  d2_toriVHS d2_ellipticPeriodFamily d2_stdRiemann fun τ ↦ d2_ellipticPeriod_isRiemannForm τ.2

example : d2_ellipticVHS.weight = 1 := rfl

end Witnesses

section G32

variable {g : ℕ} {W : TopologicalSpace.Opens (Fin 10 → ℂ)}

/-- The chart of period data over an open set of `ℂ¹⁰` is open in `ℂ¹⁰`.
Source: G32 v0.16, §5; Griffiths, Publ. Math. IHES 38 (1970), §1. -/
theorem d2_g32Chart_isOpen (X : d2_MarkedPeriodFamily (Fin 10 → ℂ) W g) (b₀ : W) :
    IsOpen (d2_g32Chart X b₀) :=
  d2_g32Chart_isOpen_aux X b₀

example (X : d2_MarkedPeriodFamily (Fin 10 → ℂ) W g) (b₀ : W) :
    (b₀ : Fin 10 → ℂ) ∈ d2_g32Chart X b₀ :=
  ⟨b₀, d2_mem_chartDomain X b₀, rfl⟩

/-- With an analytic coordinate change `κ`, the period map `κ ∘ d2_chartPeriod` is analytic on
the chart.
Source: G32 v0.16, §5 and Lemma 5.1; Griffiths, Publ. Math. IHES 38 (1970), §1. -/
theorem d2_g32Period_analytic (X : d2_MarkedPeriodFamily (Fin 10 → ℂ) W g) (b₀ : W)
    (κ : d2_ChartTarget g → Fin 9 → ℂ)
    (hκ : AnalyticOnNhd ℂ κ (d2_chartPeriod X b₀ '' d2_chartDomain X b₀)) :
    AnalyticOnNhd ℂ (d2_g32Period X b₀ κ) (d2_g32Chart X b₀) :=
  d2_g32Period_analytic_aux X b₀ κ hκ

example (X : d2_MarkedPeriodFamily (Fin 10 → ℂ) W g) (b₀ : W)
    (κ : d2_ChartTarget g →L[ℂ] Fin 9 → ℂ) :
    AnalyticOnNhd ℂ (d2_g32Period X b₀ κ) (d2_g32Chart X b₀) :=
  d2_g32Period_analytic X b₀ κ fun _ _ ↦ κ.analyticAt _

/-- **The rank in G32's form.** At a point of the chart, if `dκ` is injective on the image of the
differential of the chart period map, the derivative of `κ ∘ d2_chartPeriod` has the rank of the
Kodaira--Spencer map.
Source: G32 v0.16, Lemma 5.1 and Corollary 5.11; Griffiths, Amer. J. Math. 90 (1968), §1. -/
theorem d2_g32_finrank (X : d2_MarkedPeriodFamily (Fin 10 → ℂ) W g) (b₀ b : W)
    (hb : b ∈ d2_chartDomain X b₀) (κ : d2_ChartTarget g → Fin 9 → ℂ)
    (hκ : DifferentiableAt ℂ κ (d2_chartPeriod X b₀ b))
    (hinj : Disjoint (LinearMap.ker (fderiv ℂ κ (d2_chartPeriod X b₀ b)).toLinearMap)
      (LinearMap.range (show (Fin 10 → ℂ) →L[ℂ] d2_ChartTarget g from
        mfderiv 𝓘(ℂ, Fin 10 → ℂ) 𝓘(ℂ, d2_ChartTarget g) (d2_chartPeriod X b₀) b).toLinearMap)) :
    Module.finrank ℂ (LinearMap.range
      (fderiv ℂ (d2_g32Period X b₀ κ) b : (Fin 10 → ℂ) →ₗ[ℂ] Fin 9 → ℂ)) =
      Module.finrank ℂ (LinearMap.range (d2_kodairaSpencer X b)) :=
  d2_g32_finrank_aux X b₀ b hb κ hκ hinj

/-- **Rank nine, G32's form.** If moreover the Kodaira--Spencer map has rank nine, the derivative
of the period map has rank nine, the hypothesis of `g32r_open_image` and the conclusion of
`g32r_period_rank_nine`.
Source: G32 v0.16, Corollary 5.11 and the proof of Theorem 7.2. -/
theorem d2_g32_rank_nine (X : d2_MarkedPeriodFamily (Fin 10 → ℂ) W g) (b₀ b : W)
    (hb : b ∈ d2_chartDomain X b₀) (κ : d2_ChartTarget g → Fin 9 → ℂ)
    (hκ : DifferentiableAt ℂ κ (d2_chartPeriod X b₀ b))
    (hinj : Disjoint (LinearMap.ker (fderiv ℂ κ (d2_chartPeriod X b₀ b)).toLinearMap)
      (LinearMap.range (show (Fin 10 → ℂ) →L[ℂ] d2_ChartTarget g from
        mfderiv 𝓘(ℂ, Fin 10 → ℂ) 𝓘(ℂ, d2_ChartTarget g) (d2_chartPeriod X b₀) b).toLinearMap))
    (h9 : Module.finrank ℂ (LinearMap.range (d2_kodairaSpencer X b)) = 9) :
    Module.finrank ℂ (LinearMap.range
      (fderiv ℂ (d2_g32Period X b₀ κ) b : (Fin 10 → ℂ) →ₗ[ℂ] Fin 9 → ℂ)) = 9 :=
  d2_g32_rank_nine_aux X b₀ b hb κ hκ hinj h9

/-- **The adapter into `g32r_PeriodMap`.** It supplies `V` (the chart `d2_g32Chart`),
`isOpen_V` (`d2_g32Chart_isOpen`), `period` (`κ ∘ d2_chartPeriod`) and `analytic`
(`d2_g32Period_analytic`). The remaining fields stay inputs, each assigned to a later stage:
`mapsTo` (that `κ` lands in `𝓗₃`), `isog` (the fibres of `P` and `F`) and the Schlesinger path
`curve`, `curve_cont`, `curve_zero` go to B3/B4 (curves, Jacobians, Hurwitz covers, Prym
idempotents) or the G32 family stage; `jet` and `jet_certified` go to the concrete exported
certificate; `codiff` (FGP's identification of the jet with the derivative) goes to the FGP
comparison, in the form given by `d2_g32_finrank`. Rank nine of a certified jet is not a
further premise: `g32r_jet_rank_nine` already derives it from `g32r_CertifiedJet`.
Source: G32 v0.16, §5 and the proof of Theorem 7.2; Frediani--Ghigi--Penegini, IMRN 2015,
§§2--3. -/
def d2_g32PeriodMap (F : g32m_UniversalFamily) (P : g32h_PrymFamily)
    (X : d2_MarkedPeriodFamily (Fin 10 → ℂ) W g) (b₀ : W) (κ : d2_ChartTarget g → Fin 9 → ℂ)
    (hκ : AnalyticOnNhd ℂ κ (d2_chartPeriod X b₀ '' d2_chartDomain X b₀))
    (mapsTo : Set.MapsTo (d2_g32Period X b₀ κ) (d2_g32Chart X b₀)
      (g32m_Domain : Set (Fin 9 → ℂ)))
    (isog : ∀ t (ht : t ∈ d2_g32Chart X b₀),
      ∃ s, g32t_KIsog (P.fiber s) (F.univ ⟨d2_g32Period X b₀ κ t, mapsTo ht⟩))
    (curve : ℂ → Fin 10 → ℂ) (curve_cont : ContinuousAt curve 0)
    (curve_zero : curve 0 ∈ d2_g32Chart X b₀)
    (jet : ℂ → Matrix (Fin 9) (Fin 10) ℂ) (jet_certified : g32r_CertifiedJet jet)
    (codiff : ∀ᶠ θ in 𝓝 (0 : ℂ), ∃ L : Matrix (Fin 9) (Fin 9) ℂ,
      ∃ R : Matrix (Fin 10) (Fin 10) ℂ, IsUnit L ∧ IsUnit R ∧
        jet θ = L * LinearMap.toMatrix'
          (fderiv ℂ (d2_g32Period X b₀ κ) (curve θ) : (Fin 10 → ℂ) →ₗ[ℂ] Fin 9 → ℂ) * R) :
    g32r_PeriodMap F P where
  V := d2_g32Chart X b₀
  isOpen_V := d2_g32Chart_isOpen X b₀
  period := d2_g32Period X b₀ κ
  analytic := d2_g32Period_analytic X b₀ κ hκ
  mapsTo := mapsTo
  isog := isog
  curve := curve
  curve_cont := curve_cont
  curve_zero := curve_zero
  jet := jet
  jet_certified := jet_certified
  codiff := codiff

example (F : g32m_UniversalFamily) (P : g32h_PrymFamily)
    (X : d2_MarkedPeriodFamily (Fin 10 → ℂ) W g) (b₀ : W) (κ : d2_ChartTarget g → Fin 9 → ℂ)
    (hκ : AnalyticOnNhd ℂ κ (d2_chartPeriod X b₀ '' d2_chartDomain X b₀))
    (mapsTo : Set.MapsTo (d2_g32Period X b₀ κ) (d2_g32Chart X b₀)
      (g32m_Domain : Set (Fin 9 → ℂ)))
    (isog : ∀ t (ht : t ∈ d2_g32Chart X b₀),
      ∃ s, g32t_KIsog (P.fiber s) (F.univ ⟨d2_g32Period X b₀ κ t, mapsTo ht⟩))
    (curve : ℂ → Fin 10 → ℂ) (curve_cont : ContinuousAt curve 0)
    (curve_zero : curve 0 ∈ d2_g32Chart X b₀)
    (jet : ℂ → Matrix (Fin 9) (Fin 10) ℂ) (jet_certified : g32r_CertifiedJet jet)
    (codiff : ∀ᶠ θ in 𝓝 (0 : ℂ), ∃ L : Matrix (Fin 9) (Fin 9) ℂ,
      ∃ R : Matrix (Fin 10) (Fin 10) ℂ, IsUnit L ∧ IsUnit R ∧
        jet θ = L * LinearMap.toMatrix'
          (fderiv ℂ (d2_g32Period X b₀ κ) (curve θ) : (Fin 10 → ℂ) →ₗ[ℂ] Fin 9 → ℂ) * R) :
    (d2_g32PeriodMap F P X b₀ κ hκ mapsTo isog curve curve_cont curve_zero jet jet_certified
      codiff).period = d2_g32Period X b₀ κ := rfl

end G32

end HodgeLean.Foundations.Program
