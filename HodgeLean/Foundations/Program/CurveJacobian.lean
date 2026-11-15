import HodgeLean.Foundations.Program.CurveJacobianProofs

/-! # Track B3, compact Riemann surfaces and their Jacobians (FROZEN SPEC)

Each theorem is the matching `_aux` theorem of `CurveJacobianProofs.lean`. The objects are
constructed in `CurveJacobianDefs.lean` (route R1, analytic): a Riemann surface is a type `C` with
`ChartedSpace E C` and `IsManifold 𝓘(ℂ, E) ω C` for a complex line `E` (`finrank ℂ E = 1`); a
compact connected Riemann surface adds `T2Space C`, `CompactSpace C`, `ConnectedSpace C`. On it:
* `Ω¹(C) = b3_HolForm E C`, holomorphic functions on the tangent bundle, linear on fibres;
* the periods `b3_period γ : Ω¹(C) → ℂ` of `C¹` loops `γ` (`∫₀¹ θ(γ t, γ' t) dt`), the period
  lattice `Λ_C = b3_periodLattice E C` they generate (the model of `H₁(C, ℤ)`), the complexified
  period map `b3_cplxPeriod`, its kernel `F_C = b3_periodF E C`, and the Jacobian
  `J(C) = b3_Jacobian E C = b2_torus Λ_C F_C`;
* the signed intersection number `b3_intersection γ δ` of two loops, transversality, and the
  property `b3_IsIntersectionForm Q` of a form on `Λ_C`;
* the property `b3_IsAbelJacobi p₀ aj` of a map `C → J(C)`, the pullback `b3_pullback f` of
  functions on tangent bundles, and the property `b3_IsPushforward f g` of a lattice map.

**Claimed.** For a compact connected Riemann surface `C`: `Ω¹(C)` is finite-dimensional, and
`dim H¹(C; ℚ) = rk Λ_C = 2 dim Ω¹(C)` (so `dim Ω¹ = g` for the topological genus `g = b₁ / 2`);
`Λ_C` is a finite free `ℤ`-module whose `ℂ`-span is the dual `Ω¹(C)^∨`, and `F_C` is a weight-one
Hodge structure on it, so `J(C) = Ω¹(C)^∨ ⧸ Λ_C` is a compact complex torus of dimension `g` by
B2. Two loops have the same periods exactly when they define the same functional on `H¹(C; ℚ)`,
and every continuous loop has a `C¹` loop with the same functional (`Λ_C ≅ H₁(C, ℤ)`). On a
Hausdorff surface transverse loops cross finitely often, intersection numbers are antisymmetric, there is a unique form on
`Λ_C` computing them, and that form is a unimodular Riemann form for `F_C` (the Riemann bilinear
relations): `J(C)` is a principally polarized B2 torus. The Abel–Jacobi map exists, is unique and
is holomorphic. A holomorphic map `f : C → C'` pulls back holomorphic forms, path integrals
satisfy the chain rule, the pushforward `f_* : Λ_C → Λ_C'` exists, is unique and preserves the
filtrations (so `J(f)_* = b2_torusHom` exists), the pullback `f^*` exists as its adjoint for the
intersection forms and preserves the filtrations, and the Abel–Jacobi maps are natural.
Satisfiable instance: the elliptic curve `ℂ ⧸ (ℤ + iℤ)` (B2's `b2_torus ℤ² b2_stdF`) is
connected, `dim Ω¹ = 1`, and its Abel–Jacobi map is bijective (`J = C`). Explicit checks on it:
the loops `a : t ↦ [t e₀]` and `b : t ↦ [t e₁]` are `C¹`, have periods `1` and `i` against `dz`,
are transverse with `a · b = 1`, every intersection form equals any alternating form normalized
by `Q'(λ_a, λ_b) = 1`, and an Abel–Jacobi map based at `0` sends `[s e₀ + t e₁]` to
`[s ⊗ λ_a + t ⊗ λ_b]`. Degenerate case ruled out: on the non-compact surface `ℂ`, `Ω¹` is
infinite-dimensional.

**Not claimed.** No algebraic curves, Picard schemes or `Pic⁰` (route R2), and no comparison of
`J(C)` with the complex points of an abelian variety beyond B2's. No Riemann–Roch, no theta
divisor, no Abel's theorem on divisors and no Jacobi inversion beyond the elliptic case. The map
from singular `H₁(C, ℤ)` to `Λ_C` is described through `H¹(C; ℚ)` and loops, not constructed on
singular chains. No families of curves, no Hurwitz covers and no Prym idempotents (stage B4); none
of the fields of `g32h_PrymFamily` or `g34h_PrymFamily` is supplied here. HC no distance; AV
milestone no distance.
-/

noncomputable section

open Manifold HodgeLean.Adapters AlgebraicTopology.Singular
open scoped TensorProduct ContDiff

namespace HodgeLean.Foundations.Program

/-! ## The elliptic curve -/

/-- **The elliptic curve is connected**: it is a continuous image of the connected vector space
`ℂ ⊗ ℤ²`.
Source: Bourbaki, *Topologie générale*, ch. I, §11 (images of connected spaces); Birkenhake–Lange,
*Complex Abelian Varieties*, 2nd ed., Grundlehren 302, §1.1. -/
theorem b3_elliptic_connectedSpace : ConnectedSpace b3_Elliptic :=
  b3_elliptic_connectedSpace_aux

example : Nonempty b3_Elliptic := b3_elliptic_connectedSpace.toNonempty

/-- **The elliptic curve has genus one**: `Ω¹ = ℂ dz`.
Source: Forster, *Lectures on Riemann Surfaces*, §21 (tori have genus one); Birkenhake–Lange,
§1.1. -/
theorem b3_elliptic_finrank_holForm :
    Module.finrank ℂ (b3_HolForm b3_EllipticModel b3_Elliptic) = 1 :=
  b3_elliptic_finrank_holForm_aux

example : Module.finrank ℂ (b3_HolForm b3_EllipticModel b3_Elliptic) ≠ 0 := by
  rw [b3_elliptic_finrank_holForm]
  exact one_ne_zero

/-! ## Explicit loops of the elliptic curve

`a = b3_ellipticA` is `t ↦ [t e₀]` (`z = t`) and `b = b3_ellipticB` is `t ↦ [t e₁]` (`z = i t`),
in the coordinate `z` of `ℂ ⧸ (ℤ + iℤ)` with `[e₀] ↦ 1`. The statements below take `C¹` loops `a`,
`b` with these underlying maps; the first two statements build them. -/

/-- **The loop `a` is `C¹`**: in each chart of B2's torus it is `t ↦ t [e₀]` up to a lattice
translation.
Source: Birkenhake–Lange, §1.1 (charts of `V ⧸ Λ` are local sections of the quotient); Lee,
*Introduction to Smooth Manifolds*, 2nd ed., GTM 218, Ch. 3 (smooth curves). -/
theorem b3_ellipticA_contMDiff :
    ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, b3_EllipticModel) 1 b3_ellipticA :=
  b3_ellipticA_contMDiff_aux

/-- **The loop `b` is `C¹`**, as for `a`.
Source: Birkenhake–Lange, §1.1; Lee, Ch. 3. -/
theorem b3_ellipticB_contMDiff :
    ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, b3_EllipticModel) 1 b3_ellipticB :=
  b3_ellipticB_contMDiff_aux

example : ∃ a b : b3_SmoothLoop b3_EllipticModel b3_Elliptic,
    a.1 = b3_ellipticA ∧ b.1 = b3_ellipticB :=
  ⟨⟨b3_ellipticA, fun t ↦ (b3_ellipticPoint_add_one t 0).1, b3_ellipticA_contMDiff⟩,
    ⟨b3_ellipticB, fun t ↦ (b3_ellipticPoint_add_one 0 t).2, b3_ellipticB_contMDiff⟩, rfl, rfl⟩

/-- **The periods of `a` and `b` are `1` and `i`** against the form `dz` (`θ([z], v) = v` in the
coordinate `z`, translation invariant, hence holomorphic): `∫₀¹ dz(a') = 1`, `∫₀¹ dz(b') = i`.
Source: Forster, *Lectures on Riemann Surfaces*, GTM 81, §21 (the periods of `dz` on
`ℂ ⧸ (ℤ ω₁ + ℤ ω₂)` are `ω₁`, `ω₂`); Birkenhake–Lange, §1.1. -/
theorem b3_elliptic_periods (a b : b3_SmoothLoop b3_EllipticModel b3_Elliptic)
    (ha : a.1 = b3_ellipticA) (hb : b.1 = b3_ellipticB) :
    ∃ θ : b3_HolForm b3_EllipticModel b3_Elliptic,
      b3_period _ _ a θ = 1 ∧ b3_period _ _ b θ = Complex.I :=
  b3_elliptic_periods_aux a b ha hb

/-- The loops `a` and `b` have distinct periods. -/
example (a b : b3_SmoothLoop b3_EllipticModel b3_Elliptic)
    (ha : a.1 = b3_ellipticA) (hb : b.1 = b3_ellipticB) :
    b3_period _ _ a ≠ b3_period _ _ b := by
  obtain ⟨θ, h1, hI⟩ := b3_elliptic_periods a b ha hb
  intro h
  have := congrArg Complex.im ((congrFun h θ).symm.trans h1 ▸ hI)
  simp at this

/-- **`a` and `b` are transverse**: they cross only at `(s, t) = (0, 0)` (where `[s e₀] = [t e₁]`
forces `s, t ∈ ℤ`, as `e₀`, `e₁` are `ℝ`-independent in `(ℂ ⊗ ℤ²) ⧸ F`), with velocities `v` and
`i v` in the chart, and `Im (v̄ · i v) = |v|² > 0`.
Source: Guillemin–Pollack, *Differential Topology*, Ch. 1 §5 (transversality); Birkenhake–Lange,
§1.1. -/
theorem b3_elliptic_transverse (a b : b3_SmoothLoop b3_EllipticModel b3_Elliptic)
    (ha : a.1 = b3_ellipticA) (hb : b.1 = b3_ellipticB) :
    b3_Transverse b3_EllipticModel a b :=
  b3_elliptic_transverse_aux a b ha hb

/-- **`a · b = 1`**: one crossing, positively oriented (the pair `(v, i v)`).
Source: Farkas–Kra, *Riemann Surfaces*, 2nd ed., GTM 71, Ch. III (a canonical homology basis of
a torus has `a · b = 1`); Guillemin–Pollack, Ch. 3 §3. -/
theorem b3_elliptic_intersection (a b : b3_SmoothLoop b3_EllipticModel b3_Elliptic)
    (ha : a.1 = b3_ellipticA) (hb : b.1 = b3_ellipticB) :
    b3_intersection b3_EllipticModel a b = 1 :=
  b3_elliptic_intersection_aux a b ha hb

/-- **The intersection form of the elliptic curve is the standard symplectic form**: an
intersection form `Q` (characterized by crossing counts of transverse loops) equals any
alternating form `Q'` normalized by `Q'(λ_a, λ_b) = 1` (characterized algebraically). The periods
`λ_a`, `λ_b` generate `Λ_C ≅ H₁ = ℤ²`, and an alternating form on `ℤ²` is fixed by its value on a
basis.
Source: Farkas–Kra, Ch. III (the intersection matrix `[0 1; -1 0]` of a canonical basis);
Forster, §21. -/
theorem b3_elliptic_intersectionForm_eq (a b : b3_SmoothLoop b3_EllipticModel b3_Elliptic)
    (ha : a.1 = b3_ellipticA) (hb : b.1 = b3_ellipticB)
    (Q : LinearMap.BilinForm ℤ (b3_periodLattice b3_EllipticModel b3_Elliptic))
    (hQ : b3_IsIntersectionForm b3_EllipticModel Q)
    (Q' : LinearMap.BilinForm ℤ (b3_periodLattice b3_EllipticModel b3_Elliptic))
    (hQ'alt : ∀ x, Q' x x = 0)
    (hQ'ab : Q' (b3_latticePeriod _ _ a) (b3_latticePeriod _ _ b) = 1) :
    Q = Q' :=
  b3_elliptic_intersectionForm_eq_aux a b ha hb Q hQ Q' hQ'alt hQ'ab

/-- A normalized alternating form computes the intersection numbers of all transverse loops. -/
example (a b : b3_SmoothLoop b3_EllipticModel b3_Elliptic)
    (ha : a.1 = b3_ellipticA) (hb : b.1 = b3_ellipticB)
    (Q : LinearMap.BilinForm ℤ (b3_periodLattice b3_EllipticModel b3_Elliptic))
    (hQ : b3_IsIntersectionForm b3_EllipticModel Q)
    (Q' : LinearMap.BilinForm ℤ (b3_periodLattice b3_EllipticModel b3_Elliptic))
    (hQ'alt : ∀ x, Q' x x = 0)
    (hQ'ab : Q' (b3_latticePeriod _ _ a) (b3_latticePeriod _ _ b) = 1) :
    b3_IsIntersectionForm b3_EllipticModel Q' :=
  b3_elliptic_intersectionForm_eq a b ha hb Q hQ Q' hQ'alt hQ'ab ▸ hQ

/-- **The Abel–Jacobi map of the elliptic curve in coordinates**: the point `[s e₀ + t e₁]`
(`z = s + i t`) maps to the class of `s ⊗ λ_a + t ⊗ λ_b`. Along the segment from `0`, every
holomorphic form is `c dz` and integrates to `c (s + i t) = s ∫_a + t ∫_b`.
Source: Forster, *Lectures on Riemann Surfaces*, §21 (`∫₀^z dz = z` and the Abel–Jacobi map of a
torus); Birkenhake–Lange, §1.1 and Ch. 11. -/
theorem b3_elliptic_abelJacobi_apply (a b : b3_SmoothLoop b3_EllipticModel b3_Elliptic)
    (ha : a.1 = b3_ellipticA) (hb : b.1 = b3_ellipticB)
    (aj : b3_Elliptic → b3_Jacobian b3_EllipticModel b3_Elliptic)
    (h : b3_IsAbelJacobi b3_EllipticModel b3_Elliptic 0 aj) (s t : ℝ) :
    aj (b3_ellipticPoint s t) = QuotientAddGroup.mk (Submodule.Quotient.mk
      ((s : ℂ) ⊗ₜ[ℤ] b3_latticePeriod _ _ a + (t : ℂ) ⊗ₜ[ℤ] b3_latticePeriod _ _ b)) :=
  b3_elliptic_abelJacobi_apply_aux a b ha hb aj h s t

/-- The point `[e₀]`, which is `0`, goes to the class of the lattice vector `λ_a`, which is `0`. -/
example (a b : b3_SmoothLoop b3_EllipticModel b3_Elliptic)
    (ha : a.1 = b3_ellipticA) (hb : b.1 = b3_ellipticB)
    (aj : b3_Elliptic → b3_Jacobian b3_EllipticModel b3_Elliptic)
    (h : b3_IsAbelJacobi b3_EllipticModel b3_Elliptic 0 aj) :
    aj (b3_ellipticPoint 1 0) = 0 := by
  refine (b3_elliptic_abelJacobi_apply a b ha hb aj h 1 0).trans
    ((QuotientAddGroup.eq_zero_iff _).2 ⟨b3_latticePeriod _ _ a, congrArg Submodule.Quotient.mk ?_⟩)
  change (1 : ℂ) ⊗ₜ[ℤ] _ = _
  simp only [Complex.ofReal_one, Complex.ofReal_zero, TensorProduct.zero_tmul, add_zero]

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
variable {C : Type} [TopologicalSpace C] [ChartedSpace E C] [IsManifold 𝓘(ℂ, E) ω C]

/-! ## Holomorphic forms and the period lattice -/

/-- **`Ω¹(C)` is finite-dimensional** for a compact Riemann surface.
Source: Forster, *Lectures on Riemann Surfaces*, GTM 81, §14 (the finiteness theorem) and §17
(`dim Ω = g` by Serre duality); Cartan–Serre, *Un théorème de finitude concernant les variétés
analytiques compactes*, C. R. Acad. Sci. Paris 237 (1953). -/
theorem b3_holForm_finiteDimensional [T2Space C] [CompactSpace C] [ConnectedSpace C]
    (hE : Module.finrank ℂ E = 1) :
    FiniteDimensional ℂ (b3_HolForm E C) :=
  b3_holForm_finiteDimensional_aux hE

example : FiniteDimensional ℂ (b3_HolForm b3_EllipticModel b3_Elliptic) :=
  haveI := b3_elliptic_connectedSpace
  b3_holForm_finiteDimensional b3_ellipticModel_finrank

/-- **On the non-compact surface `ℂ`, `Ω¹` is infinite-dimensional**: the forms `zⁿ dz` are
linearly independent. This is the degenerate case that compactness rules out.
Source: Forster, *Lectures on Riemann Surfaces*, §9 (holomorphic `1`-forms on `ℂ` are `f(z) dz`
for entire `f`). -/
theorem b3_complexPlane_not_finiteDimensional :
    ¬ FiniteDimensional ℂ (b3_HolForm ℂ ℂ) :=
  b3_complexPlane_not_finiteDimensional_aux

example : ¬ Module.Finite ℂ (b3_HolForm ℂ ℂ) := b3_complexPlane_not_finiteDimensional

/-- **Periods are linear**: the period of a `C¹` loop is a `ℂ`-linear functional on `Ω¹(C)` (the
integrand is continuous, hence integrable).
Source: Forster, *Lectures on Riemann Surfaces*, §10 and §20. -/
theorem b3_period_mem_linearDual (γ : b3_SmoothLoop E C) :
    b3_period E C γ ∈ b3_linearDual E C :=
  b3_period_mem_linearDual_aux γ

example (x : b3_Elliptic) :
    b3_period b3_EllipticModel b3_Elliptic (b3_constLoop _ _ x) ∈ b3_linearDual _ _ :=
  b3_period_mem_linearDual _

/-- **A finitely generated period lattice is free**: it is a subgroup of the `ℂ`-vector space
`Ω¹(C) → ℂ`, hence torsion-free.
Source: Bourbaki, *Algèbre*, ch. VII, §4 (finitely generated torsion-free modules over a PID are
free); Mathlib `Module.free_of_finite_type_torsion_free'`. -/
theorem b3_periodLattice_free [Module.Finite ℤ (b3_periodLattice E C)] :
    Module.Free ℤ (b3_periodLattice E C) :=
  b3_periodLattice_free_aux

/-- **The period lattice is finitely generated**: it is the image of `H₁(C, ℤ)`, finitely
generated for a compact surface.
Source: Forster, *Lectures on Riemann Surfaces*, §21 (the period lattice); Farkas–Kra, *Riemann
Surfaces*, 2nd ed., GTM 71, Ch. III (the canonical homology basis). -/
theorem b3_periodLattice_finite [T2Space C] [CompactSpace C] [ConnectedSpace C]
    (hE : Module.finrank ℂ E = 1) :
    Module.Finite ℤ (b3_periodLattice E C) :=
  b3_periodLattice_finite_aux hE

example : Module.Free ℤ (b3_periodLattice b3_EllipticModel b3_Elliptic) :=
  haveI := b3_elliptic_connectedSpace
  haveI := b3_periodLattice_finite (C := b3_Elliptic) b3_ellipticModel_finrank
  b3_periodLattice_free

/-- **The period lattice has rank `2g`**, `g = dim Ω¹(C)`.
Source: Forster, *Lectures on Riemann Surfaces*, §21 (the periods of a basis of `Ω¹` form a
lattice of rank `2g` in `ℂ^g`); Griffiths–Harris, *Principles of Algebraic Geometry*, Ch. 2.2. -/
theorem b3_finrank_periodLattice [T2Space C] [CompactSpace C] [ConnectedSpace C]
    (hE : Module.finrank ℂ E = 1) :
    Module.finrank ℤ (b3_periodLattice E C) = 2 * Module.finrank ℂ (b3_HolForm E C) :=
  b3_finrank_periodLattice_aux hE

example : Module.finrank ℤ (b3_periodLattice b3_EllipticModel b3_Elliptic) = 2 := by
  have := b3_elliptic_connectedSpace
  rw [b3_finrank_periodLattice b3_ellipticModel_finrank, b3_elliptic_finrank_holForm]

/-- **`dim Ω¹ = g`**: the first rational Betti number of a compact connected Riemann surface is
`2 dim Ω¹(C)`.
Source: Forster, *Lectures on Riemann Surfaces*, §19 (harmonic forms: the de Rham group is
`Ω ⊕ Ω̄`) and §21; Griffiths–Harris, Ch. 2.2; Hatcher, *Algebraic Topology*, §2.2 and §3.1 (the
Betti numbers of a compact orientable surface). -/
theorem b3_finrank_cohomology [T2Space C] [CompactSpace C] [ConnectedSpace C]
    (hE : Module.finrank ℂ E = 1) :
    Module.finrank ℚ (Cohomology ℚ (TopCat.of C) 1) = 2 * Module.finrank ℂ (b3_HolForm E C) :=
  b3_finrank_cohomology_aux hE

example : Module.finrank ℚ (Cohomology ℚ (TopCat.of b3_Elliptic) 1) = 2 := by
  have := b3_elliptic_connectedSpace
  rw [b3_finrank_cohomology b3_ellipticModel_finrank, b3_elliptic_finrank_holForm]

/-- **The periods span the dual**: the `ℂ`-span of `Λ_C` in `Ω¹(C) → ℂ` is the space of linear
functionals. A form with all periods zero is `df` for a global holomorphic `f`, hence zero.
Source: Forster, *Lectures on Riemann Surfaces*, §10 (local primitives of holomorphic forms)
and §21; Griffiths–Harris, Ch. 2.2. -/
theorem b3_range_cplxPeriod [T2Space C] [CompactSpace C] [ConnectedSpace C]
    (hE : Module.finrank ℂ E = 1) :
    LinearMap.range (b3_cplxPeriod E C) = b3_linearDual E C :=
  b3_range_cplxPeriod_aux hE

example : LinearMap.range (b3_cplxPeriod b3_EllipticModel b3_Elliptic) = b3_linearDual _ _ :=
  haveI := b3_elliptic_connectedSpace
  b3_range_cplxPeriod b3_ellipticModel_finrank

/-- **The Jacobian filtration is a weight-one Hodge structure**: `ℂ ⊗ Λ_C = F_C ⊕ F̄_C`. With the
rank statement this says that `Λ_C` is a full lattice in `Ω¹(C)^∨`: its real span is the dual.
Source: Forster, *Lectures on Riemann Surfaces*, §21 (the periods are `ℝ`-linearly independent);
Birkenhake–Lange, Ch. 11; Deligne, *Théorie de Hodge II*, Publ. Math. IHES 40,
§4.4. -/
theorem b3_isWeightOne [T2Space C] [CompactSpace C] [ConnectedSpace C]
    (hE : Module.finrank ℂ E = 1) :
    b2_IsWeightOne (b3_periodLattice E C) (b3_periodF E C) :=
  b3_isWeightOne_aux hE

/-- With B2, the Jacobian of a compact connected Riemann surface is a compact complex torus. -/
example [T2Space C] [CompactSpace C] [ConnectedSpace C] (hE : Module.finrank ℂ E = 1) :
    CompactSpace (b3_Jacobian E C) ∧
      2 * Module.finrank ℂ ((ℂ ⊗[ℤ] b3_periodLattice E C) ⧸ b3_periodF E C) =
        Module.finrank ℤ (b3_periodLattice E C) :=
  haveI := b3_periodLattice_finite (E := E) (C := C) hE
  haveI := b3_periodLattice_free (E := E) (C := C)
  ⟨b2_torus_compactSpace _ (b3_isWeightOne hE), b2_two_mul_finrank _ (b3_isWeightOne hE)⟩

/-! ## Comparison with singular cohomology -/

/-- **Periods detect homology**: two `C¹` loops have the same periods on `Ω¹(C)` exactly when
they define the same functional `loopPeriod` on `H¹(C; ℚ)`. One direction is the de Rham theorem
for loops (Stokes), the other the Hodge decomposition and the torsion-freeness of `H₁(C, ℤ)`.
Source: Forster, *Lectures on Riemann Surfaces*, §10, §19 and §21 (homotopy invariance of
integrals of holomorphic forms, harmonic forms, periods); Griffiths–Harris, Ch. 2.2; Hatcher,
*Algebraic Topology*, §2.A and §3.1 (`H¹ = Hom(H₁, ℚ)`). -/
theorem b3_period_eq_iff_loopPeriod [T2Space C] [CompactSpace C] [ConnectedSpace C]
    (hE : Module.finrank ℂ E = 1) (γ δ : b3_SmoothLoop E C) (p q : C(UnitAddCircle, C))
    (hp : ∀ t : ℝ, γ.1 t = p t) (hq : ∀ t : ℝ, δ.1 t = q t) :
    b3_period E C γ = b3_period E C δ ↔ loopPeriod p = loopPeriod q :=
  b3_period_eq_iff_loopPeriod_aux hE γ δ p q hp hq

/-- The loops `a` and `b` define different functionals on `H¹(C; ℚ)`. -/
example (a b : b3_SmoothLoop b3_EllipticModel b3_Elliptic)
    (ha : a.1 = b3_ellipticA) (hb : b.1 = b3_ellipticB) (p q : C(UnitAddCircle, b3_Elliptic))
    (hp : ∀ t : ℝ, a.1 t = p t) (hq : ∀ t : ℝ, b.1 t = q t) :
    loopPeriod p ≠ loopPeriod q := by
  have := b3_elliptic_connectedSpace
  intro h
  obtain ⟨θ, h1, hI⟩ := b3_elliptic_periods a b ha hb
  have hab := congrFun
    ((b3_period_eq_iff_loopPeriod b3_ellipticModel_finrank a b p q hp hq).2 h) θ
  rw [h1, hI] at hab
  simpa using congrArg Complex.im hab

/-- **Every loop has a `C¹` representative**: for each continuous loop `p` there is a `C¹` loop
with the same functional on `H¹(C; ℚ)`. With `b3_period_eq_iff_loopPeriod`, the period lattice is
the image of `H₁(C, ℤ)` in `Hom(H¹(C; ℚ), ℚ)`, which is `H₁(C, ℤ)` for a surface.
Source: Lee, *Introduction to Smooth Manifolds*, 2nd ed., GTM 218, Ch. 6 (the Whitney
approximation theorem and smooth homotopies); Hatcher, §2.A. -/
theorem b3_exists_smoothLoop [T2Space C] [CompactSpace C] [ConnectedSpace C]
    (hE : Module.finrank ℂ E = 1) (p : C(UnitAddCircle, C)) :
    ∃ (γ : b3_SmoothLoop E C) (q : C(UnitAddCircle, C)),
      (∀ t : ℝ, γ.1 t = q t) ∧ loopPeriod q = loopPeriod p :=
  b3_exists_smoothLoop_aux hE p

example (p : C(UnitAddCircle, b3_Elliptic)) :
    ∃ (γ : b3_SmoothLoop b3_EllipticModel b3_Elliptic) (q : C(UnitAddCircle, b3_Elliptic)),
      (∀ t : ℝ, γ.1 t = q t) ∧ loopPeriod q = loopPeriod p :=
  haveI := b3_elliptic_connectedSpace
  b3_exists_smoothLoop b3_ellipticModel_finrank p

/-! ## Intersection numbers and the Riemann bilinear relations -/

/-- **Transverse loops cross finitely often** on a Hausdorff surface: transverse crossings are
isolated (inverse function theorem in a chart), `[0, 1]²` is compact, and a limit of crossings is
a crossing because limits in `C` are unique (on a non-Hausdorff manifold, crossings can accumulate
at a pair of non-separable points, which is not a crossing).
Source: Guillemin–Pollack, *Differential Topology*, Ch. 1 §5 and Ch. 3 §3. -/
theorem b3_crossings_finite [FiniteDimensional ℂ E] [T2Space C] (hE : Module.finrank ℂ E = 1)
    (γ δ : b3_SmoothLoop E C) (h : b3_Transverse E γ δ) :
    (b3_crossings E γ δ).Finite :=
  b3_crossings_finite_aux hE γ δ h

example (a b : b3_SmoothLoop b3_EllipticModel b3_Elliptic)
    (ha : a.1 = b3_ellipticA) (hb : b.1 = b3_ellipticB) :
    (b3_crossings _ a b).Finite :=
  b3_crossings_finite b3_ellipticModel_finrank a b (b3_elliptic_transverse a b ha hb)

/-- **Intersection numbers are antisymmetric**: swapping the loops swaps the crossings and
reverses each orientation.
Source: Guillemin–Pollack, Ch. 3 §3 (`I(X, Z) = (-1)^{kl} I(Z, X)`, here `k = l = 1`). -/
theorem b3_intersection_antisymm [FiniteDimensional ℂ E] (γ δ : b3_SmoothLoop E C) :
    b3_intersection E δ γ = -b3_intersection E γ δ :=
  b3_intersection_antisymm_aux γ δ

example (γ : b3_SmoothLoop b3_EllipticModel b3_Elliptic) :
    b3_intersection _ γ γ = 0 := by
  have := b3_intersection_antisymm γ γ
  omega

/-- With antisymmetry, `b · a = -1`. -/
example (a b : b3_SmoothLoop b3_EllipticModel b3_Elliptic)
    (ha : a.1 = b3_ellipticA) (hb : b.1 = b3_ellipticB) :
    b3_intersection b3_EllipticModel b a = -1 := by
  rw [b3_intersection_antisymm, b3_elliptic_intersection a b ha hb]

/-- **Intersection numbers are bilinear in the periods**: there is a bilinear form on `Λ_C` whose
value on the periods of two transverse loops is their intersection number. Intersection numbers
of transverse loops depend only on their homology classes, and `Λ_C ≅ H₁(C, ℤ)`.
Source: Farkas–Kra, *Riemann Surfaces*, Ch. III (the intersection form on `H₁`); Guillemin–
Pollack, Ch. 3 §3 (homotopy invariance of intersection numbers). -/
theorem b3_exists_intersectionForm [FiniteDimensional ℂ E]
    [T2Space C] [CompactSpace C] [ConnectedSpace C] (hE : Module.finrank ℂ E = 1) :
    ∃ Q : LinearMap.BilinForm ℤ (b3_periodLattice E C), b3_IsIntersectionForm E Q :=
  b3_exists_intersectionForm_aux hE

example : ∃ Q : LinearMap.BilinForm ℤ (b3_periodLattice b3_EllipticModel b3_Elliptic),
    b3_IsIntersectionForm _ Q :=
  haveI := b3_elliptic_connectedSpace
  b3_exists_intersectionForm b3_ellipticModel_finrank

/-- Every intersection form of the elliptic curve has `Q(λ_a, λ_b) = 1`. -/
example (a b : b3_SmoothLoop b3_EllipticModel b3_Elliptic)
    (ha : a.1 = b3_ellipticA) (hb : b.1 = b3_ellipticB)
    (Q : LinearMap.BilinForm ℤ (b3_periodLattice b3_EllipticModel b3_Elliptic))
    (hQ : b3_IsIntersectionForm _ Q) :
    Q (b3_latticePeriod _ _ a) (b3_latticePeriod _ _ b) = 1 :=
  (hQ a b (b3_elliptic_transverse a b ha hb)).trans (b3_elliptic_intersection a b ha hb)

/-- **The intersection form is unique**: every pair of lattice periods is realized by transverse
loops (perturb one loop within its homotopy class), and the periods generate `Λ_C`.
Source: Guillemin–Pollack, Ch. 2 §3 (the transversality homotopy theorem). -/
theorem b3_intersectionForm_unique [FiniteDimensional ℂ E]
    [T2Space C] [CompactSpace C] [ConnectedSpace C] (hE : Module.finrank ℂ E = 1)
    (Q Q' : LinearMap.BilinForm ℤ (b3_periodLattice E C))
    (hQ : b3_IsIntersectionForm E Q) (hQ' : b3_IsIntersectionForm E Q') :
    Q = Q' :=
  b3_intersectionForm_unique_aux hE Q Q' hQ hQ'

/-- The opposite form `-Q` does not compute intersection numbers: by uniqueness it would equal
`Q`, but `Q(λ_a, λ_b) = a · b = 1`. -/
example (a b : b3_SmoothLoop b3_EllipticModel b3_Elliptic)
    (ha : a.1 = b3_ellipticA) (hb : b.1 = b3_ellipticB)
    (Q : LinearMap.BilinForm ℤ (b3_periodLattice b3_EllipticModel b3_Elliptic))
    (hQ : b3_IsIntersectionForm _ Q) : ¬ b3_IsIntersectionForm _ (-Q) := by
  have := b3_elliptic_connectedSpace
  intro hQ'
  have h := b3_intersectionForm_unique b3_ellipticModel_finrank Q (-Q) hQ hQ'
  have h1 := (hQ a b (b3_elliptic_transverse a b ha hb)).trans (b3_elliptic_intersection a b ha hb)
  have h2 := congrArg (fun R : LinearMap.BilinForm ℤ _ ↦
    R (b3_latticePeriod _ _ a) (b3_latticePeriod _ _ b)) h
  simp only [LinearMap.neg_apply, h1] at h2
  omega

/-- **The Riemann bilinear relations**: the intersection form is a Riemann form for the Jacobian
filtration: alternating, `F_C` isotropic, and `Re (i Q_ℂ(x, x̄)) > 0` on `F_C \ 0`. Under
Poincaré duality `F_C` is `H^{1,0}`, and the relations are `∫_C ω ∧ η = 0` and
`i ∫_C ω ∧ ω̄ > 0` for holomorphic `ω ≠ 0`, computed on a fundamental polygon.
Source: Griffiths–Harris, Ch. 2.2 (Riemann bilinear relations); Farkas–Kra, Ch. III;
Birkenhake–Lange, Ch. 11 (the canonical polarization of `J(C)`). -/
theorem b3_intersectionForm_isRiemannForm [FiniteDimensional ℂ E]
    [T2Space C] [CompactSpace C] [ConnectedSpace C] (hE : Module.finrank ℂ E = 1)
    (Q : LinearMap.BilinForm ℤ (b3_periodLattice E C)) (hQ : b3_IsIntersectionForm E Q) :
    b2_IsRiemannForm (b3_periodLattice E C) (b3_periodF E C) Q :=
  b3_intersectionForm_isRiemannForm_aux hE Q hQ

example (Q : LinearMap.BilinForm ℤ (b3_periodLattice b3_EllipticModel b3_Elliptic))
    (hQ : b3_IsIntersectionForm _ Q) (x : b3_periodLattice b3_EllipticModel b3_Elliptic) :
    Q x x = 0 :=
  haveI := b3_elliptic_connectedSpace
  (b3_intersectionForm_isRiemannForm b3_ellipticModel_finrank Q hQ).alt x

/-- **The polarization is principal**: the intersection form is unimodular, `Λ_C → Hom(Λ_C, ℤ)`
is bijective (Poincaré duality on a compact oriented surface).
Source: Farkas–Kra, Ch. III (a canonical homology basis has intersection matrix `[0 I; -I 0]`);
Birkenhake–Lange, Ch. 11 (the canonical polarization is principal); Hatcher, §3.3. -/
theorem b3_intersectionForm_bijective [FiniteDimensional ℂ E]
    [T2Space C] [CompactSpace C] [ConnectedSpace C] (hE : Module.finrank ℂ E = 1)
    (Q : LinearMap.BilinForm ℤ (b3_periodLattice E C)) (hQ : b3_IsIntersectionForm E Q) :
    Function.Bijective Q :=
  b3_intersectionForm_bijective_aux hE Q hQ

example (Q : LinearMap.BilinForm ℤ (b3_periodLattice b3_EllipticModel b3_Elliptic))
    (hQ : b3_IsIntersectionForm _ Q) : Function.Injective Q :=
  haveI := b3_elliptic_connectedSpace
  (b3_intersectionForm_bijective b3_ellipticModel_finrank Q hQ).1

/-! ## The Abel–Jacobi map -/

/-- **The Abel–Jacobi map exists**: integrate from `p₀` along a `C¹` path; two paths differ by a
loop up to homotopy, whose periods lie in `Λ_C`, and the integrals lie in `span_ℂ Λ_C`.
Source: Forster, *Lectures on Riemann Surfaces*, §21; Griffiths–Harris, Ch. 2.2. -/
theorem b3_exists_abelJacobi [T2Space C] [CompactSpace C] [ConnectedSpace C]
    (hE : Module.finrank ℂ E = 1) (p₀ : C) :
    ∃ aj : C → b3_Jacobian E C, b3_IsAbelJacobi E C p₀ aj :=
  b3_exists_abelJacobi_aux hE p₀

example : ∃ aj : b3_Elliptic → b3_Jacobian b3_EllipticModel b3_Elliptic,
    b3_IsAbelJacobi _ _ 0 aj :=
  haveI := b3_elliptic_connectedSpace
  b3_exists_abelJacobi b3_ellipticModel_finrank 0

/-- **The Abel–Jacobi map is unique**: a connected manifold is connected by `C¹` paths, and the
class of `v` is determined by its periods since `F_C` is the kernel.
Source: Lee, *Introduction to Smooth Manifolds*, Ch. 6 (connected manifolds are connected by
smooth paths); Forster, §21. -/
theorem b3_abelJacobi_unique [T2Space C] [CompactSpace C] [ConnectedSpace C]
    (hE : Module.finrank ℂ E = 1) (p₀ : C) (aj aj' : C → b3_Jacobian E C)
    (h : b3_IsAbelJacobi E C p₀ aj) (h' : b3_IsAbelJacobi E C p₀ aj') :
    aj = aj' :=
  b3_abelJacobi_unique_aux hE p₀ aj aj' h h'

/-- On the elliptic curve, the Abel–Jacobi map obtained from `b3_exists_abelJacobi` (an
existence statement) takes the explicit values of `b3_elliptic_abelJacobi_apply`, computed from
the Abel–Jacobi property of a second map `aj`. -/
example (a b : b3_SmoothLoop b3_EllipticModel b3_Elliptic)
    (ha : a.1 = b3_ellipticA) (hb : b.1 = b3_ellipticB)
    (aj : b3_Elliptic → b3_Jacobian b3_EllipticModel b3_Elliptic)
    (h : b3_IsAbelJacobi b3_EllipticModel b3_Elliptic 0 aj) (s t : ℝ) :
    ∃ aj₀ : b3_Elliptic → b3_Jacobian b3_EllipticModel b3_Elliptic,
      b3_IsAbelJacobi b3_EllipticModel b3_Elliptic 0 aj₀ ∧ aj₀ (b3_ellipticPoint s t) =
        QuotientAddGroup.mk (Submodule.Quotient.mk ((s : ℂ) ⊗ₜ[ℤ] b3_latticePeriod _ _ a +
          (t : ℂ) ⊗ₜ[ℤ] b3_latticePeriod _ _ b)) := by
  have := b3_elliptic_connectedSpace
  have h0 := b3_exists_abelJacobi (E := b3_EllipticModel) (C := b3_Elliptic)
    b3_ellipticModel_finrank (0 : b3_Elliptic)
  refine ⟨h0.choose, h0.choose_spec, ?_⟩
  have hu : h0.choose = aj := b3_abelJacobi_unique (E := b3_EllipticModel) (C := b3_Elliptic)
    b3_ellipticModel_finrank (0 : b3_Elliptic) _ aj h0.choose_spec h
  exact (congrFun hu _).trans (b3_elliptic_abelJacobi_apply a b ha hb aj h s t)

/-- **The Abel–Jacobi map is holomorphic** for the complex structure of B2's torus (whose charts
need the lattice to be finite and discrete, which `b3_periodLattice_finite`,
`b3_periodLattice_free`, `b3_isWeightOne` and B2's `b2_latticeMap_discrete` supply): locally it
is `z ↦ (∫_{z₀}^z θᵢ)ᵢ`.
Source: Forster, *Lectures on Riemann Surfaces*, §21; Griffiths–Harris, Ch. 2.2. -/
theorem b3_abelJacobi_holomorphic [T2Space C] [CompactSpace C] [ConnectedSpace C]
    (hE : Module.finrank ℂ E = 1) [Module.Finite ℤ (b3_periodLattice E C)]
    [DiscreteTopology (b2_latticeMap (b3_periodLattice E C) (b3_periodF E C)).range]
    (p₀ : C) (aj : C → b3_Jacobian E C) (h : b3_IsAbelJacobi E C p₀ aj) :
    ContMDiff 𝓘(ℂ, E)
      𝓘(ℂ, Fin (Module.finrank ℂ ((ℂ ⊗[ℤ] b3_periodLattice E C) ⧸ b3_periodF E C)) → ℂ) ω aj :=
  b3_abelJacobi_holomorphic_aux hE p₀ aj h

/-- The instance binders are supplied by the frozen statements and B2. -/
example [T2Space C] [CompactSpace C] [ConnectedSpace C] (hE : Module.finrank ℂ E = 1) (p₀ : C)
    (aj : C → b3_Jacobian E C) (h : b3_IsAbelJacobi E C p₀ aj) :
    haveI := b3_periodLattice_finite (E := E) (C := C) hE
    haveI := b3_periodLattice_free (E := E) (C := C)
    haveI := b2_latticeMap_discrete _ (b3_isWeightOne (E := E) (C := C) hE)
    ContMDiff 𝓘(ℂ, E)
      𝓘(ℂ, Fin (Module.finrank ℂ ((ℂ ⊗[ℤ] b3_periodLattice E C) ⧸ b3_periodF E C)) → ℂ) ω aj :=
  haveI := b3_periodLattice_finite (E := E) (C := C) hE
  haveI := b3_periodLattice_free (E := E) (C := C)
  haveI := b2_latticeMap_discrete _ (b3_isWeightOne (E := E) (C := C) hE)
  b3_abelJacobi_holomorphic hE p₀ aj h

/-! ## Functoriality -/

section Maps

variable {E' : Type} [NormedAddCommGroup E'] [NormedSpace ℂ E']
variable {C' : Type} [TopologicalSpace C'] [ChartedSpace E' C'] [IsManifold 𝓘(ℂ, E') ω C']

/-- **Holomorphic maps pull back holomorphic forms**: the tangent map of a holomorphic map is
holomorphic and fibrewise `ℂ`-linear.
Source: Forster, *Lectures on Riemann Surfaces*, §9; Mathlib `ContMDiff.contMDiff_tangentMap`. -/
theorem b3_pullback_mem_holForm (f : C → C') (hf : ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, E') ω f)
    (θ : TangentBundle 𝓘(ℂ, E') C' → ℂ) (hθ : θ ∈ b3_HolForm E' C') :
    b3_pullback E E' f θ ∈ b3_HolForm E C :=
  b3_pullback_mem_holForm_aux f hf θ hθ

example : b3_pullback b3_EllipticModel b3_EllipticModel (id : b3_Elliptic → b3_Elliptic) 0 ∈
    b3_HolForm b3_EllipticModel b3_Elliptic :=
  b3_pullback_mem_holForm id contMDiff_id 0 (b3_HolForm _ _).zero_mem

/-- **The chain rule for path integrals**: `∫_{f ∘ γ} θ = ∫_γ f^* θ` for a holomorphic `f` and a
`C¹` path `γ`.
Source: Forster, *Lectures on Riemann Surfaces*, §9–§10; Mathlib `mfderiv_comp`. -/
theorem b3_pathIntegral_comp (f : C → C') (hf : ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, E') ω f)
    (γ : ℝ → C) (hγ : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) 1 γ) (θ : TangentBundle 𝓘(ℂ, E') C' → ℂ) :
    b3_pathIntegral E' C' (f ∘ γ) θ = b3_pathIntegral E C γ (b3_pullback E E' f θ) :=
  b3_pathIntegral_comp_aux f hf γ hγ θ

example (x : b3_Elliptic) (θ : TangentBundle 𝓘(ℂ, b3_EllipticModel) b3_Elliptic → ℂ) :
    b3_pathIntegral b3_EllipticModel b3_Elliptic (id ∘ fun _ : ℝ ↦ x) θ =
      b3_pathIntegral b3_EllipticModel b3_Elliptic (fun _ : ℝ ↦ x)
        (b3_pullback b3_EllipticModel b3_EllipticModel id θ) :=
  b3_pathIntegral_comp id contMDiff_id _ contMDiff_const θ

/-- **The pushforward of period lattices exists**: `λ ↦ λ ∘ f^*` sends the period of `γ` to the
period of `f ∘ γ` (chain rule), and its complexification maps `F_C` into `F_C'`; so
`J(f)_* = b2_torusHom F_C F_C' g` is a morphism of B2 tori.
Source: Birkenhake–Lange, Ch. 11 (`f_* : J(C) → J(C')`); Griffiths–Harris, Ch. 2.2. -/
theorem b3_exists_pushforward (f : C → C') (hf : ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, E') ω f) :
    ∃ g : b3_periodLattice E C →+ b3_periodLattice E' C', b3_IsPushforward E E' f g ∧
      b3_periodF E C ≤ (b3_periodF E' C').comap (b2_cplxMap g) :=
  b3_exists_pushforward_aux f hf

example : ∃ g : b3_periodLattice b3_EllipticModel b3_Elliptic →+
      b3_periodLattice b3_EllipticModel b3_Elliptic,
    b3_IsPushforward _ _ id g ∧ b3_periodF _ _ ≤ (b3_periodF _ _).comap (b2_cplxMap g) :=
  b3_exists_pushforward id contMDiff_id

/-- **The pushforward is unique**: the periods of loops generate `Λ_C`, and `f ∘ γ` is a `C¹`
loop. In particular `id_* = id` and `(f' ∘ f)_* = f'_* ∘ f_*`.
Source: Birkenhake–Lange, Ch. 11. -/
theorem b3_pushforward_unique (f : C → C') (hf : ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, E') ω f)
    (g g' : b3_periodLattice E C →+ b3_periodLattice E' C')
    (hg : b3_IsPushforward E E' f g) (hg' : b3_IsPushforward E E' f g') :
    g = g' :=
  b3_pushforward_unique_aux f hf g g' hg hg'

example (g : b3_periodLattice b3_EllipticModel b3_Elliptic →+
      b3_periodLattice b3_EllipticModel b3_Elliptic)
    (hg : b3_IsPushforward _ _ id g) : g = AddMonoidHom.id _ :=
  b3_pushforward_unique id contMDiff_id g _ hg fun γ γ' h ↦ by
    cases γ; cases γ'; cases h; rfl

/-- **The pullback of period lattices exists**: `f^* : Λ_C' → Λ_C` is the adjoint of `f_*` for
the intersection forms (which exists since `Q_C` is unimodular), and its complexification maps
`F_C'` into `F_C` (since `F_C` is Lagrangian for `Q_C` and `F_C'` is isotropic for `Q_C'`); so
`J(f)^* = b2_torusHom F_C' F_C h` is a morphism of B2 tori.
Source: Birkenhake–Lange, Ch. 11 (`f^* = φ⁻¹ ∘ (f_*)^∨ ∘ φ'` for the canonical polarizations);
Griffiths–Harris, Ch. 2.2. -/
theorem b3_exists_pullbackLattice [FiniteDimensional ℂ E] [FiniteDimensional ℂ E']
    [T2Space C] [CompactSpace C] [ConnectedSpace C] (hE : Module.finrank ℂ E = 1)
    [T2Space C'] [CompactSpace C'] [ConnectedSpace C'] (hE' : Module.finrank ℂ E' = 1)
    (f : C → C') (hf : ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, E') ω f)
    (g : b3_periodLattice E C →+ b3_periodLattice E' C') (hg : b3_IsPushforward E E' f g)
    (Q : LinearMap.BilinForm ℤ (b3_periodLattice E C)) (hQ : b3_IsIntersectionForm E Q)
    (Q' : LinearMap.BilinForm ℤ (b3_periodLattice E' C')) (hQ' : b3_IsIntersectionForm E' Q') :
    ∃ h : b3_periodLattice E' C' →+ b3_periodLattice E C,
      (∀ a b, Q (h a) b = Q' a (g b)) ∧
        b3_periodF E' C' ≤ (b3_periodF E C).comap (b2_cplxMap h) :=
  b3_exists_pullbackLattice_aux hE hE' f hf g hg Q hQ Q' hQ'

example (g : b3_periodLattice b3_EllipticModel b3_Elliptic →+
      b3_periodLattice b3_EllipticModel b3_Elliptic)
    (hg : b3_IsPushforward _ _ id g)
    (Q : LinearMap.BilinForm ℤ (b3_periodLattice b3_EllipticModel b3_Elliptic))
    (hQ : b3_IsIntersectionForm _ Q) :
    ∃ h : b3_periodLattice b3_EllipticModel b3_Elliptic →+
        b3_periodLattice b3_EllipticModel b3_Elliptic,
      (∀ a b, Q (h a) b = Q a (g b)) ∧ b3_periodF _ _ ≤ (b3_periodF _ _).comap (b2_cplxMap h) :=
  haveI := b3_elliptic_connectedSpace
  b3_exists_pullbackLattice b3_ellipticModel_finrank b3_ellipticModel_finrank id contMDiff_id
    g hg Q hQ Q hQ

/-- **The Abel–Jacobi maps are natural**: `AJ_{C'}(f p) = J(f)_*(AJ_C(p))` for base points `p₀`
and `f p₀`.
Source: Birkenhake–Lange, Ch. 11 (the universal property of the Abel–Jacobi map); Griffiths–Harris,
Ch. 2.2. -/
theorem b3_abelJacobi_natural
    [T2Space C] [CompactSpace C] [ConnectedSpace C] (hE : Module.finrank ℂ E = 1)
    [T2Space C'] [CompactSpace C'] [ConnectedSpace C'] (hE' : Module.finrank ℂ E' = 1)
    (f : C → C') (hf : ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, E') ω f)
    (g : b3_periodLattice E C →+ b3_periodLattice E' C') (hg : b3_IsPushforward E E' f g)
    (hgF : b3_periodF E C ≤ (b3_periodF E' C').comap (b2_cplxMap g))
    (p₀ : C) (aj : C → b3_Jacobian E C) (haj : b3_IsAbelJacobi E C p₀ aj)
    (aj' : C' → b3_Jacobian E' C') (haj' : b3_IsAbelJacobi E' C' (f p₀) aj') (p : C) :
    aj' (f p) = b2_torusHom (b3_periodF E C) (b3_periodF E' C') g hgF (aj p) :=
  b3_abelJacobi_natural_aux hE hE' f hf g hg hgF p₀ aj haj aj' haj' p

end Maps

/-! ## The elliptic curve: `J = C` -/

/-- **The Abel–Jacobi map of the elliptic curve is bijective** (`J = C`): with base point `0` it
is the inverse of the identification `ℂ ⧸ Λ ≅ C`, since `∫₀^z dz = z`.
Source: Forster, *Lectures on Riemann Surfaces*, §20–§21 (Abel's theorem and Jacobi inversion);
Birkenhake–Lange, §1.1 and Ch. 11. -/
theorem b3_elliptic_abelJacobi_bijective
    (aj : b3_Elliptic → b3_Jacobian b3_EllipticModel b3_Elliptic)
    (h : b3_IsAbelJacobi b3_EllipticModel b3_Elliptic 0 aj) :
    Function.Bijective aj :=
  b3_elliptic_abelJacobi_bijective_aux aj h

example : ∃ aj : b3_Elliptic → b3_Jacobian b3_EllipticModel b3_Elliptic, Function.Bijective aj :=
  haveI := b3_elliptic_connectedSpace
  let ⟨aj, h⟩ := b3_exists_abelJacobi b3_ellipticModel_finrank (0 : b3_Elliptic)
  ⟨aj, b3_elliptic_abelJacobi_bijective aj h⟩

end HodgeLean.Foundations.Program
