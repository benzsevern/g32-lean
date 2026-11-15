import HodgeLean.Foundations.Program.PrymFamilyCentreProofs

/-! # B6-3g, parts 2 and 3: the centre on the transported lattice, `hodge` and Weil type
(FROZEN SPEC)

Each public theorem is the matching `_aux` theorem of `PrymFamilyCentreProofs.lean`.

**Claimed.** Part 2: on the saturated singular lattice `Λ_s` of the actual moving fibre, the
central deck operator `b63g2_centre` is an isometry of the original intersection form pulled back
by the period comparison, the operator `b63g2_operator = 1 + 2ω` is skew for that form, and its
complexification preserves the transported filtration `b63e_transportedF … s t` for every pair
of parameters. With `b63g2_operator_sq` (`(1 + 2ω)² = -3`, which has a body) these are exactly
the hypotheses of the part 1 transport statements, so the B5 marking carries them to the model,
and part 1's rationalization and dualization give the fields `W` and `rosati` on the actual
fibres. Part 3: for B5 data with an operator `φ`, `φ² = -n`, `n > 0`, preserving `F`, the two
Hodge numbers of the `i√n`-eigenspace of the Weil action are the dimensions of
`F ∩ ker(φ_ℂ ∓ i√n)`; on the actual fibre both of these have dimension three. Together they give
`g32h_h10 = 3`, `g32h_h01 = 3`, Weil type and the field `hodge` of `g32h_PrymFamily` in both
orders (examples at the end of the file).

These are implications from the marked moving fibres with holomorphic deck actions, integral
period comparisons, intersection forms and, for the ranks, the Chevalley–Weil data of B6-3d.

**Not claimed.** Positivity `PolarizationPositive` (part 4, the field `positive`); the marked
assembly of `g32h_PrymFamily` with `S := V` and the marked Nielsen tuples (part 5); the rational
`d1_PolarizedVHS` (part 6). Nothing here concerns a discriminant, algebraicity of Weil classes or
dominance. HC no distance; AV milestone no distance.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint AlgebraicTopology.Singular
open HodgeLean.RealDefs HodgeLean.Adapters HodgeLean.Foundations
open HodgeLean.Foundations.Symplectic HodgeLean.Foundations.AppellHumbert HodgeLean.Papers
open scoped TensorProduct Manifold ContDiff

namespace HodgeLean.Foundations.Program
attribute [local instance] b4cov_sphChartedSpace b4cov_sph_isManifold

/-! ## Part 2: the centre on the saturated lattice -/

/-- **The central deck operator is an isometry of the original form** on the saturated lattice
`Λ_s`: `Q (P (c x)) (P (c y)) = Q (P x) (P y)` for `c = b63g2_centre`. The comparison `P` with
`P [γ] = ∫_γ` carries `g_*` to the pushforward `b4_latticeAct g` (naturality of loop classes and
periods), and a biholomorphism preserves the intersection form (`b4_intersectionForm_invariant`).
Source: Farkas–Kra, *Riemann Surfaces*, Ch. III (intersection numbers are invariant under
orientation-preserving homeomorphisms); Birkenhake–Lange, §11.4; `b4_intersectionForm_invariant`. -/
theorem b63g2_centre_isometry (b : Fin 10 → ℂ) (C : Type) [TopologicalSpace C]
    [MulAction b4b_Group C]
    (hC : ∀ g : b4b_Group, Continuous (fun x : C ↦ g • x))
    (V : Set (Fin 10 → ℂ)) (hV : V ⊆ b6t_polydisc b) (s : V)
    [ChartedSpace ℂ (b63l_parameterFibre b C V hV s)]
    [IsManifold 𝓘(ℂ, ℂ) ω (b63l_parameterFibre b C V hV s)]
    [T2Space (b63l_parameterFibre b C V hV s)] [CompactSpace (b63l_parameterFibre b C V hV s)]
    [ConnectedSpace (b63l_parameterFibre b C V hV s)]
    (hG : ∀ g : b4b_Group, ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω
      (fun x : b63l_parameterFibre b C V hV s ↦ g • x))
    (Ps : b6m_H1 (b63l_parameterFibre b C V hV s) →ₗ[ℤ]
      b3_periodLattice ℂ (b63l_parameterFibre b C V hV s))
    (hP : ∀ γ : b3_SmoothLoop ℂ (b63l_parameterFibre b C V hV s),
      Ps (b6m_loopClass _ γ) = b3_latticePeriod ℂ _ γ)
    (Q : LinearMap.BilinForm ℤ (b3_periodLattice ℂ (b63l_parameterFibre b C V hV s)))
    (hQ : b3_IsIntersectionForm ℂ Q)
    (x y : b63l_parameterLattice b C hC V hV s) :
    b63e_singularQ b C hC V hV s Ps Q (b63g2_centre b C hC V hV s x)
        (b63g2_centre b C hC V hV s y) =
      b63e_singularQ b C hC V hV s Ps Q x y :=
  b63g2_centre_isometry_aux b C hC V hV s hG Ps hP Q hQ x y

example (b : Fin 10 → ℂ) (C : Type) [TopologicalSpace C]
    [MulAction b4b_Group C]
    (hC : ∀ g : b4b_Group, Continuous (fun x : C ↦ g • x))
    (V : Set (Fin 10 → ℂ)) (hV : V ⊆ b6t_polydisc b) (s : V)
    [ChartedSpace ℂ (b63l_parameterFibre b C V hV s)]
    [IsManifold 𝓘(ℂ, ℂ) ω (b63l_parameterFibre b C V hV s)]
    [T2Space (b63l_parameterFibre b C V hV s)] [CompactSpace (b63l_parameterFibre b C V hV s)]
    [ConnectedSpace (b63l_parameterFibre b C V hV s)]
    (hG : ∀ g : b4b_Group, ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω
      (fun x : b63l_parameterFibre b C V hV s ↦ g • x))
    (Ps : b6m_H1 (b63l_parameterFibre b C V hV s) →ₗ[ℤ]
      b3_periodLattice ℂ (b63l_parameterFibre b C V hV s))
    (hP : ∀ γ : b3_SmoothLoop ℂ (b63l_parameterFibre b C V hV s),
      Ps (b6m_loopClass _ γ) = b3_latticePeriod ℂ _ γ)
    (Q : LinearMap.BilinForm ℤ (b3_periodLattice ℂ (b63l_parameterFibre b C V hV s)))
    (hQ : b3_IsIntersectionForm ℂ Q)
    (x y : b63l_parameterLattice b C hC V hV s) :
    b63e_singularQ b C hC V hV s Ps Q (b63g2_centre b C hC V hV s x)
        (b63g2_centre b C hC V hV s y) =
      b63e_singularQ b C hC V hV s Ps Q x y :=
  b63g2_centre_isometry b C hC V hV s hG Ps hP Q hQ x y

/-- **`1 + 2ω` is skew for the original form** on the saturated lattice: with `c` an isometry
(`b63g2_centre_isometry`) and `c² + c + 1 = 0` on `Λ_s` (equivalent to `(1 + 2c)² = -3`,
`b63g2_operator_sq`, on a torsion-free group), `c⁻¹ = c²= -1 - c`, so
`Q(cx, y) = Q(x, c⁻¹y) = -Q(x, y) - Q(x, cy)` and `Q((1 + 2c)x, y) = -Q(x, (1 + 2c)y)`. This is
the hypothesis `hskew` of `b63g_modelForm_skew` for the actual operator.
Source: G32 v0.16, §3.3 and Lemma 3.3 (`ι(K)` is Rosati-stable acting by complex conjugation);
Birkenhake–Lange, §5.1 and §12.2. -/
theorem b63g2_operator_skew (b : Fin 10 → ℂ) (C : Type) [TopologicalSpace C]
    [MulAction b4b_Group C]
    (hC : ∀ g : b4b_Group, Continuous (fun x : C ↦ g • x))
    (V : Set (Fin 10 → ℂ)) (hV : V ⊆ b6t_polydisc b) (s : V)
    [ChartedSpace ℂ (b63l_parameterFibre b C V hV s)]
    [IsManifold 𝓘(ℂ, ℂ) ω (b63l_parameterFibre b C V hV s)]
    [T2Space (b63l_parameterFibre b C V hV s)] [CompactSpace (b63l_parameterFibre b C V hV s)]
    [ConnectedSpace (b63l_parameterFibre b C V hV s)]
    (hG : ∀ g : b4b_Group, ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω
      (fun x : b63l_parameterFibre b C V hV s ↦ g • x))
    (Ps : b6m_H1 (b63l_parameterFibre b C V hV s) →ₗ[ℤ]
      b3_periodLattice ℂ (b63l_parameterFibre b C V hV s))
    (hP : ∀ γ : b3_SmoothLoop ℂ (b63l_parameterFibre b C V hV s),
      Ps (b6m_loopClass _ γ) = b3_latticePeriod ℂ _ γ)
    (Q : LinearMap.BilinForm ℤ (b3_periodLattice ℂ (b63l_parameterFibre b C V hV s)))
    (hQ : b3_IsIntersectionForm ℂ Q) :
    ∀ x y, b63e_singularQ b C hC V hV s Ps Q (b63g2_operator b C hC V hV s x) y =
      -b63e_singularQ b C hC V hV s Ps Q x (b63g2_operator b C hC V hV s y) :=
  b63g2_operator_skew_aux b C hC V hV s hG Ps hP Q hQ

example (b : Fin 10 → ℂ) (C : Type) [TopologicalSpace C]
    [MulAction b4b_Group C]
    (hC : ∀ g : b4b_Group, Continuous (fun x : C ↦ g • x))
    (V : Set (Fin 10 → ℂ)) (hV : V ⊆ b6t_polydisc b) (s : V)
    [ChartedSpace ℂ (b63l_parameterFibre b C V hV s)]
    [IsManifold 𝓘(ℂ, ℂ) ω (b63l_parameterFibre b C V hV s)]
    [T2Space (b63l_parameterFibre b C V hV s)] [CompactSpace (b63l_parameterFibre b C V hV s)]
    [ConnectedSpace (b63l_parameterFibre b C V hV s)]
    (hG : ∀ g : b4b_Group, ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω
      (fun x : b63l_parameterFibre b C V hV s ↦ g • x))
    (Ps : b6m_H1 (b63l_parameterFibre b C V hV s) →ₗ[ℤ]
      b3_periodLattice ℂ (b63l_parameterFibre b C V hV s))
    (hP : ∀ γ : b3_SmoothLoop ℂ (b63l_parameterFibre b C V hV s),
      Ps (b6m_loopClass _ γ) = b3_latticePeriod ℂ _ γ)
    (Q : LinearMap.BilinForm ℤ (b3_periodLattice ℂ (b63l_parameterFibre b C V hV s)))
    (hQ : b3_IsIntersectionForm ℂ Q) :
    ∀ x y, b63e_singularQ b C hC V hV s Ps Q (b63g2_operator b C hC V hV s x) y =
      -b63e_singularQ b C hC V hV s Ps Q x (b63g2_operator b C hC V hV s y) :=
  b63g2_operator_skew b C hC V hV s hG Ps hP Q hQ

/-- **`1 + 2ω` preserves every transported filtration.** For all parameters `s` and `t`, the
complexification of the operator on `Λ_s` preserves `b63e_transportedF … s t`, the period
filtration of the fibre at `t` pulled back along transport and periods. Transport commutes with
the centre (`b63d_centre_transport`), the comparison `P t` carries `g_*` to the pushforward
`b4_latticeAct g`, and the kernel of the complex period map is stable under biholomorphisms. This
is the hypothesis `hφ` of `b63g_modelMap_filtration` for the actual operator and filtration.
Source: G32 v0.16, §3.2–3.3; Birkenhake–Lange, §1.2 and §12.2; `b63d_centre_transport`,
`b63d_prymOperator_filtration`, `b63e_lattice_period_transport`. -/
theorem b63g2_operator_filtration (b : Fin 10 → ℂ) (C : Type) [TopologicalSpace C]
    [MulAction b4b_Group C]
    (hC : ∀ g : b4b_Group, Continuous (fun x : C ↦ g • x))
    (V : Set (Fin 10 → ℂ)) (hV : V ⊆ b6t_polydisc b)
    [∀ t : V, ChartedSpace ℂ (b63l_parameterFibre b C V hV t)]
    [∀ t : V, IsManifold 𝓘(ℂ, ℂ) ω (b63l_parameterFibre b C V hV t)]
    [∀ t : V, T2Space (b63l_parameterFibre b C V hV t)]
    [∀ t : V, CompactSpace (b63l_parameterFibre b C V hV t)]
    [∀ t : V, ConnectedSpace (b63l_parameterFibre b C V hV t)]
    (hG : ∀ (t : V) (g : b4b_Group), ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω
      (fun x : b63l_parameterFibre b C V hV t ↦ g • x))
    (P : (t : V) → b6m_H1 (b63l_parameterFibre b C V hV t) →ₗ[ℤ]
      b3_periodLattice ℂ (b63l_parameterFibre b C V hV t))
    (hP : ∀ (t : V) (γ : b3_SmoothLoop ℂ (b63l_parameterFibre b C V hV t)),
      P t (b6m_loopClass _ γ) = b3_latticePeriod ℂ _ γ)
    (s t : V) :
    b63e_transportedF b C hC V hV P s t ≤ (b63e_transportedF b C hC V hV P s t).comap
      (b2_cplxMap (b63g2_operator b C hC V hV s).toAddMonoidHom) :=
  b63g2_operator_filtration_aux b C hC V hV hG P hP s t

example (b : Fin 10 → ℂ) (C : Type) [TopologicalSpace C]
    [MulAction b4b_Group C]
    (hC : ∀ g : b4b_Group, Continuous (fun x : C ↦ g • x))
    (V : Set (Fin 10 → ℂ)) (hV : V ⊆ b6t_polydisc b)
    [∀ t : V, ChartedSpace ℂ (b63l_parameterFibre b C V hV t)]
    [∀ t : V, IsManifold 𝓘(ℂ, ℂ) ω (b63l_parameterFibre b C V hV t)]
    [∀ t : V, T2Space (b63l_parameterFibre b C V hV t)]
    [∀ t : V, CompactSpace (b63l_parameterFibre b C V hV t)]
    [∀ t : V, ConnectedSpace (b63l_parameterFibre b C V hV t)]
    (hG : ∀ (t : V) (g : b4b_Group), ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω
      (fun x : b63l_parameterFibre b C V hV t ↦ g • x))
    (P : (t : V) → b6m_H1 (b63l_parameterFibre b C V hV t) →ₗ[ℤ]
      b3_periodLattice ℂ (b63l_parameterFibre b C V hV t))
    (hP : ∀ (t : V) (γ : b3_SmoothLoop ℂ (b63l_parameterFibre b C V hV t)),
      P t (b6m_loopClass _ γ) = b3_latticePeriod ℂ _ γ)
    (s t : V) :
    b63e_transportedF b C hC V hV P s t ≤ (b63e_transportedF b C hC V hV P s t).comap
      (b2_cplxMap (b63g2_operator b C hC V hV s).toAddMonoidHom) :=
  b63g2_operator_filtration b C hC V hV hG P hP s t

/-! ## Part 3: the Hodge numbers of the Weil eigenspace -/

/-- **The `(1,0)` Hodge number of the Weil eigenspace, from lattice data.** For B5 data and a lattice
endomorphism `φ` with `φ² = -n`, `n > 0`, preserving `F`, the `i√n`-eigenspace `V_s` of the
Weil action `b63g2_weilAction` meets `H^{1,0}` of the model in the dimension of
`F ∩ ker(φ_ℂ + i√n)`. `J` is the transpose of `φ` under `H¹_ℂ = Hom(Λ, ℂ)`, so `V_s` is the
annihilator of `E₋ = ker(φ_ℂ + i√n)`; `H^{1,0}` is the annihilator of the model's filtration
(`b2_abelianHodgeF_eq`), which is the image of `F` under the marking (`b5_period_filtration`);
`E₋` and `F` have dimension `rank / 2`, so `V_s ∩ H^{1,0} = (E₋ + F)^⊥` has dimension
`dim (F ∩ E₋)`.
Source: Birkenhake–Lange, §1.2, Theorem 1.4.1 and §5.5 (the type `(r, s)` of an action of an
imaginary quadratic field); `b2_abelianHodgeF_eq`, `b5_period_filtration`. -/
theorem b63g2_weil_h10 (Λ : Type) [AddCommGroup Λ] [Module.Finite ℤ Λ] [Module.Free ℤ Λ]
    (F : Submodule ℂ (ℂ ⊗[ℤ] Λ)) (hF : b2_IsWeightOne Λ F)
    (Q : LinearMap.BilinForm ℤ Λ) (hQ : b2_IsRiemannForm Λ F Q) (n : ℤ) (hn : 0 < n)
    (φ : Λ →+ Λ) (hsq : ∀ l, φ (φ l) = (-n) • l) (hφ : F ≤ F.comap (b2_cplxMap φ)) :
    letI := b5_groupObj Λ F hF Q hQ
    letI : IsIntegral (b5_model Λ F hF Q).left := b5_integral_aux Λ F hF Q hQ
    letI := b5_smooth_aux Λ F hF Q hQ
    letI := b5_projective_aux Λ F hF Q hQ
    letI := (torusCohomology_cupProductOf (b5_model Λ F hF Q)).finite
    Module.finrank ℂ ↥((b63g2_weilAction Λ F hF Q hQ n φ hsq hφ).Vs ⊓
        (abelianVarietyCohomologyOf (finiteBetti_abelian (b5_model Λ F hF Q))
          (spec_bettiDeRhamIso_abelian (b5_model Λ F hF Q))
          (hodgeDecomposition_of_abelian (b5_model Λ F hF Q))
          (torusCohomology_cupProductOf (b5_model Λ F hF Q))).weight1.H (1, 0)) =
      Module.finrank ℂ ↥(F ⊓
        Module.End.eigenspace (b2_cplxMap φ) (-HodgeBlocks.WeilAction.omegaC (n : ℚ))) :=
  b63g2_weil_h10_aux Λ F hF Q hQ n hn φ hsq hφ

example (Λ : Type) [AddCommGroup Λ] [Module.Finite ℤ Λ] [Module.Free ℤ Λ]
    (F : Submodule ℂ (ℂ ⊗[ℤ] Λ)) (hF : b2_IsWeightOne Λ F)
    (Q : LinearMap.BilinForm ℤ Λ) (hQ : b2_IsRiemannForm Λ F Q) (n : ℤ) (hn : 0 < n)
    (φ : Λ →+ Λ) (hsq : ∀ l, φ (φ l) = (-n) • l) (hφ : F ≤ F.comap (b2_cplxMap φ)) :
    letI := b5_groupObj Λ F hF Q hQ
    letI : IsIntegral (b5_model Λ F hF Q).left := b5_integral_aux Λ F hF Q hQ
    letI := b5_smooth_aux Λ F hF Q hQ
    letI := b5_projective_aux Λ F hF Q hQ
    letI := (torusCohomology_cupProductOf (b5_model Λ F hF Q)).finite
    Module.finrank ℂ ↥((b63g2_weilAction Λ F hF Q hQ n φ hsq hφ).Vs ⊓
        (abelianVarietyCohomologyOf (finiteBetti_abelian (b5_model Λ F hF Q))
          (spec_bettiDeRhamIso_abelian (b5_model Λ F hF Q))
          (hodgeDecomposition_of_abelian (b5_model Λ F hF Q))
          (torusCohomology_cupProductOf (b5_model Λ F hF Q))).weight1.H (1, 0)) =
      Module.finrank ℂ ↥(F ⊓
        Module.End.eigenspace (b2_cplxMap φ) (-HodgeBlocks.WeilAction.omegaC (n : ℚ))) :=
  b63g2_weil_h10 Λ F hF Q hQ n hn φ hsq hφ

/-- **The `(0,1)` Hodge number of the Weil eigenspace, from lattice data.** Under the hypotheses of
`b63g2_weil_h10`, `V_s` meets `H^{0,1}` of the model in the dimension of `F ∩ ker(φ_ℂ - i√n)`:
`H^{0,1}` is the conjugate of `H^{1,0}`, the annihilator of `F̄`, and conjugation exchanges the
two eigenspaces of the rational `φ`, so `dim (F̄ ∩ E₋) = dim (F ∩ E₊)`.
Source: Birkenhake–Lange, §1.2, Theorem 1.4.1 and §5.5; `b2_abelianHodgeF_eq`,
`b5_period_filtration`. -/
theorem b63g2_weil_h01 (Λ : Type) [AddCommGroup Λ] [Module.Finite ℤ Λ] [Module.Free ℤ Λ]
    (F : Submodule ℂ (ℂ ⊗[ℤ] Λ)) (hF : b2_IsWeightOne Λ F)
    (Q : LinearMap.BilinForm ℤ Λ) (hQ : b2_IsRiemannForm Λ F Q) (n : ℤ) (hn : 0 < n)
    (φ : Λ →+ Λ) (hsq : ∀ l, φ (φ l) = (-n) • l) (hφ : F ≤ F.comap (b2_cplxMap φ)) :
    letI := b5_groupObj Λ F hF Q hQ
    letI : IsIntegral (b5_model Λ F hF Q).left := b5_integral_aux Λ F hF Q hQ
    letI := b5_smooth_aux Λ F hF Q hQ
    letI := b5_projective_aux Λ F hF Q hQ
    letI := (torusCohomology_cupProductOf (b5_model Λ F hF Q)).finite
    Module.finrank ℂ ↥((b63g2_weilAction Λ F hF Q hQ n φ hsq hφ).Vs ⊓
        (abelianVarietyCohomologyOf (finiteBetti_abelian (b5_model Λ F hF Q))
          (spec_bettiDeRhamIso_abelian (b5_model Λ F hF Q))
          (hodgeDecomposition_of_abelian (b5_model Λ F hF Q))
          (torusCohomology_cupProductOf (b5_model Λ F hF Q))).weight1.H (0, 1)) =
      Module.finrank ℂ ↥(F ⊓
        Module.End.eigenspace (b2_cplxMap φ) (HodgeBlocks.WeilAction.omegaC (n : ℚ))) :=
  b63g2_weil_h01_aux Λ F hF Q hQ n hn φ hsq hφ

example (Λ : Type) [AddCommGroup Λ] [Module.Finite ℤ Λ] [Module.Free ℤ Λ]
    (F : Submodule ℂ (ℂ ⊗[ℤ] Λ)) (hF : b2_IsWeightOne Λ F)
    (Q : LinearMap.BilinForm ℤ Λ) (hQ : b2_IsRiemannForm Λ F Q) (n : ℤ) (hn : 0 < n)
    (φ : Λ →+ Λ) (hsq : ∀ l, φ (φ l) = (-n) • l) (hφ : F ≤ F.comap (b2_cplxMap φ)) :
    letI := b5_groupObj Λ F hF Q hQ
    letI : IsIntegral (b5_model Λ F hF Q).left := b5_integral_aux Λ F hF Q hQ
    letI := b5_smooth_aux Λ F hF Q hQ
    letI := b5_projective_aux Λ F hF Q hQ
    letI := (torusCohomology_cupProductOf (b5_model Λ F hF Q)).finite
    Module.finrank ℂ ↥((b63g2_weilAction Λ F hF Q hQ n φ hsq hφ).Vs ⊓
        (abelianVarietyCohomologyOf (finiteBetti_abelian (b5_model Λ F hF Q))
          (spec_bettiDeRhamIso_abelian (b5_model Λ F hF Q))
          (hodgeDecomposition_of_abelian (b5_model Λ F hF Q))
          (torusCohomology_cupProductOf (b5_model Λ F hF Q))).weight1.H (0, 1)) =
      Module.finrank ℂ ↥(F ⊓
        Module.End.eigenspace (b2_cplxMap φ) (HodgeBlocks.WeilAction.omegaC (n : ℚ))) :=
  b63g2_weil_h01 Λ F hF Q hQ n hn φ hsq hφ

/-- **Both eigenpieces of the transported filtration have rank three.** For all parameters `s` and
`t`, with the Chevalley–Weil data at `t`, the transported filtration `b63e_transportedF … s t`
meets each of the `±i√3`-eigenspaces of the complexified operator on `Λ_s` in dimension three.
`1 + 2ω = i√3`, so the `i√3`-eigenspace of `1 + 2c` is the `ω`-eigenspace of `c`; the
comparison `E` of `b63e_lattice_period_transport` carries `F ∩ ker(c - ω)` and
`F ∩ ker(c - ω̄)` to the two central eigenparts `b63d_eigenF` of the period filtration at `t`
(possibly exchanged, if the pushforward and the homology action differ by inversion), and both
have rank three by `b63d_chevalleyWeil_hodge`.
Source: G32 v0.16, Proposition 3.1 and Lemma 3.3; Frediani–Ghigi–Penegini, IMRN 2015,
Theorem 2.10; `b63d_chevalleyWeil_hodge`, `b63e_lattice_period_transport`,
`b63d_centre_transport`. -/
theorem b63g2_eigen_rank (b : Fin 10 → ℂ) (C : Type) [TopologicalSpace C]
    [MulAction b4b_Group C]
    (hC : ∀ g : b4b_Group, Continuous (fun x : C ↦ g • x))
    (V : Set (Fin 10 → ℂ)) (hV : V ⊆ b6t_polydisc b)
    [∀ t : V, ChartedSpace ℂ (b63l_parameterFibre b C V hV t)]
    [∀ t : V, IsManifold 𝓘(ℂ, ℂ) ω (b63l_parameterFibre b C V hV t)]
    [∀ t : V, T2Space (b63l_parameterFibre b C V hV t)]
    [∀ t : V, CompactSpace (b63l_parameterFibre b C V hV t)]
    [∀ t : V, ConnectedSpace (b63l_parameterFibre b C V hV t)]
    (hG : ∀ (t : V) (g : b4b_Group), ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω
      (fun x : b63l_parameterFibre b C V hV t ↦ g • x))
    (P : (t : V) → b6m_H1 (b63l_parameterFibre b C V hV t) →ₗ[ℤ]
      b3_periodLattice ℂ (b63l_parameterFibre b C V hV t))
    (hP : ∀ (t : V) (γ : b3_SmoothLoop ℂ (b63l_parameterFibre b C V hV t)),
      P t (b6m_loopClass _ γ) = b3_latticePeriod ℂ _ γ)
    (s t : V)
    [FaithfulSMul b4b_Group (b63l_parameterFibre b C V hV t)]
    (hb : b ∈ b6_chart) (f : C → OnePoint ℂ)
    (hf : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω (b63d_projection b C f V hV t))
    (hs : Function.Surjective (b63d_projection b C f V hV t))
    (hgal : b4_IsGaloisCover b4b_Group (b63d_projection b C f V hV t))
    (hbranch : b4_branchSet ℂ ℂ (b63d_projection b C f V hV t) = Set.range (b6_branch t.val))
    (hrot : ∀ i : Fin 13, ∃ x : b63l_parameterFibre b C V hV t,
      b63d_projection b C f V hV t x = b6_branch t.val i ∧ b4_IsRotGen ℂ x (b4b_root i)) :
    Module.finrank ℂ ↥(b63e_transportedF b C hC V hV P s t ⊓
        Module.End.eigenspace (b2_cplxMap (b63g2_operator b C hC V hV s).toAddMonoidHom)
          (HodgeBlocks.WeilAction.omegaC 3)) = 3 ∧
      Module.finrank ℂ ↥(b63e_transportedF b C hC V hV P s t ⊓
        Module.End.eigenspace (b2_cplxMap (b63g2_operator b C hC V hV s).toAddMonoidHom)
          (-HodgeBlocks.WeilAction.omegaC 3)) = 3 :=
  b63g2_eigen_rank_aux b C hC V hV hG P hP s t hb f hf hs hgal hbranch hrot

example (b : Fin 10 → ℂ) (C : Type) [TopologicalSpace C]
    [MulAction b4b_Group C]
    (hC : ∀ g : b4b_Group, Continuous (fun x : C ↦ g • x))
    (V : Set (Fin 10 → ℂ)) (hV : V ⊆ b6t_polydisc b)
    [∀ t : V, ChartedSpace ℂ (b63l_parameterFibre b C V hV t)]
    [∀ t : V, IsManifold 𝓘(ℂ, ℂ) ω (b63l_parameterFibre b C V hV t)]
    [∀ t : V, T2Space (b63l_parameterFibre b C V hV t)]
    [∀ t : V, CompactSpace (b63l_parameterFibre b C V hV t)]
    [∀ t : V, ConnectedSpace (b63l_parameterFibre b C V hV t)]
    (hG : ∀ (t : V) (g : b4b_Group), ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω
      (fun x : b63l_parameterFibre b C V hV t ↦ g • x))
    (P : (t : V) → b6m_H1 (b63l_parameterFibre b C V hV t) →ₗ[ℤ]
      b3_periodLattice ℂ (b63l_parameterFibre b C V hV t))
    (hP : ∀ (t : V) (γ : b3_SmoothLoop ℂ (b63l_parameterFibre b C V hV t)),
      P t (b6m_loopClass _ γ) = b3_latticePeriod ℂ _ γ)
    (s t : V)
    [FaithfulSMul b4b_Group (b63l_parameterFibre b C V hV t)]
    (hb : b ∈ b6_chart) (f : C → OnePoint ℂ)
    (hf : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω (b63d_projection b C f V hV t))
    (hs : Function.Surjective (b63d_projection b C f V hV t))
    (hgal : b4_IsGaloisCover b4b_Group (b63d_projection b C f V hV t))
    (hbranch : b4_branchSet ℂ ℂ (b63d_projection b C f V hV t) = Set.range (b6_branch t.val))
    (hrot : ∀ i : Fin 13, ∃ x : b63l_parameterFibre b C V hV t,
      b63d_projection b C f V hV t x = b6_branch t.val i ∧ b4_IsRotGen ℂ x (b4b_root i)) :
    Module.finrank ℂ ↥(b63e_transportedF b C hC V hV P s t ⊓
        Module.End.eigenspace (b2_cplxMap (b63g2_operator b C hC V hV s).toAddMonoidHom)
          (HodgeBlocks.WeilAction.omegaC 3)) = 3 ∧
      Module.finrank ℂ ↥(b63e_transportedF b C hC V hV P s t ⊓
        Module.End.eigenspace (b2_cplxMap (b63g2_operator b C hC V hV s).toAddMonoidHom)
          (-HodgeBlocks.WeilAction.omegaC 3)) = 3 :=
  b63g2_eigen_rank b C hC V hV hG P hP s t hb f hf hs hgal hbranch hrot

/-! ## Positive-rank and rejected-case checks

The algebra of part 2 has a nonzero rank-two instance: on `ℤ²` with the standard form, the
rotation `b63g2_hex` of order three is an isometry with `c² + c + 1 = 0`, and `1 + 2c` squares
to `-3` and is skew; `c` itself is not skew, so skewness is a property of `1 + 2c`, not of every
isometry. The generic statements of part 3 have a nonzero instance with different values in the
two orders: on the elliptic model with the rotation `b63g_rot` (`n = 1`), the `(1,0)` number is
positive and the `(0,1)` number is zero. -/

/-- The rotation of order three is nonzero, and the lattice has rank two. -/
example : b63g2_hex ≠ 0 ∧ Module.finrank ℤ (Fin 2 → ℤ) = 2 := by
  refine ⟨fun h ↦ ?_, by simp⟩
  have h0 := congrArg (fun f : (Fin 2 → ℤ) →+ (Fin 2 → ℤ) ↦ f (Pi.single 0 1) 1) h
  simp [b63g2_hex_apply] at h0

/-- The pattern of `b63g2_centre_isometry` and `b63g2_operator_skew` on `ℤ²`: `c` is an
isometry of `b2_stdForm` with `c² + c + 1 = 0`; `1 + 2c` squares to `-3` and is skew. -/
example :
    (∀ l m, b2_stdForm (b63g2_hex l) (b63g2_hex m) = b2_stdForm l m) ∧
    (∀ l, b63g2_hex (b63g2_hex l) + b63g2_hex l + l = 0) ∧
    (∀ l, (l + 2 • b63g2_hex l) + 2 • b63g2_hex (l + 2 • b63g2_hex l) = (-3 : ℤ) • l) ∧
    (∀ l m, b2_stdForm (l + 2 • b63g2_hex l) m = -b2_stdForm l (m + 2 • b63g2_hex m)) := by
  refine ⟨fun l m ↦ ?_, fun l ↦ ?_, fun l ↦ ?_, fun l m ↦ ?_⟩
  · simp only [b63g2_stdForm_apply, b63g2_hex_apply]
    simp
    ring
  · ext i
    fin_cases i <;> (simp [b63g2_hex_apply, Matrix.vecHead, Matrix.vecTail]; try ring)
  · ext i
    fin_cases i <;> (simp [b63g2_hex_apply, Matrix.vecHead, Matrix.vecTail]; try ring)
  · simp only [b63g2_stdForm_apply, b63g2_hex_apply]
    simp
    ring

/-- Rejected case: the isometry `c` is not itself skew, so the skewness of `b63g2_operator_skew`
uses the form `1 + 2c` and the relation `c² + c + 1 = 0`. -/
example : ¬ ∀ l m, b2_stdForm (b63g2_hex l) m = -b2_stdForm l (b63g2_hex m) := by
  intro h
  have := h (Pi.single 0 1) (Pi.single 1 1)
  simp [b63g2_stdForm_apply, b63g2_hex_apply] at this

/-- The statements `b63g2_weil_h10` and `b63g2_weil_h01` on the elliptic model with the rotation
(`n = 1`; the hypotheses are the theorems `b63g_rot_sq` and `b63g_rot_stdF`): the vector
`e₀ + i e₁` spans `F` and is an eigenvector of the rotation for `-i`, so the `(1,0)` number is
positive and the `(0,1)` number is zero. The two orders give different values, so the order fixed
by the statements is not immaterial. -/
example :
    letI := b5_groupObj _ _ b2_std_isWeightOne _ b2_std_isRiemannForm
    letI : IsIntegral b5_elliptic.left := b5_integral_aux _ _ b2_std_isWeightOne _
      b2_std_isRiemannForm
    letI := b5_smooth_aux _ _ b2_std_isWeightOne _ b2_std_isRiemannForm
    letI := b5_projective_aux _ _ b2_std_isWeightOne _ b2_std_isRiemannForm
    letI := (torusCohomology_cupProductOf b5_elliptic).finite
    0 < Module.finrank ℂ ↥((b63g2_weilAction _ _ b2_std_isWeightOne _ b2_std_isRiemannForm 1
        b63g_rot b63g_rot_sq b63g_rot_stdF).Vs ⊓
      (abelianVarietyCohomologyOf (finiteBetti_abelian b5_elliptic)
        (spec_bettiDeRhamIso_abelian b5_elliptic) (hodgeDecomposition_of_abelian b5_elliptic)
        (torusCohomology_cupProductOf b5_elliptic)).weight1.H (1, 0)) ∧
    Module.finrank ℂ ↥((b63g2_weilAction _ _ b2_std_isWeightOne _ b2_std_isRiemannForm 1
        b63g_rot b63g_rot_sq b63g_rot_stdF).Vs ⊓
      (abelianVarietyCohomologyOf (finiteBetti_abelian b5_elliptic)
        (spec_bettiDeRhamIso_abelian b5_elliptic) (hodgeDecomposition_of_abelian b5_elliptic)
        (torusCohomology_cupProductOf b5_elliptic)).weight1.H (0, 1)) = 0 := by
  have h0 : b63g_rot (Pi.single 0 1) = Pi.single 1 1 := by
    ext i
    fin_cases i <;> simp [b63g_rot]
  have h1 : b63g_rot (Pi.single 1 1) = -Pi.single 0 1 := by
    ext i
    fin_cases i <;> simp [b63g_rot]
  have hω : HodgeBlocks.WeilAction.omegaC ((1 : ℤ) : ℚ) = Complex.I := by
    simp [HodgeBlocks.WeilAction.omegaC]
  set v : ℂ ⊗[ℤ] (Fin 2 → ℤ) := (1 : ℂ) ⊗ₜ[ℤ] (Pi.single 0 1 : Fin 2 → ℤ) +
    Complex.I ⊗ₜ[ℤ] (Pi.single 1 1 : Fin 2 → ℤ) with hv
  have hrot : b2_cplxMap b63g_rot v = (-Complex.I) • v := by
    simp only [hv, map_add, b2_cplxMap, LinearMap.baseChange_tmul,
      AddMonoidHom.coe_toIntLinearMap, h0, h1, smul_add, TensorProduct.smul_tmul', smul_eq_mul,
      TensorProduct.tmul_neg, mul_one]
    rw [show -Complex.I * Complex.I = 1 by rw [neg_mul, Complex.I_mul_I, neg_neg],
      ← TensorProduct.neg_tmul, add_comm]
  have hv0 : v ≠ 0 := by
    intro h
    have := congrArg (TensorProduct.rid ℤ ℂ ∘ (LinearMap.baseChange ℂ
      (LinearMap.proj 0 : (Fin 2 → ℤ) →ₗ[ℤ] ℤ))) h
    simp [hv] at this
  have hF : b2_stdF = ℂ ∙ v := rfl
  refine ⟨?_, ?_⟩
  · rw [b63g2_weil_h10 _ _ b2_std_isWeightOne _ b2_std_isRiemannForm 1 one_pos b63g_rot
      b63g_rot_sq b63g_rot_stdF, hω]
    refine Module.finrank_pos_iff_exists_ne_zero.2 ⟨⟨v, ?_, ?_⟩, ?_⟩
    · rw [hF]; exact Submodule.mem_span_singleton_self v
    · show v ∈ Module.End.eigenspace _ _
      rw [Module.End.mem_eigenspace_iff, hrot]
    · intro h
      exact hv0 (congrArg Subtype.val h)
  · rw [b63g2_weil_h01 _ _ b2_std_isWeightOne _ b2_std_isRiemannForm 1 one_pos b63g_rot
      b63g_rot_sq b63g_rot_stdF, hω, Submodule.finrank_eq_zero]
    rw [eq_bot_iff]
    rintro w ⟨hwF, hwE⟩
    change w ∈ ℂ ∙ v at hwF
    change w ∈ Module.End.eigenspace _ _ at hwE
    rw [Submodule.mem_span_singleton] at hwF
    obtain ⟨c, rfl⟩ := hwF
    rw [Module.End.mem_eigenspace_iff, map_smul, hrot, smul_smul, smul_smul] at hwE
    rw [Submodule.mem_bot]
    have : (c * -Complex.I - Complex.I * c) • v = 0 := by rw [sub_smul, hwE, sub_self]
    rcases smul_eq_zero.1 this with h | h
    · have hc : c = 0 := by
        have : -2 * Complex.I * c = 0 := by linear_combination h
        simpa [Complex.I_ne_zero] using this
      simp [hc]
    · exact absurd h hv0

/-! ## Chain checks toward `hodge`, Weil type, `W` and `rosati` -/

/-- **Hodge numbers of the generic sixfold.** For B5 data with an operator of square `-3`
preserving `F`, the two Hodge numbers of `b63g2_sixfold` are the dimensions of
`F ∩ ker(φ_ℂ ± i√3)`; when these agree the Weil action is of Weil type. -/
example (Λ : Type) [AddCommGroup Λ] [Module.Finite ℤ Λ] [Module.Free ℤ Λ]
    (F : Submodule ℂ (ℂ ⊗[ℤ] Λ)) (hF : b2_IsWeightOne Λ F)
    (Q : LinearMap.BilinForm ℤ Λ) (hQ : b2_IsRiemannForm Λ F Q) (φ : Λ →+ Λ)
    (hsq : ∀ l, φ (φ l) = (-3 : ℤ) • l) (hφ : F ≤ F.comap (b2_cplxMap φ))
    (h : Module.finrank ℂ ↥(F ⊓ Module.End.eigenspace (b2_cplxMap φ)
        (-HodgeBlocks.WeilAction.omegaC 3)) =
      Module.finrank ℂ ↥(F ⊓ Module.End.eigenspace (b2_cplxMap φ)
        (HodgeBlocks.WeilAction.omegaC 3))) :
    letI := (torusCohomology_cupProductOf (b63g2_sixfold Λ F hF Q hQ φ hsq hφ).X).finite
    (b63g2_sixfold Λ F hF Q hQ φ hsq hφ).W.IsWeilType := by
  have h10 := (b63g2_sixfold_h10 Λ F hF Q hQ φ hsq hφ).trans
    (b63g2_weil_h10 Λ F hF Q hQ 3 (by norm_num) φ hsq hφ)
  have h01 := (b63g2_sixfold_h01 Λ F hF Q hQ φ hsq hφ).trans
    (b63g2_weil_h01 Λ F hF Q hQ 3 (by norm_num) φ hsq hφ)
  rw [show HodgeBlocks.WeilAction.omegaC ((3 : ℤ) : ℚ) = HodgeBlocks.WeilAction.omegaC 3 by
    norm_num] at h10 h01
  exact (isWeilType_iff_finrank_eq _ _ _ _ _).2 (h10.trans (h.trans h01.symm))

/-- **The actual moving fibres.** For the saturated lattice at `s` (made free and finite by a
supplied basis), the filtration transported from `t`, the original form and the operator
`1 + 2ω`, the certificates of `b63e_weight_one_riemann`, the square `b63g2_operator_sq` and the
filtration statement `b63g2_operator_filtration` give a `g32t_Sixfold` on the B5 model. With the
Chevalley–Weil data at `t` its Hodge numbers are `3` and `3`, it is of Weil type, its Weil action
is Rosati-skew for its class (the field `rosati`), and for every Nielsen tuple the field `hodge`
holds in both orders. -/
example (b : Fin 10 → ℂ) (C : Type) [TopologicalSpace C]
    [MulAction b4b_Group C]
    (hC : ∀ g : b4b_Group, Continuous (fun x : C ↦ g • x))
    (V : Set (Fin 10 → ℂ)) (hV : V ⊆ b6t_polydisc b)
    [∀ t : V, ChartedSpace ℂ (b63l_parameterFibre b C V hV t)]
    [∀ t : V, IsManifold 𝓘(ℂ, ℂ) ω (b63l_parameterFibre b C V hV t)]
    [∀ t : V, T2Space (b63l_parameterFibre b C V hV t)]
    [∀ t : V, CompactSpace (b63l_parameterFibre b C V hV t)]
    [∀ t : V, ConnectedSpace (b63l_parameterFibre b C V hV t)]
    (hG : ∀ (t : V) (g : b4b_Group), ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω
      (fun x : b63l_parameterFibre b C V hV t ↦ g • x))
    (hb : b ∈ b6_chart) [ChartedSpace ℂ C] [IsManifold 𝓘(ℂ, ℂ) ω C]
    [T2Space C] [CompactSpace C] [ConnectedSpace C]
    (f : C → OnePoint ℂ) (hf : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω f) (hs : Function.Surjective f)
    (hk : ∀ t : V, ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω (b63d_projection b C f V hV t))
    (Q₀ : LinearMap.BilinForm ℤ (b3_periodLattice ℂ C)) (hQ₀ : b3_IsIntersectionForm ℂ Q₀)
    (Q : (t : V) → LinearMap.BilinForm ℤ (b3_periodLattice ℂ (b63l_parameterFibre b C V hV t)))
    (hQ : ∀ t : V, b3_IsIntersectionForm ℂ (Q t))
    (P : (t : V) → b6m_H1 (b63l_parameterFibre b C V hV t) →ₗ[ℤ]
      b3_periodLattice ℂ (b63l_parameterFibre b C V hV t))
    (hP : ∀ (t : V) (γ : b3_SmoothLoop ℂ (b63l_parameterFibre b C V hV t)),
      P t (b6m_loopClass _ γ) = b3_latticePeriod ℂ _ γ)
    (s t : V) {ι : Type} [Fintype ι]
    (B : Module.Basis ι ℤ (b63l_parameterLattice b C hC V hV s))
    [FaithfulSMul b4b_Group (b63l_parameterFibre b C V hV t)]
    (hgal : b4_IsGaloisCover b4b_Group (b63d_projection b C f V hV t))
    (hbranch : b4_branchSet ℂ ℂ (b63d_projection b C f V hV t) = Set.range (b6_branch t.val))
    (hrot : ∀ i : Fin 13, ∃ x : b63l_parameterFibre b C V hV t,
      b63d_projection b C f V hV t x = b6_branch t.val i ∧ b4_IsRotGen ℂ x (b4b_root i))
    (hst : Function.Surjective (b63d_projection b C f V hV t)) :
    letI : Module.Free ℤ (b63l_parameterLattice b C hC V hV s) := Module.Free.of_basis B
    letI : Module.Finite ℤ (b63l_parameterLattice b C hC V hV s) := Module.Finite.of_basis B
    let X := b63g2_sixfold _ _ (b63e_weight_one_riemann b C hC V hV hG hb f hf hs hk Q₀ hQ₀ Q hQ
      P hP s t).1 _ (b63e_weight_one_riemann b C hC V hV hG hb f hf hs hk Q₀ hQ₀ Q hQ P hP s t).2
      (b63g2_operator b C hC V hV s).toAddMonoidHom (b63g2_operator_sq b C hC V hV s (hG s))
      (b63g2_operator_filtration b C hC V hV hG P hP s t)
    g32h_h10 X = 3 ∧ g32h_h01 X = 3 ∧
      (letI := (torusCohomology_cupProductOf X.X).finite; X.W.IsWeilType) ∧
      (letI := (torusCohomology_cupProductOf X.X).finite
       IsRosatiSkew (polarizationVec (torusCohomology_cupProductOf X.X) X.pol) X.W.J) ∧
      ∀ g : Fin 13 → Matrix (Fin 4) (Fin 4) ℂ, g32h_Nielsen g →
        ((g32h_h10 X : ℝ) = g32h_holoCW g ∧
            (g32h_h01 X : ℝ) = g32h_multCW g - g32h_holoCW g) ∧
          ((g32h_h01 X : ℝ) = g32h_holoCW g ∧
            (g32h_h10 X : ℝ) = g32h_multCW g - g32h_holoCW g) :=
  letI : Module.Free ℤ (b63l_parameterLattice b C hC V hV s) := Module.Free.of_basis B
  letI : Module.Finite ℤ (b63l_parameterLattice b C hC V hV s) := Module.Finite.of_basis B
  have W := b63e_weight_one_riemann b C hC V hV hG hb f hf hs hk Q₀ hQ₀ Q hQ P hP s t
  have hsq := b63g2_operator_sq b C hC V hV s (hG s)
  have hφ := b63g2_operator_filtration b C hC V hV hG P hP s t
  have hE := b63g2_eigen_rank b C hC V hV hG P hP s t hb f (hk t) hst hgal hbranch hrot
  have h10 : g32h_h10 (b63g2_sixfold _ _ W.1 _ W.2 _ hsq hφ) = 3 := by
    have h := (b63g2_sixfold_h10 _ _ W.1 _ W.2 _ hsq hφ).trans
      (b63g2_weil_h10 _ _ W.1 _ W.2 3 (by norm_num) _ hsq hφ)
    rw [show HodgeBlocks.WeilAction.omegaC ((3 : ℤ) : ℚ) = HodgeBlocks.WeilAction.omegaC 3 by
      norm_num] at h
    exact h.trans hE.2
  have h01 : g32h_h01 (b63g2_sixfold _ _ W.1 _ W.2 _ hsq hφ) = 3 := by
    have h := (b63g2_sixfold_h01 _ _ W.1 _ W.2 _ hsq hφ).trans
      (b63g2_weil_h01 _ _ W.1 _ W.2 3 (by norm_num) _ hsq hφ)
    rw [show HodgeBlocks.WeilAction.omegaC ((3 : ℤ) : ℚ) = HodgeBlocks.WeilAction.omegaC 3 by
      norm_num] at h
    exact h.trans hE.1
  ⟨h10, h01, (isWeilType_iff_finrank_eq _ _ _ _ _).2 (h10.trans h01.symm),
    b63g2_sixfold_rosati _ _ W.1 _ W.2 _ hsq hφ
      (b63g2_operator_skew b C hC V hV s (hG s) (P s) (hP s) (Q s) (hQ s)),
    fun g hg ↦ by
      rw [h10, h01, g32h_holoCW_of_nielsen g hg, g32h_multCW_of_nielsen g hg]
      norm_num⟩

end HodgeLean.Foundations.Program
