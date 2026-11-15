import HodgeLean.Foundations.Program.PrymFamilyExistsProofs

/-! # The Prym family `P`: named existence on the marked root cover (FROZEN SPEC)

Each public theorem is the matching `_aux` theorem of `PrymFamilyExistsProofs.lean`.

**Claimed.** Implications from the marked root cover of `MarkedRootCover.lean` and the B6-3
fibre data to an element of `g32h_PrymFamily` with its base and fibres pinned:

* `b63gP_fiber_positive`: the field `positive` at every fibre `b63g5_fiber … t` of the marked
  family, from part 4 (`b63g4_abelian_positive` on the class `b63g_modelClass`, not negated);
* `b63gP_family_of_cover`: every conclusion of `mr_rootCover` with fibre data over a parameter
  set `V ⊆ b6t_polydisc mr_base` and a basis of rank twelve gives an element `F` with
  `V ≃ F.S`, `F.tuple = b63g5_tuple` and `F.fiber = b63g5_fiber … t` at every `t`, and
  `Nonempty F.S`; `positive` is `b63gP_fiber_positive`, not a binder;
* `b63gP_exists`: some element is marked over the whole polydisc for the explicit loops
  `b63gP_loops` (`b63gP_IsMarked`) and has a nonempty index type;
* `b63gP_family_isMarked`, `b63gP_family_tuple`: the named family `b63gP_family` (Hilbert's
  choice of a marked, nonempty element) is marked, nonempty, with tuple `b63g5_tuple`;
* `b63gP_theoremA`, `b63gP_theoremA_of_transport`, `b63gP_theoremA_of_reverse`,
  `b63gP_theoremA_of_qinv`: the G32 Theorem A statements of `g32a_theoremA` and of the three
  premise bundles with `P := b63gP_family` supplied, the last three with the field `spread`
  derived by S7 for `F.univ = b60b_univ`.

**Not claimed.** The remaining G32 premises over `b63gP_family`: stage 3 `h46`, the period map
`R`, the stage-5 comparison `hpol`, and `transport` (or `reverse`, or `qinv`); the rational
variation of Hodge structure over the polydisc (part 6); a marking outside
`b6t_polydisc mr_base`; any identification with the selected `b6_Cover`; a discriminant,
algebraicity of Weil classes or dominance.
HC no distance; AV milestone no distance.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint AlgebraicTopology.Singular
open HodgeLean.RealDefs HodgeLean.Adapters HodgeLean.Foundations HodgeLean.Papers
open HodgeLean.Foundations.Symplectic HodgeLean.Foundations.AppellHumbert
open TopologicalSpace
open scoped Manifold ContDiff

namespace HodgeLean.Foundations.Program
attribute [local instance] b4cov_sphChartedSpace b4cov_sph_isManifold

/-- **The field `positive` on the fibres of the marked family.** For every base `b` of the
chart, every B6-3 fibre data and every basis of the reference lattice, the restricted
polarization of `b63g5_fiber … t` is positive, for every nondegeneracy witness. The fibre is the
part 1 sixfold `b63g2_sixfold` of the B5 model of `(Λ_{s₀}, F_t, Q_{s₀})`, whose class is
`b63g_modelClass`, not negated; the Riemann form is `b63g_modelForm_riemann` of the certificate
`b63e_weight_one_riemann`, and part 4 gives positivity of its class (`b63g4_abelian_positive`).
Source: G32 v0.16, Lemma 3.3 (the restricted polarization is a polarization); Birkenhake–Lange,
*Complex Abelian Varieties*, 2nd ed., §4.1–§4.2 (Riemann relations); `b63g4_abelian_positive`,
`b63g_modelForm_riemann`, `b63e_weight_one_riemann`. -/
theorem b63gP_fiber_positive (b : Fin 10 → ℂ) (C : Type) [TopologicalSpace C]
    [MulAction b4b_Group C]
    (hC : ∀ g : b4b_Group, Continuous (fun x : C ↦ g • x))
    (V : Set (Fin 10 → ℂ)) (hV : V ⊆ b6t_polydisc b)
    [∀ t : V, ChartedSpace ℂ (b63l_parameterFibre b C V hV t)]
    [∀ t : V, IsManifold 𝓘(ℂ, ℂ) ω (b63l_parameterFibre b C V hV t)]
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
    (s₀ : V) {ι : Type} [Fintype ι] (B : Module.Basis ι ℤ (b63l_parameterLattice b C hC V hV s₀))
    (t : V) :
    let X := b63g5_fiber b C hC V hV hG hb f hf hs hk Q₀ hQ₀ Q hQ P hP s₀ B t
    ∀ h : IsNondegenerate (polarizationVec (torusCohomology_cupProductOf X.X) X.pol),
      PolarizationPositive (finiteBetti_abelian X.X) (spec_bettiDeRhamIso_abelian X.X)
        (hodgeDecomposition_of_abelian X.X) (torusCohomology_cupProductOf X.X) h :=
  b63gP_fiber_positive_aux b C hC V hV hG hb f hf hs hk Q₀ hQ₀ Q hQ P hP s₀ B t

example (b : Fin 10 → ℂ) (C : Type) [TopologicalSpace C]
    [MulAction b4b_Group C]
    (hC : ∀ g : b4b_Group, Continuous (fun x : C ↦ g • x))
    (V : Set (Fin 10 → ℂ)) (hV : V ⊆ b6t_polydisc b)
    [∀ t : V, ChartedSpace ℂ (b63l_parameterFibre b C V hV t)]
    [∀ t : V, IsManifold 𝓘(ℂ, ℂ) ω (b63l_parameterFibre b C V hV t)]
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
    (s₀ : V) {ι : Type} [Fintype ι] (B : Module.Basis ι ℤ (b63l_parameterLattice b C hC V hV s₀))
    (t : V) :
    let X := b63g5_fiber b C hC V hV hG hb f hf hs hk Q₀ hQ₀ Q hQ P hP s₀ B t
    ∀ h : IsNondegenerate (polarizationVec (torusCohomology_cupProductOf X.X) X.pol),
      PolarizationPositive (finiteBetti_abelian X.X) (spec_bettiDeRhamIso_abelian X.X)
        (hodgeDecomposition_of_abelian X.X) (torusCohomology_cupProductOf X.X) h :=
  b63gP_fiber_positive b C hC V hV hG hb f hf hs hk Q₀ hQ₀ Q hQ P hP s₀ B t

/-- **The marked family of a marked root cover is a Prym family.** For every conclusion of
`mr_rootCover` (with base point `y₀` and explicit loops `γ`), every parameter set
`V ⊆ b6t_polydisc mr_base`, every B6-3 fibre data on `V`, every reference parameter `s₀ : V`
and every basis of rank twelve of `Λ_{s₀}`, there is an element `F` of `g32h_PrymFamily` with an
equivalence `V ≃ F.S`, the marked tuple `b63g5_tuple` and the fibre `b63g5_fiber … t` at the
image of every `t`, and a nonempty index type. The fields other than `positive` are those of the
part 5 assembly; `positive` is `b63gP_fiber_positive`, the statement of part 4 on these fibres.
Source: G32 v0.16, Subsections 3.1–3.3, Lemma 3.3 and Lemma 3.6; the part 5 statements
`b63g5_fibre_galois`, `b63g5_fibre_branch`, `b63g5_fibre_rot`; `b63g2_eigen_rank`,
`b63g_model_finrank`, `b2_abelian_nondegenerate`, `b63g2_sixfold_rosati`,
`b63g4_abelian_positive`; Chevalley–Weil in the form of Frediani–Ghigi–Penegini, IMRN 2015,
Theorem 2.10. -/
theorem b63gP_family_of_cover (U : Type) [TopologicalSpace U] [MulAction b4b_Group U]
    (π : U → b6t_punctured mr_base) (hπ : IsQuotientCoveringMap π b4b_Group)
    (y₀ : b6t_punctured mr_base) (u₀ : π ⁻¹' {y₀})
    (γ : Fin 13 → FundamentalGroup (b6t_punctured mr_base) y₀)
    (hγ : ∀ i, mr_IsLoop mr_base y₀ i (γ i))
    (hroot : ∀ i, hπ.fundamentalGroupToMulOpposite u₀ (γ i) = MulOpposite.op (b4b_root i))
    (C : Type) [TopologicalSpace C] [ChartedSpace ℂ C] [IsManifold 𝓘(ℂ, ℂ) ω C]
    [T2Space C] [CompactSpace C] [ConnectedSpace C]
    [MulAction b4b_Group C] [FaithfulSMul b4b_Group C] (f : C → OnePoint ℂ) (ι : U → C)
    (hf : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω f) (hgal : b4_IsGaloisCover b4b_Group f)
    (hsurj : Function.Surjective f)
    (hC : ∀ g : b4b_Group, Continuous (fun x : C ↦ g • x))
    (hι : Continuous ι) (hproj : ∀ u, f (ι u) = π u)
    (hequiv : ∀ (g : b4b_Group) (u : U), ι (g • u) = g • ι u)
    (hfree : ∀ x, f x ∉ Set.range (b6_branch mr_base) → MulAction.stabilizer b4b_Group x = ⊥)
    (hrot₀ : ∀ j, ∃ x, f x = b6_branch mr_base j ∧ b4_IsRotGen ℂ x (b4b_root j))
    (V : Set (Fin 10 → ℂ)) (hV : V ⊆ b6t_polydisc mr_base)
    [∀ t : V, ChartedSpace ℂ (b63l_parameterFibre mr_base C V hV t)]
    [∀ t : V, IsManifold 𝓘(ℂ, ℂ) ω (b63l_parameterFibre mr_base C V hV t)]
    (hG : ∀ (t : V) (g : b4b_Group), ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω
      (fun x : b63l_parameterFibre mr_base C V hV t ↦ g • x))
    (hk : ∀ t : V, ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω (b63d_projection mr_base C f V hV t))
    (Q₀ : LinearMap.BilinForm ℤ (b3_periodLattice ℂ C)) (hQ₀ : b3_IsIntersectionForm ℂ Q₀)
    (Q : (t : V) → LinearMap.BilinForm ℤ
      (b3_periodLattice ℂ (b63l_parameterFibre mr_base C V hV t)))
    (hQ : ∀ t : V, b3_IsIntersectionForm ℂ (Q t))
    (P : (t : V) → b6m_H1 (b63l_parameterFibre mr_base C V hV t) →ₗ[ℤ]
      b3_periodLattice ℂ (b63l_parameterFibre mr_base C V hV t))
    (hP : ∀ (t : V) (γ : b3_SmoothLoop ℂ (b63l_parameterFibre mr_base C V hV t)),
      P t (b6m_loopClass _ γ) = b3_latticePeriod ℂ _ γ)
    (s₀ : V) (B : Module.Basis (Fin 12) ℤ (b63l_parameterLattice mr_base C hC V hV s₀)) :
    ∃ F : g32h_PrymFamily, (∃ j : V ≃ F.S, ∀ t : V,
      F.tuple (j t) = b63g5_tuple ∧
        F.fiber (j t) = b63g5_fiber mr_base C hC V hV hG mr_base_mem_chart f hf hsurj hk Q₀ hQ₀
          Q hQ P hP s₀ B t) ∧ Nonempty F.S :=
  b63gP_family_of_cover_aux U π hπ y₀ u₀ γ hγ hroot C f ι hf hgal hsurj hC hι hproj hequiv hfree hrot₀ V hV hG hk Q₀ hQ₀ Q hQ P hP s₀ B

example (U : Type) [TopologicalSpace U] [MulAction b4b_Group U]
    (π : U → b6t_punctured mr_base) (hπ : IsQuotientCoveringMap π b4b_Group)
    (y₀ : b6t_punctured mr_base) (u₀ : π ⁻¹' {y₀})
    (γ : Fin 13 → FundamentalGroup (b6t_punctured mr_base) y₀)
    (hγ : ∀ i, mr_IsLoop mr_base y₀ i (γ i))
    (hroot : ∀ i, hπ.fundamentalGroupToMulOpposite u₀ (γ i) = MulOpposite.op (b4b_root i))
    (C : Type) [TopologicalSpace C] [ChartedSpace ℂ C] [IsManifold 𝓘(ℂ, ℂ) ω C]
    [T2Space C] [CompactSpace C] [ConnectedSpace C]
    [MulAction b4b_Group C] [FaithfulSMul b4b_Group C] (f : C → OnePoint ℂ) (ι : U → C)
    (hf : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω f) (hgal : b4_IsGaloisCover b4b_Group f)
    (hsurj : Function.Surjective f)
    (hC : ∀ g : b4b_Group, Continuous (fun x : C ↦ g • x))
    (hι : Continuous ι) (hproj : ∀ u, f (ι u) = π u)
    (hequiv : ∀ (g : b4b_Group) (u : U), ι (g • u) = g • ι u)
    (hfree : ∀ x, f x ∉ Set.range (b6_branch mr_base) → MulAction.stabilizer b4b_Group x = ⊥)
    (hrot₀ : ∀ j, ∃ x, f x = b6_branch mr_base j ∧ b4_IsRotGen ℂ x (b4b_root j))
    (V : Set (Fin 10 → ℂ)) (hV : V ⊆ b6t_polydisc mr_base)
    [∀ t : V, ChartedSpace ℂ (b63l_parameterFibre mr_base C V hV t)]
    [∀ t : V, IsManifold 𝓘(ℂ, ℂ) ω (b63l_parameterFibre mr_base C V hV t)]
    (hG : ∀ (t : V) (g : b4b_Group), ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω
      (fun x : b63l_parameterFibre mr_base C V hV t ↦ g • x))
    (hk : ∀ t : V, ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω (b63d_projection mr_base C f V hV t))
    (Q₀ : LinearMap.BilinForm ℤ (b3_periodLattice ℂ C)) (hQ₀ : b3_IsIntersectionForm ℂ Q₀)
    (Q : (t : V) → LinearMap.BilinForm ℤ
      (b3_periodLattice ℂ (b63l_parameterFibre mr_base C V hV t)))
    (hQ : ∀ t : V, b3_IsIntersectionForm ℂ (Q t))
    (P : (t : V) → b6m_H1 (b63l_parameterFibre mr_base C V hV t) →ₗ[ℤ]
      b3_periodLattice ℂ (b63l_parameterFibre mr_base C V hV t))
    (hP : ∀ (t : V) (γ : b3_SmoothLoop ℂ (b63l_parameterFibre mr_base C V hV t)),
      P t (b6m_loopClass _ γ) = b3_latticePeriod ℂ _ γ)
    (s₀ : V) (B : Module.Basis (Fin 12) ℤ (b63l_parameterLattice mr_base C hC V hV s₀)) :
    ∃ F : g32h_PrymFamily, (∃ j : V ≃ F.S, ∀ t : V,
      F.tuple (j t) = b63g5_tuple ∧
        F.fiber (j t) = b63g5_fiber mr_base C hC V hV hG mr_base_mem_chart f hf hsurj hk Q₀ hQ₀
          Q hQ P hP s₀ B t) ∧ Nonempty F.S :=
  b63gP_family_of_cover U π hπ y₀ u₀ γ hγ hroot C f ι hf hgal hsurj hC hι hproj hequiv hfree hrot₀ V hV hG hk Q₀ hQ₀ Q hQ P hP s₀ B

/-- **Existence of the marked Prym family over the polydisc.** Some element of `g32h_PrymFamily`
is marked (`b63gP_IsMarked`: the marked family of a marked root cover for the explicit loops
`b63gP_loops` at `b63gP_basePoint`, indexed by the whole polydisc `b6t_polydisc mr_base`, with
tuple `b63g5_tuple` and fibre `b63g5_fiber … t` at every `t`) and has a nonempty index type.
The witness is `b63gP_family_of_cover` applied to `mr_rootCover` for these loops, the fibre
complex structures of `b63g5_fibre_structure`, the intersection forms of
`b3_exists_intersectionForm`, the period comparisons of `b6m_period_comparison` and the basis of
rank twelve of `b63d_lattice_rank` at `b63gP_s₀`.
Source: G32 v0.16, Lemma 3.6; `mr_rootCover`, `b63g5_fibre_structure`,
`b3_exists_intersectionForm`, `b6m_period_comparison`, `b63d_lattice_rank`; Forster,
*Lectures on Riemann Surfaces*, GTM 81, Theorems 4.22 and 8.4. -/
theorem b63gP_exists :
    ∃ F : g32h_PrymFamily, b63gP_IsMarked F ∧ Nonempty F.S :=
  b63gP_exists_aux

example :
    ∃ F : g32h_PrymFamily, b63gP_IsMarked F ∧ Nonempty F.S :=
  b63gP_exists

/-- **`b63gP_family` is marked, with a nonempty index type.** The choice of `b63gP_family` is a
marked element once one exists (`b63gP_exists`, Mathlib `Classical.epsilon_spec`). So its index
type is the polydisc up to the equivalence of `b63gP_IsMarked`, its tuple is `b63g5_tuple` and
its fibres are `b63g5_fiber … t`.
Source: `b63gP_exists`; Mathlib `Classical.epsilon_spec`. -/
theorem b63gP_family_isMarked :
    b63gP_IsMarked b63gP_family ∧ Nonempty b63gP_family.S :=
  b63gP_family_isMarked_aux

example :
    b63gP_IsMarked b63gP_family ∧ Nonempty b63gP_family.S :=
  b63gP_family_isMarked

/-- **The tuple of `b63gP_family` is the marked tuple** at every index.
Source: `b63gP_family_isMarked` (the equivalence of `b63gP_IsMarked` is surjective);
`b63g5_tuple`. -/
theorem b63gP_family_tuple (s : b63gP_family.S) :
    b63gP_family.tuple s = b63g5_tuple :=
  b63gP_family_tuple_aux s

example (s : b63gP_family.S) :
    b63gP_family.tuple s = b63g5_tuple :=
  b63gP_family_tuple s

/-- **G32 Theorem A with the Prym family fixed.** `g32a_theoremA` at `P := b63gP_family`: from the
universal family `F`, stage 3 `h46`, the period map `R`, the stage-5 comparison `hpol`, Hilbert
spreading `spread` and isogeny transport `transport`, all over `b63gP_family`, the Weil classes
of every member of `M = (3, ℚ(√-3), [-2])` are algebraic. The premise `P` is gone.
Source: G32 v0.16, Theorem A and its proof (Theorem 7.2); `g32a_theoremA`;
`b63gP_family`. -/
theorem b63gP_theoremA (F : g32m_UniversalFamily)
    (h46 : g32s_Prop46 b63gP_family) (R : g32r_PeriodMap F b63gP_family)
    (hpol : ∀ s, g32d_ParabolicPolarization (g32h_fiber_polarized b63gP_family s))
    (spread : ∃ C : Set (Set g32m_Domain), C.Countable ∧
      (∀ Z ∈ C, IsClosedAnalytic (Fin 9 → ℂ) Z) ∧ {m | g32t_WeilAlg (F.univ m)} = ⋃₀ C)
    (transport : ∀ P Q, g32t_KIsog P Q → (g32t_WeilAlg P ↔ g32t_WeilAlg Q))
    (A : Over (Spec ↧ℂ))
    [GrpObj A] [IsCommMonObj A] [IsIntegral A.left] [Smooth A.hom] [IsProjective A.hom]
    (W : letI := (torusCohomology_cupProductOf A).finite
      HodgeBlocks.WeilAction
        (abelianVarietyCohomologyOf (finiteBetti_abelian A)
          (spec_bettiDeRhamIso_abelian A) (hodgeDecomposition_of_abelian A)
          (torusCohomology_cupProductOf A)).weight1 3)
    (pol : HQ A 2) : G32TheoremAStatement A W pol :=
  b63gP_theoremA_aux F h46 R hpol spread transport A W pol

example (F : g32m_UniversalFamily)
    (h46 : g32s_Prop46 b63gP_family) (R : g32r_PeriodMap F b63gP_family)
    (hpol : ∀ s, g32d_ParabolicPolarization (g32h_fiber_polarized b63gP_family s))
    (spread : ∃ C : Set (Set g32m_Domain), C.Countable ∧
      (∀ Z ∈ C, IsClosedAnalytic (Fin 9 → ℂ) Z) ∧ {m | g32t_WeilAlg (F.univ m)} = ⋃₀ C)
    (transport : ∀ P Q, g32t_KIsog P Q → (g32t_WeilAlg P ↔ g32t_WeilAlg Q))
    (A : Over (Spec ↧ℂ))
    [GrpObj A] [IsCommMonObj A] [IsIntegral A.left] [Smooth A.hom] [IsProjective A.hom]
    (W : letI := (torusCohomology_cupProductOf A).finite
      HodgeBlocks.WeilAction
        (abelianVarietyCohomologyOf (finiteBetti_abelian A)
          (spec_bettiDeRhamIso_abelian A) (hodgeDecomposition_of_abelian A)
          (torusCohomology_cupProductOf A)).weight1 3)
    (pol : HQ A 2) : G32TheoremAStatement A W pol :=
  b63gP_theoremA F h46 R hpol spread transport A W pol

/-- **G32 Theorem A with the Prym family fixed and spreading derived (S7b).** For a universal
family with `F.univ = b60b_univ`, the field `spread` is `hk7_spread` from `h46`, `R` and the
first direction of `transport` at the dominance pairs. The premises that remain are `F`, `h46`,
`R`, `hpol` and `transport`.
Source: G32 v0.16, Theorem A, Lemma 2.2 and Lemma 7.1; `hk7_spread`,
`g32a_theoremA_of_premises`. -/
theorem b63gP_theoremA_of_transport (F : g32m_UniversalFamily) (hF : F.univ = b60b_univ)
    (h46 : g32s_Prop46 b63gP_family) (R : g32r_PeriodMap F b63gP_family)
    (hpol : ∀ s, g32d_ParabolicPolarization (g32h_fiber_polarized b63gP_family s))
    (transport : ∀ P Q, g32t_KIsog P Q → (g32t_WeilAlg P ↔ g32t_WeilAlg Q))
    (A : Over (Spec ↧ℂ))
    [GrpObj A] [IsCommMonObj A] [IsIntegral A.left] [Smooth A.hom] [IsProjective A.hom]
    (W : letI := (torusCohomology_cupProductOf A).finite
      HodgeBlocks.WeilAction
        (abelianVarietyCohomologyOf (finiteBetti_abelian A)
          (spec_bettiDeRhamIso_abelian A) (hodgeDecomposition_of_abelian A)
          (torusCohomology_cupProductOf A)).weight1 3)
    (pol : HQ A 2) : G32TheoremAStatement A W pol :=
  b63gP_theoremA_of_transport_aux F hF h46 R hpol transport A W pol

example (F : g32m_UniversalFamily) (hF : F.univ = b60b_univ)
    (h46 : g32s_Prop46 b63gP_family) (R : g32r_PeriodMap F b63gP_family)
    (hpol : ∀ s, g32d_ParabolicPolarization (g32h_fiber_polarized b63gP_family s))
    (transport : ∀ P Q, g32t_KIsog P Q → (g32t_WeilAlg P ↔ g32t_WeilAlg Q))
    (A : Over (Spec ↧ℂ))
    [GrpObj A] [IsCommMonObj A] [IsIntegral A.left] [Smooth A.hom] [IsProjective A.hom]
    (W : letI := (torusCohomology_cupProductOf A).finite
      HodgeBlocks.WeilAction
        (abelianVarietyCohomologyOf (finiteBetti_abelian A)
          (spec_bettiDeRhamIso_abelian A) (hodgeDecomposition_of_abelian A)
          (torusCohomology_cupProductOf A)).weight1 3)
    (pol : HQ A 2) : G32TheoremAStatement A W pol :=
  b63gP_theoremA_of_transport F hF h46 R hpol transport A W pol

/-- **G32 Theorem A with the Prym family fixed, along reverse isogenies (S7g).** For a universal
family with `F.univ = b60b_univ`, the bundle `g32n_premises` with `P := b63gP_family` and
`spread := hk7_spread_of_members`; the premises that remain are `F`, `h46`, `R`, `hpol` and
`reverse`.
Source: G32 v0.16, Theorem A and Sections 2–7; Mumford, *Abelian Varieties*, §§4 and 18;
`hk7_spread_of_members`, `g32n_theoremA_of_premises`. -/
theorem b63gP_theoremA_of_reverse (F : g32m_UniversalFamily) (hF : F.univ = b60b_univ)
    (h46 : g32s_Prop46 b63gP_family) (R : g32r_PeriodMap F b63gP_family)
    (hpol : ∀ s, g32d_ParabolicPolarization (g32h_fiber_polarized b63gP_family s))
    (reverse : ∀ P Q, g32t_IsMember P → g32t_IsMember Q → g32t_KIsog P Q → g32t_KIsog Q P)
    (A : Over (Spec ↧ℂ))
    [GrpObj A] [IsCommMonObj A] [IsIntegral A.left] [Smooth A.hom] [IsProjective A.hom]
    (W : letI := (torusCohomology_cupProductOf A).finite
      HodgeBlocks.WeilAction
        (abelianVarietyCohomologyOf (finiteBetti_abelian A)
          (spec_bettiDeRhamIso_abelian A) (hodgeDecomposition_of_abelian A)
          (torusCohomology_cupProductOf A)).weight1 3)
    (pol : HQ A 2) : G32TheoremAStatement A W pol :=
  b63gP_theoremA_of_reverse_aux F hF h46 R hpol reverse A W pol

example (F : g32m_UniversalFamily) (hF : F.univ = b60b_univ)
    (h46 : g32s_Prop46 b63gP_family) (R : g32r_PeriodMap F b63gP_family)
    (hpol : ∀ s, g32d_ParabolicPolarization (g32h_fiber_polarized b63gP_family s))
    (reverse : ∀ P Q, g32t_IsMember P → g32t_IsMember Q → g32t_KIsog P Q → g32t_KIsog Q P)
    (A : Over (Spec ↧ℂ))
    [GrpObj A] [IsCommMonObj A] [IsIntegral A.left] [Smooth A.hom] [IsProjective A.hom]
    (W : letI := (torusCohomology_cupProductOf A).finite
      HodgeBlocks.WeilAction
        (abelianVarietyCohomologyOf (finiteBetti_abelian A)
          (spec_bettiDeRhamIso_abelian A) (hodgeDecomposition_of_abelian A)
          (torusCohomology_cupProductOf A)).weight1 3)
    (pol : HQ A 2) : G32TheoremAStatement A W pol :=
  b63gP_theoremA_of_reverse F hF h46 R hpol reverse A W pol

/-- **G32 Theorem A with the Prym family fixed, along quasi-inverses (S7f).** For a universal
family with `F.univ = b60b_univ`, the bundle `qinv_premises` with `P := b63gP_family` and
`spread := hk7_spread_of_witness`; the premises that remain are `F`, `h46`, `R`, `hpol` and
`qinv`.
Source: G32 v0.16, Theorem A and Sections 2–7; Mumford, *Abelian Varieties*, §4;
`hk7_spread_of_witness`, `qinv_g32_theoremA_of_premises`. -/
theorem b63gP_theoremA_of_qinv (F : g32m_UniversalFamily) (hF : F.univ = b60b_univ)
    (h46 : g32s_Prop46 b63gP_family) (R : g32r_PeriodMap F b63gP_family)
    (hpol : ∀ s, g32d_ParabolicPolarization (g32h_fiber_polarized b63gP_family s))
    (qinv : qinv_premise)
    (A : Over (Spec ↧ℂ))
    [GrpObj A] [IsCommMonObj A] [IsIntegral A.left] [Smooth A.hom] [IsProjective A.hom]
    (W : letI := (torusCohomology_cupProductOf A).finite
      HodgeBlocks.WeilAction
        (abelianVarietyCohomologyOf (finiteBetti_abelian A)
          (spec_bettiDeRhamIso_abelian A) (hodgeDecomposition_of_abelian A)
          (torusCohomology_cupProductOf A)).weight1 3)
    (pol : HQ A 2) : G32TheoremAStatement A W pol :=
  b63gP_theoremA_of_qinv_aux F hF h46 R hpol qinv A W pol

example (F : g32m_UniversalFamily) (hF : F.univ = b60b_univ)
    (h46 : g32s_Prop46 b63gP_family) (R : g32r_PeriodMap F b63gP_family)
    (hpol : ∀ s, g32d_ParabolicPolarization (g32h_fiber_polarized b63gP_family s))
    (qinv : qinv_premise)
    (A : Over (Spec ↧ℂ))
    [GrpObj A] [IsCommMonObj A] [IsIntegral A.left] [Smooth A.hom] [IsProjective A.hom]
    (W : letI := (torusCohomology_cupProductOf A).finite
      HodgeBlocks.WeilAction
        (abelianVarietyCohomologyOf (finiteBetti_abelian A)
          (spec_bettiDeRhamIso_abelian A) (hodgeDecomposition_of_abelian A)
          (torusCohomology_cupProductOf A)).weight1 3)
    (pol : HQ A 2) : G32TheoremAStatement A W pol :=
  b63gP_theoremA_of_qinv F hF h46 R hpol qinv A W pol

/-! ## Checks

All checks below have bodies. -/

/-- **Derivation of `b63gP_fiber_positive` from part 4.** The fibre is the B5 model of the
reference lattice with the transported filtration, and its class is `b63g_modelClass`; part 4
(`b63g4_abelian_positive`) applies to the Riemann form `b63g_modelForm_riemann`. -/
example (b : Fin 10 → ℂ) (C : Type) [TopologicalSpace C]
    [MulAction b4b_Group C]
    (hC : ∀ g : b4b_Group, Continuous (fun x : C ↦ g • x))
    (V : Set (Fin 10 → ℂ)) (hV : V ⊆ b6t_polydisc b)
    [∀ t : V, ChartedSpace ℂ (b63l_parameterFibre b C V hV t)]
    [∀ t : V, IsManifold 𝓘(ℂ, ℂ) ω (b63l_parameterFibre b C V hV t)]
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
    (s₀ : V) {ι : Type} [Fintype ι] (B : Module.Basis ι ℤ (b63l_parameterLattice b C hC V hV s₀))
    (t : V) :
    let X := b63g5_fiber b C hC V hV hG hb f hf hs hk Q₀ hQ₀ Q hQ P hP s₀ B t
    ∀ h : IsNondegenerate (polarizationVec (torusCohomology_cupProductOf X.X) X.pol),
      PolarizationPositive (finiteBetti_abelian X.X) (spec_bettiDeRhamIso_abelian X.X)
        (hodgeDecomposition_of_abelian X.X) (torusCohomology_cupProductOf X.X) h := by
  intro X
  let _ : Module.Free ℤ (b63l_parameterLattice b C hC V hV s₀) := Module.Free.of_basis B
  let _ : Module.Finite ℤ (b63l_parameterLattice b C hC V hV s₀) := Module.Finite.of_basis B
  have W := b63e_weight_one_riemann b C hC V hV hG hb f hf hs hk Q₀ hQ₀ Q hQ P hP s₀ t
  have hsq := b63g2_operator_sq b C hC V hV s₀ (hG s₀)
  have hφ := b63g2_operator_filtration b C hC V hV hG P hP s₀ t
  have hX : X = b63g2_sixfold _ _ W.1 _ W.2 _ hsq hφ := rfl
  rw [hX]
  unfold b63g2_sixfold
  intro h
  let _ := b5_groupObj _ _ W.1 _ W.2
  let _ : IsIntegral (b5_model _ _ W.1 (b63e_singularQ b C hC V hV s₀ (P s₀) (Q s₀))).left :=
    b5_integral_aux _ _ W.1 _ W.2
  let _ := b5_smooth_aux _ _ W.1 _ W.2
  let _ := b5_projective_aux _ _ W.1 _ W.2
  exact b63g4_abelian_positive _ _ (b63g_modelForm_riemann _ _ W.1 _ W.2)

/-- **Instance check on the actual marked root cover, and the chain to `b63gP_exists`.** From
`mr_rootCover` for the explicit loops `b63gP_loops` at `b63gP_basePoint`, the fibre complex
structures `b63g5_fibre_structure`, the intersection forms `b3_exists_intersectionForm`, the period
comparisons `b6m_period_comparison` and the basis of rank twelve (not zero) of
`b63d_lattice_rank` at `b63gP_s₀`, every binder of `b63gP_family_of_cover` is supplied with
`V` the whole polydisc, and its conclusion is the statement `b63gP_exists`. -/
example : ∃ F : g32h_PrymFamily, b63gP_IsMarked F ∧ Nonempty F.S := by
  have hb : mr_base ∈ b6_chart := mr_base_mem_chart
  have hγ : ∀ i, mr_IsLoop mr_base b63gP_basePoint i (b63gP_loops i) := fun i ↦
    (mr_loop_existsUnique mr_base b63gP_s₀.property b63gP_basePoint rfl i).exists.choose_spec
  obtain ⟨U, _, _, _, π, hπ, u₀, hroot, C, _, _, _, _, _, _, _, _, f, ι, hf, hgal, hsurj, hact,
    hι, hrange, hproj, hequiv, hfree, hrot₀⟩ := mr_rootCover b63gP_basePoint b63gP_loops hγ
  have hC : ∀ g : b4b_Group, Continuous (fun x : C ↦ g • x) := fun g ↦ (hact g).continuous
  have hS := fun t : b6t_polydisc mr_base ↦
    b63g5_fibre_structure mr_base hb C f hf hgal hact (b6t_polydisc mr_base) Set.Subset.rfl t
  choose cs ms hk hG using hS
  obtain ⟨Q₀, hQ₀⟩ := b3_exists_intersectionForm (E := ℂ) (C := C) (Module.finrank_self ℂ)
  choose Q hQ using fun t : b6t_polydisc mr_base ↦
    b3_exists_intersectionForm (E := ℂ)
      (C := b63l_parameterFibre mr_base C (b6t_polydisc mr_base) Set.Subset.rfl t)
      (Module.finrank_self ℂ)
  choose P hP using fun t : b6t_polydisc mr_base ↦ b6m_period_comparison
    (b63l_parameterFibre mr_base C (b6t_polydisc mr_base) Set.Subset.rfl t)
  have hstab : ∀ j : Fin 13, ∃ x, f x = b6_branch mr_base j ∧
      MulAction.stabilizer b4b_Group x ≠ ⊥ := by
    intro j
    obtain ⟨x, hx, hrx⟩ := hrot₀ j
    refine ⟨x, hx, fun h ↦ ?_⟩
    have hmem : b4b_root j ∈ MulAction.stabilizer b4b_Group x := hrx.1
    rw [h, Subgroup.mem_bot] at hmem
    have h3 := b63_root_order j
    rw [hmem, orderOf_one] at h3
    split_ifs at h3 <;> omega
  have hgal' := (b63g5_fibre_galois mr_base hb C f hgal hsurj hfree (b6t_polydisc mr_base)
    Set.Subset.rfl b63gP_s₀)
  have B : Module.Basis (Fin 12) ℤ (b63l_parameterLattice mr_base C hC (b6t_polydisc mr_base)
      Set.Subset.rfl b63gP_s₀) :=
    (b63d_lattice_rank mr_base C hC (b6t_polydisc mr_base) Set.Subset.rfl b63gP_s₀
      (hG b63gP_s₀) hb f (hk b63gP_s₀) hgal'.2.1 hgal'.1
      (b63g5_fibre_branch mr_base hb C f hgal hsurj hfree hstab (b6t_polydisc mr_base)
        Set.Subset.rfl b63gP_s₀ (hk b63gP_s₀) (hG b63gP_s₀))
      (b63g5_fibre_rot U π hπ b63gP_basePoint u₀ b63gP_loops hγ hroot C f ι hι.continuous hproj
        hequiv hgal hsurj hfree (b6t_polydisc mr_base) Set.Subset.rfl b63gP_s₀ (hk b63gP_s₀)
        (hG b63gP_s₀))).1.some
  obtain ⟨F, ⟨j, hj⟩, hne⟩ := b63gP_family_of_cover U π hπ b63gP_basePoint u₀ b63gP_loops hγ
    hroot C f ι hf hgal hsurj hC hι.continuous hproj hequiv hfree hrot₀ (b6t_polydisc mr_base)
    Set.Subset.rfl hG hk Q₀ hQ₀ Q hQ (fun t ↦ (P t).toLinearMap) hP b63gP_s₀ B
  exact ⟨F, ⟨U, inferInstance, inferInstance, inferInstance, π, hπ, u₀, hroot, C, inferInstance,
    inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, f, ι, hf, hsurj, hact, hgal, hι, hrange, hproj, hequiv, hfree, hrot₀, cs, ms,
    hG, hk, Q₀, hQ₀, Q, hQ, fun t ↦ (P t).toLinearMap, hP, B, j, hj⟩, hne⟩

/-- **The choice is marked.** `b63gP_family_isMarked` from `b63gP_exists` and the choice
property of `b63gP_family`. -/
example : b63gP_IsMarked b63gP_family ∧ Nonempty b63gP_family.S :=
  @Classical.epsilon_spec g32h_PrymFamily (fun F ↦ b63gP_IsMarked F ∧ Nonempty F.S)
    b63gP_exists

/-- **The tuple pinning from the marking.** `b63gP_family_tuple` from `b63gP_family_isMarked`. -/
example (s : b63gP_family.S) : b63gP_family.tuple s = b63g5_tuple := by
  obtain ⟨_, _, _, _, _, _, _, -, _, _, _, _, _, _, _, _, _, _, _, _, _, _, -, -, -, -, -, -, -,
    _, _, _, _, _, _, _, _, _, _, _, j, hj⟩ := b63gP_family_isMarked.1
  simpa using (hj (j.symm s)).1

/-- **Non-degeneracy of `b63gP_family`.** Its index type is nonempty, so it is not the empty
family (every field of which is vacuous); every fibre is a sixfold with Hodge numbers `(3, 3)`,
not a rank-zero object; and no entry of its tuple is the identity matrix. -/
example : Nonempty b63gP_family.S ∧ b63gP_family ≠ b63gP_emptyFamily ∧
    (∀ s, dim (b63gP_family.fiber s).X.left = 6 ∧ g32h_h10 (b63gP_family.fiber s) = 3 ∧
      g32h_h01 (b63gP_family.fiber s) = 3) ∧
    ∀ (s : b63gP_family.S) (i : Fin 13), b63gP_family.tuple s i ≠ 1 := by
  refine ⟨b63gP_family_isMarked.2, fun h ↦ ?_, fun s ↦ ⟨(g32h_fiber_polarized _ s).dim_eq,
    g32h_h10_eq_three _ s⟩, fun s i hi ↦ ?_⟩
  · have hne := b63gP_family_isMarked.2
    rw [h] at hne
    exact hne.elim Empty.elim
  · rw [b63gP_family_tuple s] at hi
    have h1 : b4b_root i = 1 :=
      Subtype.val_injective (hi.trans (map_one b4b_toMatrix).symm)
    have h3 := b63_root_order i
    rw [h1, orderOf_one] at h3
    split_ifs at h3 <;> omega

/-- The binder `hF : F.univ = b60b_univ` of the S7 statements is satisfiable: the concrete
universal family of `UniversalFamilyCover.lean`. -/
example : ∃ F : g32m_UniversalFamily, F.univ = b60b_univ :=
  ⟨{ univ := b60b_univ, member := b60b_member, cover := b60c_cover }, rfl⟩

/-! ## The S7 bundles with `P` fixed

Each bundle type-checks with `P := b63gP_family` and its field `spread` derived by S7. -/

/-- `g32a_premises` with `P := b63gP_family` and `spread := hk7_spread`. -/
example (F : g32m_UniversalFamily) (hF : F.univ = b60b_univ)
    (h46 : g32s_Prop46 b63gP_family) (R : g32r_PeriodMap F b63gP_family)
    (hpol : ∀ s, g32d_ParabolicPolarization (g32h_fiber_polarized b63gP_family s))
    (transport : ∀ P Q, g32t_KIsog P Q → (g32t_WeilAlg P ↔ g32t_WeilAlg Q)) :
    ∃ B : g32a_premises, B.F = F ∧ B.P = b63gP_family :=
  ⟨{ F, P := b63gP_family, h46, R, hpol, transport
     spread := hk7_spread F hF b63gP_family h46 R fun p hp h => by
       have hp' : g32t_KIsog (b63gP_family.fiber p.2) (F.univ p.1) := by rw [hF]; exact hp
       have := (transport _ _ hp').1 h
       rwa [hF] at this }, rfl, rfl⟩

/-- `g32n_premises` with `P := b63gP_family` and `spread := hk7_spread_of_members`. -/
example (F : g32m_UniversalFamily) (hF : F.univ = b60b_univ)
    (h46 : g32s_Prop46 b63gP_family) (R : g32r_PeriodMap F b63gP_family)
    (hpol : ∀ s, g32d_ParabolicPolarization (g32h_fiber_polarized b63gP_family s))
    (reverse : ∀ P Q, g32t_IsMember P → g32t_IsMember Q → g32t_KIsog P Q → g32t_KIsog Q P) :
    ∃ B : g32n_premises, B.F = F ∧ B.P = b63gP_family :=
  ⟨{ F, P := b63gP_family, h46, R, hpol, reverse
     spread := hk7_spread_of_members F hF b63gP_family h46 R hpol reverse }, rfl, rfl⟩

/-- `qinv_premises` with `P := b63gP_family` and `spread := hk7_spread_of_witness`. -/
example (F : g32m_UniversalFamily) (hF : F.univ = b60b_univ)
    (h46 : g32s_Prop46 b63gP_family) (R : g32r_PeriodMap F b63gP_family)
    (hpol : ∀ s, g32d_ParabolicPolarization (g32h_fiber_polarized b63gP_family s))
    (qinv : qinv_premise) :
    ∃ B : qinv_premises, B.F = F ∧ B.P = b63gP_family :=
  ⟨{ F, P := b63gP_family, h46, R, hpol, qinv
     spread := hk7_spread_of_witness F hF b63gP_family h46 R
       fun _ _ f hf hi => qinv _ _ f hf hi }, rfl, rfl⟩

/-! ## Chain checks toward G32 Theorem A -/

/-- **`b63gP_theoremA_of_transport` from `b63gP_theoremA`** with `spread := hk7_spread`. -/
example (F : g32m_UniversalFamily) (hF : F.univ = b60b_univ)
    (h46 : g32s_Prop46 b63gP_family) (R : g32r_PeriodMap F b63gP_family)
    (hpol : ∀ s, g32d_ParabolicPolarization (g32h_fiber_polarized b63gP_family s))
    (transport : ∀ P Q, g32t_KIsog P Q → (g32t_WeilAlg P ↔ g32t_WeilAlg Q))
    (A : Over (Spec ↧ℂ))
    [GrpObj A] [IsCommMonObj A] [IsIntegral A.left] [Smooth A.hom] [IsProjective A.hom]
    (W : letI := (torusCohomology_cupProductOf A).finite
      HodgeBlocks.WeilAction
        (abelianVarietyCohomologyOf (finiteBetti_abelian A)
          (spec_bettiDeRhamIso_abelian A) (hodgeDecomposition_of_abelian A)
          (torusCohomology_cupProductOf A)).weight1 3)
    (pol : HQ A 2) : G32TheoremAStatement A W pol :=
  b63gP_theoremA F h46 R hpol
    (hk7_spread F hF b63gP_family h46 R fun p hp h => by
      have hp' : g32t_KIsog (b63gP_family.fiber p.2) (F.univ p.1) := by rw [hF]; exact hp
      have := (transport _ _ hp').1 h
      rwa [hF] at this) transport A W pol

/-- **`b63gP_theoremA_of_reverse` from the `g32n_premises` bundle.** -/
example (F : g32m_UniversalFamily) (hF : F.univ = b60b_univ)
    (h46 : g32s_Prop46 b63gP_family) (R : g32r_PeriodMap F b63gP_family)
    (hpol : ∀ s, g32d_ParabolicPolarization (g32h_fiber_polarized b63gP_family s))
    (reverse : ∀ P Q, g32t_IsMember P → g32t_IsMember Q → g32t_KIsog P Q → g32t_KIsog Q P)
    (A : Over (Spec ↧ℂ))
    [GrpObj A] [IsCommMonObj A] [IsIntegral A.left] [Smooth A.hom] [IsProjective A.hom]
    (W : letI := (torusCohomology_cupProductOf A).finite
      HodgeBlocks.WeilAction
        (abelianVarietyCohomologyOf (finiteBetti_abelian A)
          (spec_bettiDeRhamIso_abelian A) (hodgeDecomposition_of_abelian A)
          (torusCohomology_cupProductOf A)).weight1 3)
    (pol : HQ A 2) : G32TheoremAStatement A W pol :=
  g32n_theoremA_of_premises
    { F, P := b63gP_family, h46, R, hpol, reverse
      spread := hk7_spread_of_members F hF b63gP_family h46 R hpol reverse } A W pol

/-- **`b63gP_theoremA_of_qinv` from the `qinv_premises` bundle.** -/
example (F : g32m_UniversalFamily) (hF : F.univ = b60b_univ)
    (h46 : g32s_Prop46 b63gP_family) (R : g32r_PeriodMap F b63gP_family)
    (hpol : ∀ s, g32d_ParabolicPolarization (g32h_fiber_polarized b63gP_family s))
    (qinv : qinv_premise)
    (A : Over (Spec ↧ℂ))
    [GrpObj A] [IsCommMonObj A] [IsIntegral A.left] [Smooth A.hom] [IsProjective A.hom]
    (W : letI := (torusCohomology_cupProductOf A).finite
      HodgeBlocks.WeilAction
        (abelianVarietyCohomologyOf (finiteBetti_abelian A)
          (spec_bettiDeRhamIso_abelian A) (hodgeDecomposition_of_abelian A)
          (torusCohomology_cupProductOf A)).weight1 3)
    (pol : HQ A 2) : G32TheoremAStatement A W pol :=
  qinv_g32_theoremA_of_premises
    { F, P := b63gP_family, h46, R, hpol, qinv
      spread := hk7_spread_of_witness F hF b63gP_family h46 R
        fun _ _ f hf hi => qinv _ _ f hf hi } A W pol

end HodgeLean.Foundations.Program
