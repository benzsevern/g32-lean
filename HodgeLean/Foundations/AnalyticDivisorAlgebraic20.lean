import HodgeLean.Foundations.AnalyticDivisorAlgebraic20Proofs

/-! # Analytic divisor gluing, stage 20

This stage freezes regular-locus connectedness, component identification, relative local
finiteness, and constancy of multiplicity.  It also supplies weighted topological carrier data. The analytic carrier construction and
canonical component quotient are expressible but deferred.
HC no distance; AV milestone no distance.
-/

noncomputable section
namespace HodgeLean.Foundations.AnalyticDivisorAlgebraic20

open Filter Set Topology
open HodgeLean.Foundations.AnalyticDivisorAlgebraic18
open HodgeLean.Foundations.AnalyticDivisorAlgebraic19
open HodgeLean.Foundations.AnalyticDivisorAlgebraic14
open HodgeLean.Foundations.AnalyticDivisorAlgebraic6
open HodgeLean.Foundations.AnalyticDivisorAlgebraic7
open HodgeLean.Foundations.AnalyticDivisorAlgebraic18

/-- The regular locus of an irreducible analytic hypersurface germ is dense and connected after
shrinking around its zero.
Source: Gunning--Rossi, *Analytic Functions of Several Complex Variables*, III.A, Theorem 4;
Chirka, *Complex Analytic Sets*, §5.1.  This does not use the stage-eighteen Nullstellensatz. -/
theorem gaga20_regular_locus {n : ℕ} (p : Fin n → ℂ) (f : (Fin n → ℂ) → ℂ)
    (hf : AnalyticAt ℂ f p) (hf0 : f p = 0) (hirr : IsIrreducibleAt f p) :
    ∃ W ∈ nhds p, IsOpen W ∧ p ∈ W ∧
      closure (gaga20_regularZero f ∩ W) = {x | f x = 0} ∩ closure W ∧
      IsConnected (gaga20_regularZero f ∩ W) :=
  gaga20_regular_locus_aux p f hf hf0 hirr

/-- Analytic hypersurface carriers with connected dense regular parts agree throughout `U`
if they share a nonempty relatively open regular patch. Density is within each carrier.
Source: Chirka, *Complex Analytic Sets*, §5.1 (irreducible components and regular parts). -/
theorem gaga20_component_identification {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [FiniteDimensional ℂ E] (U W : Set E) (P Q : E → ℂ)
    (hU : IsOpen U) (hW : IsOpen W) (hWU : W ⊆ U)
    (hP : AnalyticOnNhd ℂ P U) (hQ : AnalyticOnNhd ℂ Q U)
    (hcP : IsConnected (gaga20_regularZero P ∩ U))
    (hcQ : IsConnected (gaga20_regularZero Q ∩ U))
    (hdP : closure (gaga20_regularZero P ∩ U) ∩ U = {x ∈ U | P x = 0})
    (hdQ : closure (gaga20_regularZero Q ∩ U) ∩ U = {x ∈ U | Q x = 0})
    (hne : (gaga20_regularZero P ∩ W).Nonempty)
    (hpatch : gaga20_regularZero P ∩ W = gaga20_regularZero Q ∩ W) :
    {x ∈ U | P x = 0} = {x ∈ U | Q x = 0} :=
  gaga20_component_identification_aux U W P Q hU hW hWU hP hQ hcP hcQ hdP hdQ hne hpatch

/-- A family whose members meet only finitely many indices on a neighbourhood of every point
of `U` is locally finite in the subspace `U`.
Source: Bourbaki, *General Topology*, Ch. I, §9, no. 2. -/
theorem gaga20_relative_local_finiteness {E : Type*} [TopologicalSpace E]
    {U : Set E} {A : Type*} (C : A → Set E)
    (hU : IsOpen U)
    (hlocal : ∀ x ∈ U, ∃ W ∈ nhds x, {a | (C a ∩ W).Nonempty}.Finite) :
    LocallyFinite fun a ↦ ((↑) : U → E) ⁻¹' C a :=
  gaga20_relative_local_finiteness_aux C hU hlocal

/-- A locally constant multiplicity on a connected regular component is constant there.
Source: Chirka, *Complex Analytic Sets*, §2.3 (multiplicity on the regular locus). -/
theorem gaga20_multiplicity_constancy {E : Type*} [TopologicalSpace E]
    {A : Type*} (m : A → E → ℕ)
    (R : A → Set E)
    (hconn : ∀ a, IsConnected (R a))
    (hloc : ∀ a x, x ∈ R a → ∃ W ∈ nhds x, ∀ y ∈ W ∩ R a, m a y = m a x) :
    ∀ a x, x ∈ R a → ∀ y, y ∈ R a → m a y = m a x :=
  gaga20_multiplicity_constancy_aux m R hconn hloc

-- The irreducible coordinate axis constructs every premise of the regular-locus statement.
example : ∃ W ∈ nhds (0 : Fin 2 → ℂ), IsOpen W ∧ 0 ∈ W ∧
    closure (gaga20_regularZero gaga18_axis ∩ W) =
      {x | gaga18_axis x = 0} ∩ closure W ∧
    IsConnected (gaga20_regularZero gaga18_axis ∩ W) := by
  exact gaga20_regular_locus 0 gaga18_axis gaga18_concrete_data.1
    (by simp [gaga18_axis]) gaga18_concrete_data.2.1

-- The irreducible cusp constructs the singular test for the same statement.
example : ∃ W ∈ nhds (0 : Fin 2 → ℂ), IsOpen W ∧ 0 ∈ W ∧
    closure (gaga20_regularZero gaga18_cusp ∩ W) =
      {x | gaga18_cusp x = 0} ∩ closure W ∧
    IsConnected (gaga20_regularZero gaga18_cusp ∩ W) := by
  exact gaga20_regular_locus 0 gaga18_cusp gaga18_cusp_irreducible.1
    (by simp [gaga18_cusp]) gaga18_cusp_irreducible.2

-- The empty indexed family constructs the degenerate relative-finiteness input.
example {E : Type*} [TopologicalSpace E] (U : Set E) (hU : IsOpen U) :
    LocallyFinite (fun a : Empty ↦ ((↑) : U → E) ⁻¹' (a.elim : Set E)) := by
  apply gaga20_relative_local_finiteness (U := U) _ hU
  intro x _
  refine ⟨univ, univ_mem, ?_⟩
  have heq : {a : Empty | ((a.elim : Set E) ∩ univ).Nonempty} = ∅ := by
    ext a
    exact a.elim
  rw [heq]
  exact finite_empty

-- The empty topological weighted family.
example {E : Type*} [TopologicalSpace E] (U : Set E) :
    gaga20_WeightedTopologicalFamily E U where
  Component := Empty
  component := fun a ↦ a.elim
  multiplicity := fun a ↦ a.elim
  multiplicity_pos := fun a ↦ a.elim
  component_subset := fun a ↦ a.elim
  locallyFinite := locallyFinite_of_finite _

-- A single closed point with weight one is a topological weighted family.
example {E : Type*} [TopologicalSpace E] [T1Space E] (x : E) :
    gaga20_WeightedTopologicalFamily E {x} where
  Component := Unit
  component _ := ⟨{x}, isClosed_singleton, singleton_nonempty x,
    isPreirreducible_singleton⟩
  multiplicity _ := 1
  multiplicity_pos _ := Nat.zero_lt_one
  component_subset _ := subset_rfl
  locallyFinite := locallyFinite_of_finite _

-- Both factors of the crossing, separately, have connected dense regular shrinkings.
example (a : Fin 2) : ∃ W ∈ nhds (0 : Fin 2 → ℂ), IsOpen W ∧ 0 ∈ W ∧
    closure (gaga20_regularZero (fun z ↦ z a) ∩ W) =
      {z | z a = 0} ∩ closure W ∧
    IsConnected (gaga20_regularZero (fun z ↦ z a) ∩ W) :=
  gaga20_regular_locus 0 (fun z ↦ z a) (gaga18_coordinate_data.1 a).1
    rfl (gaga18_coordinate_data.1 a).2

-- A nonempty singleton index family instantiates relative local finiteness.
example : LocallyFinite (fun _ : Unit ↦
    ((↑) : ↥(univ : Set ℂ) → ℂ) ⁻¹' ({0} : Set ℂ)) := by
  apply gaga20_relative_local_finiteness _ isOpen_univ
  intro x _
  exact ⟨univ, univ_mem, Set.toFinite _⟩

-- Nonempty connected domain and positive, constant multiplicity.
example : ∀ x : ℂ, x ∈ (univ : Set ℂ) → ∀ y : ℂ, y ∈ (univ : Set ℂ) →
    (fun _ : ℂ ↦ (2 : ℕ)) y = (fun _ : ℂ ↦ (2 : ℕ)) x := by
  exact gaga20_multiplicity_constancy (A := Unit) (fun _ _ ↦ 2) (fun _ ↦ univ)
    (fun _ ↦ isConnected_univ) (fun _ _ _ ↦ ⟨univ, univ_mem, fun _ _ ↦ rfl⟩) ()

-- Carrier intersection is an operation on sets, including empty intersections.
example : let D : gaga20_WeightedTopologicalFamily ℂ {0} :=
    ⟨Unit, fun _ ↦ ⟨{0}, isClosed_singleton, singleton_nonempty 0,
      isPreirreducible_singleton⟩, fun _ ↦ 2, fun _ ↦ by decide,
      fun _ ↦ subset_rfl, locallyFinite_of_finite _⟩
    D.carrierIntersection {0} () = {0} ∧ D.carrierIntersection ∅ () = ∅ := by
  simp [gaga20_WeightedTopologicalFamily.carrierIntersection]

-- The old counterexample cannot supply any nonempty common regular patch.
example (W : Set ℂ) : ¬ (gaga20_regularZero (fun _ : ℂ ↦ (1 : ℂ)) ∩ W).Nonempty := by
  rintro ⟨z, hz, _⟩
  exact one_ne_zero hz.1

/-- Zero-germ containment gives association of irreducible equations through the analytic
Nullstellensatz; no association is assumed.
Source: `spec_hypersurface_nullstellensatz`, Gunning--Rossi III.A, Theorem 1. -/
theorem gaga20_match_of_zero_containment {n : ℕ} (p : Fin n → ℂ)
    (P Q : (Fin n → ℂ) → ℂ) (hP : AnalyticAt ℂ P p) (hQ : AnalyticAt ℂ Q p)
    (hiP : IsIrreducibleAt P p) (hiQ : IsIrreducibleAt Q p)
    (hzero : ∀ᶠ z in nhds p, P z = 0 → Q z = 0) : AreAssociatedAt Q P p :=
  gaga20_match_of_zero_containment_aux p P Q hP hQ hiP hiQ hzero

/-- Nearby factors from distinct anchor groups have equal local divisors to distinct ambient
members. This transports all their coefficients, using stages seventeen through nineteen.
Source: `spec_nearby_distinct_group_matching`, `spec_nearby_factor_matching`, and
`spec_localDivisorAt_eq_of_areAssociatedAt`. -/
theorem gaga20_nearby_distinct_divisors {n r : ℕ} {ι : Type*}
    {U : Set ((Fin n → ℂ) × ℂ)} {V : ι → Set ((Fin n → ℂ) × ℂ)}
    {f : ι → (Fin n → ℂ) × ℂ → ℂ} (hD : IsLocalDivisorData U V f)
    (i : ι) {p : (Fin n → ℂ) × ℂ}
    {v : (Fin n → ℂ) × ℂ → ℂ} {P : Fin r → (Fin n → ℂ) × ℂ → ℂ}
    {b : Fin r → ℕ} (hvP : AnalyticAt ℂ v p) (hv0P : v p ≠ 0)
    (hPp : ∀ a, AnalyticAt ℂ (P a) p) (hirr : ∀ a, IsIrreducibleAt (P a) p)
    (hb : ∀ a, 0 < b a) (hcop : Pairwise (fun a c ↦ IsCoprimeAt (P a) (P c) p)) :
    ∀ᶠ q in nhds p, ∀ (N : Set ((Fin n → ℂ) × ℂ)), IsOpen N → N ∈ nhds p →
      N ⊆ V i → q ∈ N → AnalyticOnNhd ℂ v N →
      (∀ a, AnalyticOnNhd ℂ (P a) N) →
      (∀ y ∈ N, f i y = v y * ∏ a, P a y ^ b a) →
      ∀ (a c : Fin r), a ≠ c → P a q = 0 → P c q = 0 →
      ∀ (ka kc t : ℕ) (ua uc w : (Fin n → ℂ) × ℂ → ℂ)
        (Qa : Fin ka → (Fin n → ℂ) × ℂ → ℂ)
        (Qc : Fin kc → (Fin n → ℂ) × ℂ → ℂ)
        (R : Fin t → (Fin n → ℂ) × ℂ → ℂ)
        (da : Fin ka → ℕ) (dc : Fin kc → ℕ) (e : Fin t → ℕ),
        AnalyticAt ℂ ua q → ua q ≠ 0 →
        (∀ j, AnalyticAt ℂ (Qa j) q ∧ IsIrreducibleAt (Qa j) q ∧ 0 < da j) →
        Pairwise (fun j l ↦ IsCoprimeAt (Qa j) (Qa l) q) →
        (P a =ᶠ[nhds q] fun y ↦ ua y * ∏ j, Qa j y ^ da j) →
        AnalyticAt ℂ uc q → uc q ≠ 0 →
        (∀ j, AnalyticAt ℂ (Qc j) q ∧ IsIrreducibleAt (Qc j) q ∧ 0 < dc j) →
        Pairwise (fun j l ↦ IsCoprimeAt (Qc j) (Qc l) q) →
        (P c =ᶠ[nhds q] fun y ↦ uc y * ∏ j, Qc j y ^ dc j) →
        AnalyticAt ℂ w q → w q ≠ 0 →
        (∀ l, AnalyticAt ℂ (R l) q ∧ IsIrreducibleAt (R l) q ∧ 0 < e l) →
        Pairwise (fun l s ↦ IsCoprimeAt (R l) (R s) q) →
        (f i =ᶠ[nhds q] fun y ↦ w y * ∏ l, R l y ^ e l) →
        ∀ ja jc, ∃ la lc, localDivisorAt n (Qa ja) q = localDivisorAt n (R la) q ∧
          localDivisorAt n (Qc jc) q = localDivisorAt n (R lc) q ∧ la ≠ lc :=
  gaga20_nearby_distinct_divisors_aux hD i hvP hv0P hPp hirr hb hcop

/-- On a common neighbourhood the anchor groups stay coprime and their clean regular
multiplicities equal their fixed exponents. This derives local constancy from factorization;
it does not assume a locally constant weight function. Transverse directions can vary.
Source: `gaga19_pair_propagation_product` (stage-eighteen coprimality propagation),
`spec_transverseOrder_of_decomposition`, and `spec_localDivisor_multiplicity_eq_transverseOrder`.
The last theorem identifies transverse order with the canonical local-divisor coefficient. -/
theorem gaga20_clean_multiplicity {n k : ℕ}
    {f u : (Fin n → ℂ) × ℂ → ℂ}
    {P : Fin k → (Fin n → ℂ) × ℂ → ℂ} {b : Fin k → ℕ}
    (hu : AnalyticAt ℂ u 0) (hu0 : u 0 ≠ 0)
    (hP : ∀ a, AnalyticAt ℂ (P a) 0)
    (hiP : ∀ a, IsIrreducibleAt (P a) 0)
    (hb : ∀ a, 0 < b a)
    (hcop : Pairwise (fun a c ↦ IsCoprimeAt (P a) (P c) 0))
    (hfac : f =ᶠ[nhds 0] fun y ↦ u y * ∏ a, P a y ^ b a) :
    ∃ N, IsOpen N ∧ (0 : (Fin n → ℂ) × ℂ) ∈ N ∧
      (∀ q ∈ N, Pairwise (fun a c ↦ IsCoprimeAt (P a) (P c) q)) ∧
      ∀ q ∈ N, ∀ a, P a q = 0 → (∀ c, c ≠ a → P c q ≠ 0) →
        ∀ v : (Fin n → ℂ) × ℂ, fderiv ℂ (P a) q v ≠ 0 →
          analyticOrderAt (fun t : ℂ ↦ f (q + t • v)) 0 = b a :=
  gaga20_clean_multiplicity_aux hu hu0 hP hiP hb hcop hfac

/-- Distinct anchor factors cannot acquire zero-germ containment at a nearby point where
the selected factor remains irreducible. This converts coprimality into a carrier obstruction.
Source: `spec_eventually_pairwise_coprime` and `spec_hypersurface_nullstellensatz`. -/
theorem gaga20_no_zero_germ_containment {n k : ℕ} (p : Fin n → ℂ)
    (P : Fin k → (Fin n → ℂ) → ℂ)
    (hP : ∀ a, AnalyticAt ℂ (P a) p) (hiP : ∀ a, IsIrreducibleAt (P a) p)
    (hcop : Pairwise (fun a c ↦ IsCoprimeAt (P a) (P c) p)) :
    ∀ᶠ q in nhds p, ∀ a c, a ≠ c → IsIrreducibleAt (P a) q →
      ¬ (∀ᶠ z in nhds q, P a z = 0 → P c z = 0) :=
  gaga20_no_zero_germ_containment_aux p P hP hiP hcop

end HodgeLean.Foundations.AnalyticDivisorAlgebraic20
