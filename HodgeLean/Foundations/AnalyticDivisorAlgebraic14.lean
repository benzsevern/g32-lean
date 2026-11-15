import HodgeLean.Foundations.AnalyticDivisorAlgebraic14Proofs

/-! # Local divisor data on an open set: frozen specification

This stage states the first glueing layer for analytic divisors with explicit covers. Local
divisor data on an open set `U` consists of open charts covering `U` and local equations, analytic
and not identically zero near any point, associated by nonvanishing analytic germs on overlaps.
Claimed, by implication from that association and from stages seven, eight, nine and thirteen:
the zero sets of two local equations agree on overlaps, so the support is well defined and
relatively closed in `U`; the stage-eight local divisor read at a point of an overlap does not
depend on the chart; it is nonzero exactly at points of the support; restriction to a refinement
is local divisor data with the same support and multiplicities; and at every point of the support
some irreducible decomposition of the local equation exists, each of whose factors has clean
regular points in the support arbitrarily close to that point.

Not claimed: a sheaf of divisors, equivalence of two families of data by common refinement,
meromorphic data, a single defining function on `U` (Cousin II), a divisor on a complex manifold,
Chow's theorem, GAGA, algebraicity, or a cycle class.

HC no distance; AV milestone no distance.
-/

noncomputable section
namespace HodgeLean.Foundations.AnalyticDivisorAlgebraic14

open Filter Set Topology
open HodgeLean.Foundations.AnalyticDivisorAlgebraic6
open HodgeLean.Foundations.AnalyticDivisorAlgebraic7
open HodgeLean.Foundations.AnalyticDivisorAlgebraic8

/-- On an overlap of two charts, the two local equations vanish at the same points.
Source: Griffiths--Harris, *Principles of Algebraic Geometry*, Ch. 1 §1; a germ associated by a
nonvanishing analytic factor has the same zeros. -/
theorem spec_zero_iff_on_overlap {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {ι : Type*} {U : Set E} {V : ι → Set E} {f : ι → E → ℂ}
    (hD : IsLocalDivisorData U V f) (i j : ι) (x : E) (hi : x ∈ V i) (hj : x ∈ V j) :
    f i x = 0 ↔ f j x = 0 :=
  spec_zero_iff_on_overlap_aux hD i j x hi hj

example {ι : Type*} {U : Set ℂ} {V : ι → Set ℂ} {f : ι → ℂ → ℂ}
    (hD : IsLocalDivisorData U V f) (i : ι) (x : ℂ) (hi : x ∈ V i) :
    f i x = 0 ↔ f i x = 0 :=
  spec_zero_iff_on_overlap hD i i x hi hi

/-- Membership in the support may be tested in any chart containing the point.
Source: Griffiths--Harris, *Principles of Algebraic Geometry*, Ch. 1 §1. -/
theorem spec_mem_localDivisorSupport_iff {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] {ι : Type*} {U : Set E} {V : ι → Set E} {f : ι → E → ℂ}
    (hD : IsLocalDivisorData U V f) (i : ι) (x : E) (hi : x ∈ V i) :
    x ∈ localDivisorSupport V f ↔ f i x = 0 :=
  spec_mem_localDivisorSupport_iff_aux hD i x hi

example {ι : Type*} {U : Set ℂ} {V : ι → Set ℂ} {f : ι → ℂ → ℂ}
    (hD : IsLocalDivisorData U V f) (i : ι) (x : ℂ) (hi : x ∈ V i) (hx : f i x ≠ 0) :
    x ∉ localDivisorSupport V f :=
  fun h ↦ hx ((spec_mem_localDivisorSupport_iff hD i x hi).mp h)

/-- The support lies in `U` and is closed in the subspace topology of `U`.
Source: Griffiths--Harris, *Principles of Algebraic Geometry*, Ch. 1 §1; continuity of analytic
functions. -/
theorem spec_isClosed_localDivisorSupport {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] {ι : Type*} {U : Set E} {V : ι → Set E} {f : ι → E → ℂ}
    (hD : IsLocalDivisorData U V f) :
    localDivisorSupport V f ⊆ U ∧
      IsClosed (((↑) : U → E) ⁻¹' localDivisorSupport V f) :=
  spec_isClosed_localDivisorSupport_aux hD

example {ι : Type*} {V : ι → Set ℂ} {f : ι → ℂ → ℂ}
    (hD : IsLocalDivisorData univ V f) :
    IsClosed (((↑) : ↥(univ : Set ℂ) → ℂ) ⁻¹' localDivisorSupport V f) :=
  (spec_isClosed_localDivisorSupport hD).2

/-- Analytic functions associated at `p` have the same translated local divisor at `p`.
Source: Gunning--Rossi, *Analytic Functions of Several Complex Variables*, II.B, Definition 1;
`spec_localDivisor_associated`. -/
theorem spec_localDivisorAt_eq_of_areAssociatedAt {n : ℕ}
    {f g : (Fin n → ℂ) × ℂ → ℂ} {p : (Fin n → ℂ) × ℂ}
    (hf : AnalyticAt ℂ f p) (hg : AnalyticAt ℂ g p) (h : AreAssociatedAt f g p) :
    localDivisorAt n f p = localDivisorAt n g p :=
  spec_localDivisorAt_eq_of_areAssociatedAt_aux hf hg h

example {n : ℕ} {f g : (Fin n → ℂ) × ℂ → ℂ} {p : (Fin n → ℂ) × ℂ}
    (hf : AnalyticAt ℂ f p) (hg : AnalyticAt ℂ g p) (h : AreAssociatedAt f g p)
    (c : LocalFactorClass n) :
    localDivisorAt n f p c = localDivisorAt n g p c := by
  rw [spec_localDivisorAt_eq_of_areAssociatedAt hf hg h]

/-- A function analytic and nonvanishing at `p` has zero local divisor there: units have
multiplicity zero along every component.
Source: Griffiths--Harris, *Principles of Algebraic Geometry*, Ch. 1 §1;
`spec_localDivisor_unit`. -/
theorem spec_localDivisorAt_eq_zero_of_ne_zero {n : ℕ}
    {f : (Fin n → ℂ) × ℂ → ℂ} {p : (Fin n → ℂ) × ℂ}
    (hf : AnalyticAt ℂ f p) (hp : f p ≠ 0) :
    localDivisorAt n f p = 0 :=
  spec_localDivisorAt_eq_zero_of_ne_zero_aux hf hp

-- The constant `1`, at any point and for `n = 0`.
example (p : (Fin 0 → ℂ) × ℂ) : localDivisorAt 0 (fun _ ↦ 1) p = 0 :=
  spec_localDivisorAt_eq_zero_of_ne_zero analyticAt_const one_ne_zero

/-- At a point of an overlap the local divisor computed from either chart's equation is the same,
so every component multiplicity is independent of the chart.
Source: Griffiths--Harris, *Principles of Algebraic Geometry*, Ch. 1 §1;
`spec_localDivisorAt_eq_of_areAssociatedAt`. -/
theorem spec_localDivisorAt_eq_on_overlap {n : ℕ} {ι : Type*}
    {U : Set ((Fin n → ℂ) × ℂ)} {V : ι → Set ((Fin n → ℂ) × ℂ)}
    {f : ι → (Fin n → ℂ) × ℂ → ℂ} (hD : IsLocalDivisorData U V f)
    (i j : ι) (p : (Fin n → ℂ) × ℂ) (hi : p ∈ V i) (hj : p ∈ V j) :
    localDivisorAt n (f i) p = localDivisorAt n (f j) p :=
  spec_localDivisorAt_eq_on_overlap_aux hD i j p hi hj

example {n : ℕ} {ι : Type*} {U : Set ((Fin n → ℂ) × ℂ)} {V : ι → Set ((Fin n → ℂ) × ℂ)}
    {f : ι → (Fin n → ℂ) × ℂ → ℂ} (hD : IsLocalDivisorData U V f)
    (i j : ι) (p : (Fin n → ℂ) × ℂ) (hi : p ∈ V i) (hj : p ∈ V j) (c : LocalFactorClass n) :
    localDivisorAt n (f i) p c = localDivisorAt n (f j) p c := by
  rw [spec_localDivisorAt_eq_on_overlap hD i j p hi hj]

/-- The local divisor at a point of a chart is nonzero exactly when the point lies in the support.
Source: Gunning--Rossi, *Analytic Functions of Several Complex Variables*, II.B, Theorems 3--6;
Griffiths--Harris, *Principles of Algebraic Geometry*, Ch. 1 §1. -/
theorem spec_localDivisorAt_ne_zero_iff {n : ℕ} {ι : Type*}
    {U : Set ((Fin n → ℂ) × ℂ)} {V : ι → Set ((Fin n → ℂ) × ℂ)}
    {f : ι → (Fin n → ℂ) × ℂ → ℂ} (hD : IsLocalDivisorData U V f)
    (i : ι) (p : (Fin n → ℂ) × ℂ) (hi : p ∈ V i) :
    localDivisorAt n (f i) p ≠ 0 ↔ p ∈ localDivisorSupport V f :=
  spec_localDivisorAt_ne_zero_iff_aux hD i p hi

example {n : ℕ} {ι : Type*} {U : Set ((Fin n → ℂ) × ℂ)} {V : ι → Set ((Fin n → ℂ) × ℂ)}
    {f : ι → (Fin n → ℂ) × ℂ → ℂ} (hD : IsLocalDivisorData U V f)
    (i : ι) (p : (Fin n → ℂ) × ℂ) (hi : p ∈ V i) (hp : f i p = 0) :
    localDivisorAt n (f i) p ≠ 0 :=
  (spec_localDivisorAt_ne_zero_iff hD i p hi).mpr ⟨i, hi, hp⟩

/-- Restricting local divisor data to an open refinement of its cover gives local divisor data on
the same open set.
Source: Griffiths--Harris, *Principles of Algebraic Geometry*, Ch. 1 §1 (refinement of the
defining cover). -/
theorem spec_refinement_isLocalDivisorData {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] {ι κ : Type*} {U : Set E} {V : ι → Set E} {f : ι → E → ℂ}
    (hD : IsLocalDivisorData U V f) (W : κ → Set E) (τ : κ → ι)
    (hW : ∀ k, IsOpen (W k)) (hWU : (⋃ k, W k) = U) (hWV : ∀ k, W k ⊆ V (τ k)) :
    IsLocalDivisorData U W (fun k ↦ f (τ k)) :=
  spec_refinement_isLocalDivisorData_aux hD W τ hW hWU hWV

-- The trivial refinement.
example {ι : Type*} {U : Set ℂ} {V : ι → Set ℂ} {f : ι → ℂ → ℂ}
    (hD : IsLocalDivisorData U V f) : IsLocalDivisorData U V (fun i ↦ f (id i)) :=
  spec_refinement_isLocalDivisorData hD V id hD.1 hD.2.1 fun _ ↦ subset_rfl

/-- A refinement has the same support.
Source: Griffiths--Harris, *Principles of Algebraic Geometry*, Ch. 1 §1. -/
theorem spec_refinement_support {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] {ι κ : Type*} {U : Set E} {V : ι → Set E} {f : ι → E → ℂ}
    (hD : IsLocalDivisorData U V f) (W : κ → Set E) (τ : κ → ι)
    (hWU : (⋃ k, W k) = U) (hWV : ∀ k, W k ⊆ V (τ k)) :
    localDivisorSupport W (fun k ↦ f (τ k)) = localDivisorSupport V f :=
  spec_refinement_support_aux hD W τ hWU hWV

example {ι : Type*} {U : Set ℂ} {V : ι → Set ℂ} {f : ι → ℂ → ℂ}
    (hD : IsLocalDivisorData U V f) :
    localDivisorSupport V (fun i ↦ f (id i)) = localDivisorSupport V f :=
  spec_refinement_support hD V id hD.2.1 fun _ ↦ subset_rfl

/-- A refinement has the same multiplicities: at a point of a refining chart and of an original
chart, the two local divisors agree.
Source: Griffiths--Harris, *Principles of Algebraic Geometry*, Ch. 1 §1. -/
theorem spec_refinement_localDivisorAt {n : ℕ} {ι κ : Type*}
    {U : Set ((Fin n → ℂ) × ℂ)} {V : ι → Set ((Fin n → ℂ) × ℂ)}
    {f : ι → (Fin n → ℂ) × ℂ → ℂ} (hD : IsLocalDivisorData U V f)
    (W : κ → Set ((Fin n → ℂ) × ℂ)) (τ : κ → ι) (hWV : ∀ k, W k ⊆ V (τ k))
    (k : κ) (i : ι) (p : (Fin n → ℂ) × ℂ) (hk : p ∈ W k) (hi : p ∈ V i) :
    localDivisorAt n (f (τ k)) p = localDivisorAt n (f i) p :=
  spec_refinement_localDivisorAt_aux hD W τ hWV k i p hk hi

example {n : ℕ} {ι : Type*} {U : Set ((Fin n → ℂ) × ℂ)} {V : ι → Set ((Fin n → ℂ) × ℂ)}
    {f : ι → (Fin n → ℂ) × ℂ → ℂ} (hD : IsLocalDivisorData U V f)
    (i : ι) (p : (Fin n → ℂ) × ℂ) (hi : p ∈ V i) :
    localDivisorAt n (f (id i)) p = localDivisorAt n (f i) p :=
  spec_refinement_localDivisorAt hD V id (fun _ ↦ subset_rfl) i i p hi hi

/-- A nonzero analytic germ vanishing at an arbitrary point `p` is a unit times positive powers of
pairwise coprime irreducible analytic germs at `p`.
Source: Gunning--Rossi, *Analytic Functions of Several Complex Variables*, II.B, Theorems 3--6;
`spec_exists_irreducible_decomposition` after translation to the origin. -/
theorem spec_exists_irreducible_decomposition_at {n : ℕ}
    {f : (Fin n → ℂ) × ℂ → ℂ} {p : (Fin n → ℂ) × ℂ}
    (hf : AnalyticAt ℂ f p) (hf0 : f p = 0) (hnz : ¬ ∀ᶠ y in 𝓝 p, f y = 0) :
    ∃ k : ℕ, ∃ u : (Fin n → ℂ) × ℂ → ℂ,
      ∃ P : Fin k → (Fin n → ℂ) × ℂ → ℂ, ∃ m : Fin k → ℕ,
        AnalyticAt ℂ u p ∧ u p ≠ 0 ∧
        (∀ j, AnalyticAt ℂ (P j) p ∧ IsIrreducibleAt (P j) p ∧ 0 < m j) ∧
        Pairwise (fun j l ↦ IsCoprimeAt (P j) (P l) p) ∧
        f =ᶠ[𝓝 p] fun y ↦ u y * ∏ j, (P j y) ^ (m j) :=
  spec_exists_irreducible_decomposition_at_aux hf hf0 hnz

-- At the origin the conclusion has the shape of stage seven's decomposition.
example {n : ℕ} {f : (Fin n → ℂ) × ℂ → ℂ}
    (hf : AnalyticAt ℂ f 0) (hf0 : f 0 = 0) (hnz : ¬ ∀ᶠ y in 𝓝 0, f y = 0) :
    ∃ k : ℕ, ∃ u : (Fin n → ℂ) × ℂ → ℂ,
      ∃ P : Fin k → (Fin n → ℂ) × ℂ → ℂ, ∃ m : Fin k → ℕ,
        AnalyticAt ℂ u 0 ∧ u 0 ≠ 0 ∧
        (∀ j, AnalyticAt ℂ (P j) 0 ∧ IsIrreducibleAt (P j) 0 ∧ 0 < m j) ∧
        Pairwise (fun j l ↦ IsCoprimeAt (P j) (P l) 0) ∧
        f =ᶠ[𝓝 0] fun y ↦ u y * ∏ j, (P j y) ^ (m j) :=
  spec_exists_irreducible_decomposition_at hf hf0 hnz

/-- Given an irreducible decomposition of a chart's equation at `p`, every factor has clean
regular points, lying in the chart and in the support and avoiding the other factors, arbitrarily
close to `p`.
Source: Gunning--Rossi, Ch. III; Chirka, *Complex Analytic Sets*, §§2--5;
`spec_point_mem_closure_clean_regular_factor`. -/
theorem spec_mem_closure_clean_support_factor {n k : ℕ} {ι : Type*}
    {U : Set ((Fin n → ℂ) × ℂ)} {V : ι → Set ((Fin n → ℂ) × ℂ)}
    {f : ι → (Fin n → ℂ) × ℂ → ℂ} (hD : IsLocalDivisorData U V f)
    (i : ι) (p : (Fin n → ℂ) × ℂ) (hi : p ∈ V i)
    {u : (Fin n → ℂ) × ℂ → ℂ} {P : Fin k → (Fin n → ℂ) × ℂ → ℂ} {m : Fin k → ℕ}
    (hu : AnalyticAt ℂ u p) (hu0 : u p ≠ 0)
    (hP : ∀ j, AnalyticAt ℂ (P j) p ∧ IsIrreducibleAt (P j) p ∧ 0 < m j)
    (hcP : Pairwise (fun j l ↦ IsCoprimeAt (P j) (P l) p))
    (hfac : f i =ᶠ[𝓝 p] fun y ↦ u y * ∏ j, (P j y) ^ (m j)) (j : Fin k) :
    p ∈ closure {y | y ∈ V i ∩ localDivisorSupport V f ∧ P j y = 0 ∧
      (∀ l, l ≠ j → P l y ≠ 0) ∧ fderiv ℂ (P j) y ≠ 0} :=
  spec_mem_closure_clean_support_factor_aux hD i p hi hu hu0 hP hcP hfac j

-- The clean points found are in particular points of the support.
example {n k : ℕ} {ι : Type*}
    {U : Set ((Fin n → ℂ) × ℂ)} {V : ι → Set ((Fin n → ℂ) × ℂ)}
    {f : ι → (Fin n → ℂ) × ℂ → ℂ} (hD : IsLocalDivisorData U V f)
    (i : ι) (p : (Fin n → ℂ) × ℂ) (hi : p ∈ V i)
    {u : (Fin n → ℂ) × ℂ → ℂ} {P : Fin k → (Fin n → ℂ) × ℂ → ℂ} {m : Fin k → ℕ}
    (hu : AnalyticAt ℂ u p) (hu0 : u p ≠ 0)
    (hP : ∀ j, AnalyticAt ℂ (P j) p ∧ IsIrreducibleAt (P j) p ∧ 0 < m j)
    (hcP : Pairwise (fun j l ↦ IsCoprimeAt (P j) (P l) p))
    (hfac : f i =ᶠ[𝓝 p] fun y ↦ u y * ∏ j, (P j y) ^ (m j)) (j : Fin k) :
    p ∈ closure (localDivisorSupport V f) :=
  closure_mono (fun _ hy ↦ hy.1.2) (spec_mem_closure_clean_support_factor hD i p hi hu hu0 hP
    hcP hfac j)

/-- At every point of the support, a chart's equation has an irreducible decomposition with at
least one factor, and every factor has clean regular points of the support arbitrarily close.
Source: Gunning--Rossi, II.B, Theorems 3--6 and Ch. III; Chirka, *Complex Analytic Sets*,
§§2--5. -/
theorem spec_mem_support_exists_clean_decomposition {n : ℕ} {ι : Type*}
    {U : Set ((Fin n → ℂ) × ℂ)} {V : ι → Set ((Fin n → ℂ) × ℂ)}
    {f : ι → (Fin n → ℂ) × ℂ → ℂ} (hD : IsLocalDivisorData U V f)
    (i : ι) (p : (Fin n → ℂ) × ℂ) (hi : p ∈ V i) (hp : p ∈ localDivisorSupport V f) :
    ∃ k : ℕ, ∃ u : (Fin n → ℂ) × ℂ → ℂ,
      ∃ P : Fin k → (Fin n → ℂ) × ℂ → ℂ, ∃ m : Fin k → ℕ,
        0 < k ∧ AnalyticAt ℂ u p ∧ u p ≠ 0 ∧
        (∀ j, AnalyticAt ℂ (P j) p ∧ IsIrreducibleAt (P j) p ∧ 0 < m j) ∧
        Pairwise (fun j l ↦ IsCoprimeAt (P j) (P l) p) ∧
        (f i =ᶠ[𝓝 p] fun y ↦ u y * ∏ j, (P j y) ^ (m j)) ∧
        ∀ j, p ∈ closure {y | y ∈ V i ∩ localDivisorSupport V f ∧ P j y = 0 ∧
          (∀ l, l ≠ j → P l y ≠ 0) ∧ fderiv ℂ (P j) y ≠ 0} :=
  spec_mem_support_exists_clean_decomposition_aux hD i p hi hp

-- Every point of the support lies in the closure of the clean regular part of the support.
example {n : ℕ} {ι : Type*}
    {U : Set ((Fin n → ℂ) × ℂ)} {V : ι → Set ((Fin n → ℂ) × ℂ)}
    {f : ι → (Fin n → ℂ) × ℂ → ℂ} (hD : IsLocalDivisorData U V f)
    (i : ι) (p : (Fin n → ℂ) × ℂ) (hi : p ∈ V i) (hp : p ∈ localDivisorSupport V f) :
    p ∈ closure (localDivisorSupport V f) := by
  obtain ⟨k, u, P, m, hk, -, -, -, -, -, hcl⟩ :=
    spec_mem_support_exists_clean_decomposition hD i p hi hp
  exact closure_mono (fun _ hy ↦ hy.1.2) (hcl ⟨0, hk⟩)

/-! ### Degenerate checks -/

-- The empty cover is local divisor data on the empty set, with empty support.
example {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] :
    IsLocalDivisorData (∅ : Set E) (fun i : Empty ↦ i.elim) (fun _ _ ↦ 0) :=
  ⟨fun i ↦ i.elim, by simp, fun i ↦ i.elim, fun i ↦ i.elim, fun i ↦ i.elim⟩

example {E : Type*} :
    localDivisorSupport (fun i : Empty ↦ (i.elim : Set E)) (fun _ _ ↦ 0) = ∅ := by
  ext x
  simp [localDivisorSupport]

-- On `U = ∅` an empty chart may carry any equation, the zero function included: the
-- nonvanishing condition is a condition at points of the chart.
example {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] :
    IsLocalDivisorData (∅ : Set E) (fun _ : Unit ↦ ∅) (fun _ _ ↦ 0) := by
  refine ⟨fun _ ↦ isOpen_empty, iUnion_const _, fun _ ↦ analyticOnNhd_const, ?_, ?_⟩
  · intro _ x hx
    exact hx.elim
  · intro _ _ x hx
    exact hx.1.elim

-- A zero equation on a nonempty chart is excluded.
example : ¬ IsLocalDivisorData (univ : Set ℂ) (fun _ : Unit ↦ univ) (fun _ _ ↦ 0) := by
  intro hD
  exact hD.2.2.2.1 () 0 (mem_univ _) (Eventually.of_forall fun _ ↦ rfl)

-- A single chart whose equation is a unit everywhere: empty support and zero local divisor at
-- every point, for every `n` including `n = 0`.
example {n : ℕ} :
    IsLocalDivisorData (univ : Set ((Fin n → ℂ) × ℂ)) (fun _ : Unit ↦ univ)
      (fun _ _ ↦ (1 : ℂ)) := by
  refine ⟨fun _ ↦ isOpen_univ, iUnion_const _, fun _ ↦ analyticOnNhd_const, ?_, ?_⟩
  · intro _ x _ h
    exact one_ne_zero h.self_of_nhds
  · intro _ _ x _
    exact ⟨fun _ ↦ 1, analyticAt_const, one_ne_zero, Eventually.of_forall fun _ ↦ by simp⟩

example {E : Type*} : localDivisorSupport (fun _ : Unit ↦ (univ : Set E)) (fun _ _ ↦ 1) = ∅ := by
  ext x
  simp [localDivisorSupport]

example {n : ℕ} (p : (Fin n → ℂ) × ℂ) : localDivisorAt n (fun _ ↦ 1) p = 0 :=
  spec_localDivisorAt_eq_zero_of_ne_zero analyticAt_const one_ne_zero

-- A single chart with the last coordinate as equation: its support is the hyperplane, so the
-- local divisor at the origin is nonzero (here for `n = 0`).
example (hD : IsLocalDivisorData (univ : Set ((Fin 0 → ℂ) × ℂ)) (fun _ : Unit ↦ univ)
      (fun _ y ↦ y.2)) :
    localDivisorAt 0 (fun y ↦ y.2) 0 ≠ 0 :=
  (spec_localDivisorAt_ne_zero_iff hD () 0 (mem_univ _)).mpr ⟨(), mem_univ _, rfl⟩

-- Disjoint charts: the overlap condition between different charts is vacuous.
example : IsLocalDivisorData {z : ℂ | ‖z‖ < 1 ∨ 2 < ‖z‖}
    (fun b : Bool ↦ if b then {z : ℂ | ‖z‖ < 1} else {z | 2 < ‖z‖})
    (fun b _ ↦ if b then (1 : ℂ) else 2) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro b
    cases b
    · exact isOpen_lt continuous_const continuous_norm
    · exact isOpen_lt continuous_norm continuous_const
  · ext z
    simp [or_comm]
  · intro b
    cases b <;> exact analyticOnNhd_const
  · intro b x _ h
    have h0 := h.self_of_nhds
    cases b <;> simp at h0
  · intro b c x hx
    cases b <;> cases c
    · exact ⟨fun _ ↦ 1, analyticAt_const, one_ne_zero, Eventually.of_forall fun _ ↦ by simp⟩
    · simp only [Bool.false_eq_true, ↓reduceIte, mem_inter_iff, mem_ofPred_eq] at hx
      linarith [hx.1, hx.2]
    · simp only [Bool.false_eq_true, ↓reduceIte, mem_inter_iff, mem_ofPred_eq] at hx
      linarith [hx.1, hx.2]
    · exact ⟨fun _ ↦ 1, analyticAt_const, one_ne_zero, Eventually.of_forall fun _ ↦ by simp⟩

-- Falsification: a pair of equations that are not associated on an overlap is not local
-- divisor data, although each equation alone would be.
example : ¬ IsLocalDivisorData (univ : Set ℂ) (fun _ : Bool ↦ univ)
    (fun b z ↦ if b then z else 1) := by
  intro hD
  obtain ⟨u, -, hu0, hfu⟩ := hD.2.2.2.2 true false 0 ⟨mem_univ _, mem_univ _⟩
  have h0 := hfu.self_of_nhds
  simp at h0
  exact hu0 h0.symm

-- Conventions inherited from stage eight: a function whose translate is not analytic, and the
-- zero function, are assigned the zero local divisor.
example {n : ℕ} (f : (Fin n → ℂ) × ℂ → ℂ) (p : (Fin n → ℂ) × ℂ)
    (h : ¬ AnalyticAt ℂ (fun y ↦ f (p + y)) 0) : localDivisorAt n f p = 0 := by
  simp [localDivisorAt, h]

example {n : ℕ} (p : (Fin n → ℂ) × ℂ) : localDivisorAt n (fun _ ↦ 0) p = 0 := by
  have h : AnalyticAt ℂ (fun y : (Fin n → ℂ) × ℂ ↦ (fun _ ↦ (0 : ℂ)) (p + y)) 0 :=
    analyticAt_const
  simp only [localDivisorAt, h, ↓reduceDIte]
  exact spec_localDivisor_zero n

end HodgeLean.Foundations.AnalyticDivisorAlgebraic14
