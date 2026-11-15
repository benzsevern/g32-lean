import HodgeLean.Foundations.AnalyticStratificationProofs

/-! # Countable holomorphic parametrization (frozen specification)

Implication from local finite holomorphic equations to countable parametrizations, and from
closed analyticity and properness to strictly smaller parameter dimensions. The images need
not be disjoint, embedded strata or a Whitney stratification. The intermediate hypersurface
cover can contain extra points; pullback of the original equations removes them.
HC no distance; AV milestone no distance.
Concrete premise witnesses are in AnalyticStratificationExamples.
-/

noncomputable section
open Set Filter Topology
namespace HodgeLean.Foundations

/-- A nonzero holomorphic germ vanishing at the anchor has a derivative with a regular zero there.
Source: Gunning--Rossi, Chapter I, §A (Taylor expansion and uniqueness);
Chirka, *Complex Analytic Sets*, §2 (local equations). -/
theorem astrat_finite_derivative (n : ℕ) (f : (Fin n → ℂ) → ℂ)
    (z : Fin n → ℂ) (hf : AnalyticAt ℂ f z) (hz : f z = 0)
    (hne : ¬ f =ᶠ[𝓝 z] 0) :
    ∃ s : List (Fin n), AnalyticAt ℂ (astrat_partial n f s) z ∧
      astrat_partial n f s z = 0 ∧ fderiv ℂ (astrat_partial n f s) z ≠ 0 :=
  astrat_finite_derivative_aux n f z hf hz hne

/-- A regular hypersurface has an anchored parametrization on an open parameter domain.
Source: Gunning--Rossi, Chapter I, §B, Theorem 4; the kernel chart in
AnalyticDivisorAlgebraic3.spec_exists_analytic_graph, followed by finite-dimensional coordinates. -/
theorem astrat_regular_parametrization (n : ℕ)
    (W : Set (Fin (n + 1) → ℂ)) (hW : IsOpen W)
    (f : (Fin (n + 1) → ℂ) → ℂ) (hf : AnalyticOnNhd ℂ f W)
    (z : Fin (n + 1) → ℂ) (hz : z ∈ W) (hzero : f z = 0)
    (hreg : fderiv ℂ f z ≠ 0) :
    ∃ (U : Set (Fin n → ℂ)) (V : Set (Fin (n + 1) → ℂ))
      (g : (Fin n → ℂ) → (Fin (n + 1) → ℂ)),
      IsOpen U ∧ (0 : Fin n → ℂ) ∈ U ∧ IsOpen V ∧ z ∈ V ∧ V ⊆ W ∧
      AnalyticOnNhd ℂ g U ∧ g 0 = z ∧ g '' U = V ∩ {x | f x = 0} :=
  astrat_regular_parametrization_aux n W hW f hf z hz hzero hreg

/-- A nonzero equation on a connected open domain has a countable hypersurface cover.
The chart images may contain points where the original equation is nonzero.
Source: Gunning--Rossi, Chapter I, §§A--B (derivatives and implicit functions);
second countability applied separately to the regular zero locus of each derivative. -/
theorem astrat_zero_set_cover (n : ℕ)
    (W : Set (Fin (n + 1) → ℂ)) (hW : IsOpen W) (hc : IsPreconnected W)
    (f : (Fin (n + 1) → ℂ) → ℂ) (hf : AnalyticOnNhd ℂ f W)
    (a : Fin (n + 1) → ℂ) (ha : a ∈ W) (hne : f a ≠ 0) :
    ∃ (U : ℕ → Set (Fin n → ℂ))
      (g : ℕ → (Fin n → ℂ) → (Fin (n + 1) → ℂ)),
      (∀ j, IsOpen (U j)) ∧ (∀ j, AnalyticOnNhd ℂ (g j) (U j)) ∧
      (∀ j, MapsTo (g j) (U j) W) ∧
      W ∩ {x | f x = 0} ⊆ ⋃ j, g j '' U j :=
  astrat_zero_set_cover_aux n W hW hc f hf a ha hne

/-- Local finite equations pull back along a holomorphic map on an open domain.
Source: Gunning--Rossi, Chapter II, local analytic sets and inverse images;
Chirka, *Complex Analytic Sets*, §2. -/
theorem astrat_pullback_equations (n k : ℕ) (Z : Set (Fin n → ℂ))
    (hZ : ∀ z ∈ Z, ∃ (V : Set (Fin n → ℂ)), IsOpen V ∧ z ∈ V ∧
      ∃ (r : ℕ) (F : Fin r → (Fin n → ℂ) → ℂ),
        (∀ i, AnalyticOnNhd ℂ (F i) V) ∧
        ∀ x ∈ V, (x ∈ Z ↔ ∀ i, F i x = 0))
    (U : Set (Fin k → ℂ)) (hU : IsOpen U)
    (g : (Fin k → ℂ) → (Fin n → ℂ)) (hg : AnalyticOnNhd ℂ g U) :
    ∀ z ∈ U ∩ g ⁻¹' Z, ∃ (V : Set (Fin k → ℂ)), IsOpen V ∧ z ∈ V ∧
      ∃ (r : ℕ) (F : Fin r → (Fin k → ℂ) → ℂ),
        (∀ i, AnalyticOnNhd ℂ (F i) V) ∧
        ∀ x ∈ V, (x ∈ U ∩ g ⁻¹' Z ↔ ∀ i, F i x = 0) :=
  astrat_pullback_equations_aux n k Z hZ U hU g hg

/-- Sets with local finite holomorphic equations at their own points have countable charts.
Only charts whose images lie in the interior may have full ambient parameter dimension.
Source: Gunning--Rossi, Chapter III (local parametrization); Chirka, §2;
dimension induction using derivative hypersurface covers and pullback equations. -/
theorem astrat_local_parametrization (n : ℕ) (Z : Set (Fin n → ℂ))
    (hZ : ∀ z ∈ Z, ∃ (V : Set (Fin n → ℂ)), IsOpen V ∧ z ∈ V ∧
      ∃ (r : ℕ) (F : Fin r → (Fin n → ℂ) → ℂ),
        (∀ i, AnalyticOnNhd ℂ (F i) V) ∧
        ∀ x ∈ V, (x ∈ Z ↔ ∀ i, F i x = 0)) :
    ∃ (d : ℕ → ℕ) (U : ∀ j, Set (Fin (d j) → ℂ))
      (f : ∀ j, (Fin (d j) → ℂ) → (Fin n → ℂ)),
      (∀ j, d j ≤ n) ∧ (∀ j, IsOpen (U j)) ∧
      (∀ j, AnalyticOnNhd ℂ (f j) (U j)) ∧
      (∀ j, d j = n → f j '' U j ⊆ interior Z) ∧ Z = ⋃ j, f j '' U j :=
  astrat_local_parametrization_aux n Z hZ

/-- Countably many holomorphic images of strictly smaller dimension equal a proper analytic set.
Source: Gunning--Rossi, Chapter III, regular loci and stratification by complex dimension;
Chirka, *Complex Analytic Sets*, §2. -/
theorem astrat_analytic_stratification (n : ℕ) (hn : 0 < n)
    (Z : Set (Fin n → ℂ)) (hZ : IsClosedAnalytic (Fin n → ℂ) Z) (hp : Z ≠ univ) :
    ∃ (d : ℕ → ℕ) (U : ∀ j, Set (Fin (d j) → ℂ))
      (f : ∀ j, (Fin (d j) → ℂ) → (Fin n → ℂ)),
      (∀ j, d j < n) ∧ (∀ j, IsOpen (U j)) ∧
      (∀ j, DifferentiableOn ℂ (f j) (U j)) ∧ Z = ⋃ j, f j '' U j :=
  astrat_analytic_stratification_aux n hn Z hZ hp

end HodgeLean.Foundations
