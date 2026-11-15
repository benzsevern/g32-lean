import HodgeLean.Foundations.AnalyticDivisorAlgebraic24

/-! # A nonempty divisor on the fixed cubic

The cover removes all periods except the selected one. Its linear equations cut out
exactly the period lattice, hence descend to the identity point of the cubic.
HC no distance; AV milestone no distance.
-/
noncomputable section
namespace HodgeLean.Foundations.AnalyticDivisorAlgebraic24
open Filter Set Topology
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint TopologicalSpace
open HodgeLean.Foundations HodgeLean.Adapters HodgeLean.RealDefs
open HodgeLean.Foundations.AnalyticDivisorAlgebraic7
open HodgeLean.Foundations.AnalyticDivisorAlgebraic14
open HodgeLean.Foundations.AnalyticDivisorAlgebraic21
open HodgeLean.Foundations.AnalyticDivisorAlgebraic22
open HodgeLean.Foundations.AnalyticDivisorAlgebraic23
open scoped Manifold CategoryTheory.MonObj

abbrev gaga24_Vector := Fin (dim Curves.E.left) → ℂ
abbrev gaga24_Lattice := abelianPeriodLattice Curves.E

def gaga24_coordinate : gaga24_Vector ≃L[ℂ] ℂ := by
  unfold gaga24_Vector
  rw [Curves.E_dim]
  exact ContinuousLinearEquiv.piUnique ℂ (fun _ : Fin 1 ↦ ℂ)

def gaga24_curveOpen : Option gaga24_Lattice → Set gaga24_Vector
  | none => (gaga24_Lattice : Set gaga24_Vector)ᶜ
  | some l => ((gaga24_Lattice : Set gaga24_Vector) \ {l.val})ᶜ

def gaga24_curveEquation : Option gaga24_Lattice → gaga24_Vector → ℂ
  | none => fun _ ↦ 1
  | some l => fun z ↦ gaga24_coordinate (z - l)

lemma gaga24_curveOpen_open (i : Option gaga24_Lattice) : IsOpen (gaga24_curveOpen i) := by
  let : IsCommMonObj Curves.E := isCommMonObj_of_complexSelfProductIntegral Curves.E
    (complexSelfProductIntegral_of_isIntegral Curves.E)
  let := discrete_complexExponentialLattice Curves.E (dim Curves.E.left)
  have hc : IsClosed (gaga24_Lattice : Set gaga24_Vector) :=
    gaga24_Lattice.toAddSubgroup.isClosed_of_discreteTopology
  cases i with
  | none => exact hc.isOpen_compl
  | some l => exact (isClosed_of_subset_discrete_closed sdiff_subset
      (isDiscrete_iff_discreteTopology.mpr inferInstance) hc).isOpen_compl

lemma gaga24_curveEquation_analytic (i : Option gaga24_Lattice) (p : gaga24_Vector) :
    AnalyticAt ℂ (gaga24_curveEquation i) p := by
  cases i with
  | none => exact analyticAt_const
  | some l => exact (gaga24_coordinate.analyticAt _).comp (analyticAt_id.sub analyticAt_const)

lemma gaga24_curve_zero (i : Option gaga24_Lattice) (p : gaga24_Vector)
    (hp : p ∈ gaga24_curveOpen i) :
    gaga24_curveEquation i p = 0 ↔ p ∈ gaga24_Lattice := by
  cases i with
  | none => simpa [gaga24_curveOpen, gaga24_curveEquation] using hp
  | some l =>
    have he : gaga24_curveEquation (some l) p = 0 ↔ p = l := by
      simp [gaga24_curveEquation, sub_eq_zero]
    rw [he]
    change ¬ (p ∈ gaga24_Lattice ∧ p ∉ ({l.val} : Set gaga24_Vector)) at hp
    exact ⟨fun h ↦ h ▸ l.property, fun h ↦ by simpa using not_not.mp (fun hn ↦ hp ⟨h, hn⟩)⟩

lemma gaga24_associated_units {a b : gaga24_Vector → ℂ} {p : gaga24_Vector}
    (ha : AnalyticAt ℂ a p) (hb : AnalyticAt ℂ b p) (ha0 : a p ≠ 0) (hb0 : b p ≠ 0) :
    AreAssociatedAt a b p := by
  refine ⟨fun z ↦ a z / b z, ha.div hb hb0, div_ne_zero ha0 hb0, ?_⟩
  filter_upwards [hb.continuousAt.eventually_ne hb0] with z hz
  exact (div_mul_cancel₀ (a z) hz).symm

lemma gaga24_curve_periodic (l : gaga24_Lattice) (i j : Option gaga24_Lattice)
    (p : gaga24_Vector) (hi : p ∈ gaga24_curveOpen i)
    (hj : p + l ∈ gaga24_curveOpen j) :
    AreAssociatedAt (gaga24_curveEquation i) (fun z ↦ gaga24_curveEquation j (z + l)) p := by
  have han : AnalyticAt ℂ (fun z ↦ gaga24_curveEquation j (z + l)) p :=
    (gaga24_curveEquation_analytic j (p + l)).comp (f := fun z : gaga24_Vector ↦ z + l)
      (show AnalyticAt ℂ (fun z : gaga24_Vector ↦ z + l) p from
        analyticAt_id.add analyticAt_const)
  by_cases hp : p ∈ gaga24_Lattice
  · have hpl : p + l ∈ gaga24_Lattice := gaga24_Lattice.add_mem hp l.property
    have hi0 := (gaga24_curve_zero i p hi).mpr hp
    have hj0 := (gaga24_curve_zero j (p + l) hj).mpr hpl
    cases i with
    | none => exact (one_ne_zero hi0).elim
    | some a =>
      cases j with
      | none => exact (one_ne_zero hj0).elim
      | some b =>
        have ha : p = a := by simpa [gaga24_curveEquation, sub_eq_zero] using hi0
        have hb : p + l = b := sub_eq_zero.mp (gaga24_coordinate.injective (by
          simpa only [gaga24_curveEquation, map_zero] using hj0))
        refine ⟨fun _ ↦ 1, analyticAt_const, one_ne_zero, Eventually.of_forall fun z ↦ ?_⟩
        simp only [gaga24_curveEquation, one_mul]
        congr 1
        rw [← ha, ← hb]
        abel
  · apply gaga24_associated_units (gaga24_curveEquation_analytic i p) han
    · exact fun h ↦ hp ((gaga24_curve_zero i p hi).mp h)
    · intro h
      have hpl := (gaga24_curve_zero j (p + l) hj).mp h
      exact hp (by simpa using gaga24_Lattice.sub_mem hpl l.property)

lemma gaga24_curve_data : IsLocalDivisorData univ gaga24_curveOpen gaga24_curveEquation := by
  refine ⟨gaga24_curveOpen_open, ?_, fun i p _ ↦ gaga24_curveEquation_analytic i p, ?_, ?_⟩
  · apply eq_univ_of_forall
    intro p
    by_cases hp : p ∈ gaga24_Lattice
    · exact mem_iUnion.mpr ⟨some ⟨p, hp⟩, by simp [gaga24_curveOpen]⟩
    · exact mem_iUnion.mpr ⟨none, hp⟩
  · intro i p _ he
    cases i with
    | none => exact one_ne_zero he.self_of_nhds
    | some l =>
      have han : AnalyticOnNhd ℂ (gaga24_curveEquation (some l)) univ :=
        fun z _ ↦ gaga24_curveEquation_analytic (some l) z
      have hall := han.eqOn_zero_of_preconnected_of_eventuallyEq_zero
        isPreconnected_univ (mem_univ p) he
      have h := hall (mem_univ (l.val + gaga24_coordinate.symm 1))
      simp [gaga24_curveEquation] at h
  · intro i j p hp
    simpa using gaga24_curve_periodic (0 : gaga24_Lattice) i j p hp.1 (by simpa using hp.2)


lemma gaga24_curve_support : localDivisorSupport gaga24_curveOpen gaga24_curveEquation =
    (gaga24_Lattice : Set gaga24_Vector) := by
  ext p
  constructor
  · rintro ⟨i, hi, hz⟩
    exact (gaga24_curve_zero i p hi).mp hz
  · intro hp
    refine ⟨some ⟨p, hp⟩, ?_, ?_⟩
    · simp [gaga24_curveOpen]
    · simp [gaga24_curveEquation]

/-- The descended divisor is supported at the identity of the fixed cubic.
Source: `abelianExp_add_lattice` and the explicit local linear equations. -/
lemma gaga24_curve_image : abelianExp Curves.E ''
    localDivisorSupport gaga24_curveOpen gaga24_curveEquation = {abelianExp Curves.E 0} := by
  rw [gaga24_curve_support]
  apply Set.Subset.antisymm
  · rintro _ ⟨p, hp, rfl⟩
    have h := abelianExp_add_lattice Curves.E 0 ⟨p, hp⟩
    simpa using h
  · intro y hy
    rw [Set.mem_singleton_iff] at hy
    subst y
    exact ⟨0, gaga24_Lattice.zero_mem, rfl⟩

lemma gaga24_curve_orbit_exists :
    Nonempty (gaga22_descendedOnX Curves.E gaga24_curve_data gaga24_curve_periodic).Component := by
  have hs := (gaga22_descended_support gaga24_Lattice.toAddSubgroup
    gaga24_curve_data gaga24_curve_periodic).2.1
  have hz : (0 : gaga24_Vector) ∈ localDivisorSupport gaga24_curveOpen gaga24_curveEquation := by
    rw [gaga24_curve_support]
    exact gaga24_Lattice.zero_mem
  have hm := Set.mem_image_of_mem
    (QuotientAddGroup.mk : gaga24_Vector → gaga24_Vector ⧸ gaga24_Lattice.toAddSubgroup) hz
  rw [← hs] at hm
  obtain ⟨O, _⟩ := mem_iUnion.mp hm
  exact ⟨O⟩

/-- A selected actual orbit, obtained from the zero at the origin via stage-22 support.
Source: `gaga22_descended_support`. -/
def gaga24_curveOrbit :
    (gaga22_descendedOnX Curves.E gaga24_curve_data gaga24_curve_periodic).Component :=
  Classical.choice gaga24_curve_orbit_exists

lemma gaga24_curve_orbit_carrier :
    (gaga22_descendedOnX Curves.E gaga24_curve_data gaga24_curve_periodic).carrier
      gaga24_curveOrbit = {abelianExp Curves.E 0} := by
  change abelianExp Curves.E '' gaga21_componentCarrier (Quotient.out gaga24_curveOrbit) = _
  have hsub := Set.image_mono (f := abelianExp Curves.E) (gaga21_b2_carrier_support gaga24_curve_data
    (Quotient.out gaga24_curveOrbit))
  rw [gaga24_curve_image] at hsub
  have hne := (gaga21_carrier_geometry gaga24_curve_data
    (Quotient.out gaga24_curveOrbit)).1.image (abelianExp Curves.E)
  exact Set.eq_singleton_iff_nonempty_unique_mem.mpr ⟨hne, fun _ h ↦ hsub h⟩

-- The ambient scheme, its group object, and every divisor input are supplied above.
example : dim Curves.E.left = 1 := Curves.E_dim

example : gaga23_carrier Curves.E gaga24_curve_data gaga24_curve_periodic
    gaga24_curve_chow gaga24_curveOrbit ≠ univ ∧
    1 ≤ Order.coheight (gaga23_point Curves.E gaga24_curve_data gaga24_curve_periodic
      gaga24_curve_chow gaga24_curveOrbit) :=
  gaga24_proper Curves.E gaga24_curve_data gaga24_curve_periodic gaga24_curve_chow gaga24_curveOrbit

example : ∃ (p : gaga24_Vector) (g : gaga24_Vector → ℂ),
    abelianExp Curves.E p ∈ cycleComponentSmoothSupport Curves.E
      (gaga23_point Curves.E gaga24_curve_data gaga24_curve_periodic gaga24_curve_chow gaga24_curveOrbit) ∧
    AnalyticAt ℂ g p ∧ g p = 0 ∧ fderiv ℂ g p ≠ 0 ∧
    (∀ᶠ z in 𝓝 p, g z = 0 ↔ abelianExp Curves.E z ∈ gaga23_componentSupport Curves.E
      (gaga23_point Curves.E gaga24_curve_data gaga24_curve_periodic gaga24_curve_chow gaga24_curveOrbit)) :=
  gaga24_common_regular Curves.E gaga24_curve_data gaga24_curve_periodic gaga24_curve_chow gaga24_curveOrbit

example : SmoothOfRelativeDimension 0 (cycleComponentSmoothLocusOver Curves.E
    (gaga23_point Curves.E gaga24_curve_data gaga24_curve_periodic gaga24_curve_chow gaga24_curveOrbit)).hom := by
  obtain ⟨m, hm, hd⟩ := gaga24_component_dimension Curves.E gaga24_curve_data
    gaga24_curve_periodic gaga24_curve_chow gaga24_curveOrbit
  rw [Curves.E_dim] at hd
  have : m = 0 := by omega
  simpa only [this] using hm

example : Order.coheight (gaga23_point Curves.E gaga24_curve_data gaga24_curve_periodic
    gaga24_curve_chow gaga24_curveOrbit) = 1 :=
  gaga24_codim Curves.E gaga24_curve_data gaga24_curve_periodic gaga24_curve_chow gaga24_curveOrbit

end HodgeLean.Foundations.AnalyticDivisorAlgebraic24
