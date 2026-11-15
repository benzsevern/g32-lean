import HodgeLean.Foundations.Program.HurwitzFamilyAnalyticB62bTopology

noncomputable section

namespace HodgeLean.Foundations.Program

def b6a_stationaryOpen (b : Fin 10 → ℂ) : Set (OnePoint ℂ) :=
  (⋃ i : Fin 10, ((↑) : ℂ → OnePoint ℂ) ''
    Metric.closedBall (b i) (b6t_radius b))ᶜ

theorem b6a_stationaryOpen_isOpen (b : Fin 10 → ℂ) :
    IsOpen (b6a_stationaryOpen b) := by
  exact (isClosed_iUnion_of_finite fun i : Fin 10 ↦
    ((isCompact_closedBall (b i) (b6t_radius b)).image
      OnePoint.continuous_coe).isClosed).isOpen_compl

theorem b6a_fixed_value_mem_stationaryOpen (b : Fin 10 → ℂ) (hb : b ∈ b6_chart)
    (j : Fin 13) (hj : ¬j.val < 10) :
    b6a_value b j 0 ∈ b6a_stationaryOpen b := by
  have hd := (b6t_discs b hb).2.1
  have hv : j.val = 10 ∨ j.val = 11 ∨ j.val = 12 := by omega
  rcases hv with hv | hv | hv
  · simpa [b6a_stationaryOpen, b6a_value, hj, hv] using fun i ↦ (hd i).1
  · simpa [b6a_stationaryOpen, b6a_value, hj, hv] using fun i ↦ (hd i).2
  · simp [b6a_stationaryOpen, b6a_value, hj, hv]

theorem b6a_value_continuous (b : Fin 10 → ℂ) (j : Fin 13) :
    Continuous (b6a_value b j) := by
  unfold b6a_value
  split
  · exact OnePoint.continuous_coe.comp (continuous_const.add continuous_id)
  · split
    · exact OnePoint.continuous_coe
    · split
      · exact OnePoint.continuous_coe.comp (continuous_const.add continuous_id)
      · exact b4cov_sphInv_continuous.comp OnePoint.continuous_coe

noncomputable def b6a_fixedMarkChart (b : Fin 10 → ℂ) (j : Fin 13) (n : ℕ)
    {C : Type} [TopologicalSpace C] (P : OpenPartialHomeomorph C ℂ) :
    OpenPartialHomeomorph C ℂ :=
  P.trans (OpenPartialHomeomorph.ofSet
    ((fun w : ℂ ↦ b6a_value b j (w ^ n)) ⁻¹' b6a_stationaryOpen b)
    ((b6a_stationaryOpen_isOpen b).preimage
      ((b6a_value_continuous b j).comp (continuous_id.pow n))))

theorem b6a_mem_fixedMarkChart_source (b : Fin 10 → ℂ) (hb : b ∈ b6_chart)
    (j : Fin 13) (hj : ¬j.val < 10) (n : ℕ) (hn : 0 < n)
    {C : Type} [TopologicalSpace C] (P : OpenPartialHomeomorph C ℂ)
    (x : C) (hx : x ∈ P.source) (hzero : P x = 0) :
    x ∈ (b6a_fixedMarkChart b j n P).source := by
  simpa [b6a_fixedMarkChart, hx, hzero, hn.ne'] using
    b6a_fixed_value_mem_stationaryOpen b hb j hj

theorem b6a_fixedMarkChart_power (b : Fin 10 → ℂ) (hb : b ∈ b6_chart)
    (j : Fin 13) (hj : ¬j.val < 10) (n : ℕ)
    {C : Type} [TopologicalSpace C] (P : OpenPartialHomeomorph C ℂ)
    (f : C → OnePoint ℂ) (hf : ∀ x ∈ P.source, f x = b6a_value b j (P x ^ n))
    (t : b6t_polydisc b) (x : C) (hx : x ∈ (b6a_fixedMarkChart b j n P).source) :
    b6a_map b f (t, x) = b6a_value t.val j (b6a_fixedMarkChart b j n P x ^ n) := by
  have hxs : x ∈ P.source := hx.1
  have hstat : b6a_value b j (P x ^ n) ∈ b6a_stationaryOpen b := hx.2
  change b6t_sphere b t.val (f x) = _
  rw [hf x hxs, (b6t_fixed b hb t.val t.property).2.2.2 _ hstat]
  simp [b6a_fixedMarkChart, b6a_value, hj]

theorem b6a_value_zero (b : Fin 10 → ℂ) (j : Fin 13) :
    b6a_value b j 0 = b6_branch b j := by
  fin_cases j <;> simp [b6a_value] <;> rfl

theorem b6a_value_injective (b : Fin 10 → ℂ) (j : Fin 13) :
    Function.Injective (b6a_value b j) := by
  intro x y h
  unfold b6a_value at h
  split_ifs at h
  · exact add_left_cancel (OnePoint.coe_injective h)
  · exact OnePoint.coe_injective h
  · exact add_left_cancel (OnePoint.coe_injective h)
  · exact OnePoint.coe_injective (b4cov_sphInv_involutive.injective h)

def b6a_markValueOpen (b : Fin 10 → ℂ) (j : Fin 13) : Set (OnePoint ℂ) :=
  (Set.range (fun k : {k : Fin 13 // k ≠ j} ↦ b6_branch b k.val))ᶜ

theorem b6a_markValueOpen_isOpen (b : Fin 10 → ℂ) (j : Fin 13) :
    IsOpen (b6a_markValueOpen b j) :=
  (Set.finite_range (fun k : {k : Fin 13 // k ≠ j} ↦ b6_branch b k.val)).isClosed.isOpen_compl

theorem b6a_branch_mem_markValueOpen (b : Fin 10 → ℂ) (hb : b ∈ b6_chart)
    (j k : Fin 13) : b6_branch b k ∈ b6a_markValueOpen b j ↔ k = j := by
  constructor
  · intro hk
    by_contra hkj
    exact hk ⟨⟨k, hkj⟩, rfl⟩
  · rintro rfl ⟨k, hk⟩
    exact k.property (hb hk)

end HodgeLean.Foundations.Program
