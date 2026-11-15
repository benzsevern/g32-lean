import HodgeLean.Foundations.Program.PrymTheoremAPolarized
import HodgeLean.Foundations.Program.SchlesingerPath

/-! # B6-5: the retained cover family along the G32 Schlesinger path (definitions)

The retained family of `rf8_SharedFamily` with its centre `mr_base` and its rotation tuple
`b4b_root` replaced by an arbitrary centre `c` and an arbitrary tuple `g`; the centre
`b65z_centre p = b65p_curve p 0` of the G32 path; the reference parameter, the local period
function, the transported filtration and the retained Prym fibres over `b6t_polydisc c`; the
property of a `g32h_PrymFamily` of being indexed by those fibres; and the specialization of a
retained `mr_base` family. No statement is asserted here.
HC no distance; AV milestone no distance.
-/

noncomputable section
open Set Manifold Filter Topology HodgeLean.Papers
open scoped ContDiff TensorProduct
namespace HodgeLean.Foundations.Program
attribute [local instance] b4cov_sphChartedSpace b4cov_sph_isManifold

/-- The centre of the G32 path cover family: the normalized base configuration of the
Schlesinger path, `b65p_curve p 0 = b65p_chartPoint p`.
Source: G32 v0.16, §3.1 and §5.5 (The direction, the covers `C_θ`); `b65p_curve`. -/
def b65z_centre (p : Fin 12 → ℂ) : Fin 10 → ℂ := b65p_curve p 0

example (p : Fin 12 → ℂ) : b65z_centre p = b65p_chartPoint p := by
  simp only [b65z_centre, b65p_curve]
  congr 1
  funext j
  simp [b65p_moving, b65p_poles]

/-- The radius of the polydisc about any configuration is positive.
Source: `b6t_radius`, the inverse of `4 (1 + Σ nonnegative terms)`. -/
theorem b65z_radius_pos (c : Fin 10 → ℂ) : 0 < b6t_radius c := by
  unfold b6t_radius
  apply inv_pos.mpr
  apply mul_pos (by norm_num)
  have h : 0 ≤ ∑ i : Fin 10, (‖c i‖⁻¹ + ‖c i - 1‖⁻¹ +
      ∑ j : Fin 10, if i = j then 0 else (dist (c i) (c j))⁻¹) := by
    apply Finset.sum_nonneg
    intro i _
    have h1 : 0 ≤ ∑ j : Fin 10, if i = j then (0 : ℝ) else (dist (c i) (c j))⁻¹ := by
      apply Finset.sum_nonneg
      intro j _
      split_ifs <;> positivity
    positivity
  linarith

/-- A configuration lies in its own polydisc.
Source: `b65z_radius_pos`; `Metric.mem_ball_self`. -/
theorem b65z_centre_mem (c : Fin 10 → ℂ) : c ∈ b6t_polydisc c :=
  fun _ ↦ Metric.mem_ball_self (b65z_radius_pos c)

/-- The polydisc about any configuration is open.
Source: Mathlib `isOpen_iInter_of_finite`, `Metric.isOpen_ball`, `continuous_apply`. -/
theorem b65z_polydisc_open (c : Fin 10 → ℂ) : IsOpen (b6t_polydisc c) := by
  have h : b6t_polydisc c = ⋂ i : Fin 10, (fun t : Fin 10 → ℂ ↦ t i) ⁻¹'
      Metric.ball (c i) (b6t_radius c) := by
    ext t
    simp [b6t_polydisc]
  rw [h]
  exact isOpen_iInter_of_finite fun i ↦ Metric.isOpen_ball.preimage (continuous_apply i)

/-- **Satisfiability of the path field `curve_zero`** at the new centre: the base point of the
Schlesinger path lies in the polydisc about `b65z_centre p`, for every `p`. -/
example (p : Fin 12 → ℂ) : b65p_curve p 0 ∈ b6t_polydisc (b65z_centre p) :=
  b65z_centre_mem _

/-- The filled fibre over a parameter of the polydisc about `c`.
Source: `b63l_parameterFibre`; `rf8_fibre` with `mr_base` replaced by `c`. -/
abbrev b65z_fibre (c : Fin 10 → ℂ) (C : Type) [TopologicalSpace C] (t : b6t_polydisc c) :=
  b63l_parameterFibre c C (b6t_polydisc c) (Set.Subset.refl _) t

example (c : Fin 10 → ℂ) (C : Type) [TopologicalSpace C] (t : b6t_polydisc c) :
    b65z_fibre c C t ≃ₜ C := b6m_coordinate c C t

/-- **The retained cover family at an arbitrary centre.** The fields of `rf8_SharedFamily`
with the centre `mr_base` replaced by a configuration `c` and the rotation generators `b4b_root j`
at the ordered branch points replaced by `g j`: one compact connected surface `C` with the G32
action, the B6-2b analytic atlas over `b6t_polydisc c × C` (which contains `c ∈ b6_chart`, the
punctured Galois cover and its filling), the analytic structures on the filled fibres, the Galois,
branch and rotation properties at every parameter, the intersection forms, the period comparisons
and the integral operator `1 + 2ω`, all retained together.
Source: `rf8_SharedFamily` (`RelativeFrameAssemblyDefs.lean:25`); `rf7_HurwitzAtlas`
(`b6a_analytic_atlas`, Fulton, Ann. Math. 90 (1969), 542–575; Harris–Morrison, *Moduli of
Curves*, §1.G); G32 v0.16, §3.1 and Definition 3.5. -/
structure b65z_SharedFamily (c : Fin 10 → ℂ) (g : Fin 13 → b4b_Group) where
  C : Type
  [topC : TopologicalSpace C]
  [chartC : ChartedSpace ℂ C]
  [manC : IsManifold 𝓘(ℂ, ℂ) ω C]
  [t2C : T2Space C]
  [compactC : CompactSpace C]
  [connectedC : ConnectedSpace C]
  [actionC : MulAction b4b_Group C]
  hC : ∀ h : b4b_Group, Continuous (fun x : C ↦ h • x)
  [totalChart : ChartedSpace ((Fin 10 → ℂ) × ℂ) (b6t_polydisc c × C)]
  [totalMan : IsManifold 𝓘(ℂ, (Fin 10 → ℂ) × ℂ) ω (b6t_polydisc c × C)]
  atlas : rf7_HurwitzAtlas c b4b_Group C
  [fibreChart : ∀ t, ChartedSpace ℂ (b65z_fibre c C t)]
  [fibreMan : ∀ t, IsManifold 𝓘(ℂ, ℂ) ω (b65z_fibre c C t)]
  [fibreT2 : ∀ t, T2Space (b65z_fibre c C t)]
  [fibreCompact : ∀ t, CompactSpace (b65z_fibre c C t)]
  [fibreConnected : ∀ t, ConnectedSpace (b65z_fibre c C t)]
  [fibreFaithful : ∀ t, FaithfulSMul b4b_Group (b65z_fibre c C t)]
  hincl : ∀ t, ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, (Fin 10 → ℂ) × ℂ) ω
    (fun x : b65z_fibre c C t ↦ x.val)
  hG : ∀ t (h : b4b_Group), ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω
    (fun x : b65z_fibre c C t ↦ h • x)
  hk : ∀ t, ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω
    (b63d_projection c C atlas.f (b6t_polydisc c) (Set.Subset.refl _) t)
  hsurj : ∀ t, Function.Surjective
    (b63d_projection c C atlas.f (b6t_polydisc c) (Set.Subset.refl _) t)
  hgal : ∀ t, b4_IsGaloisCover b4b_Group
    (b63d_projection c C atlas.f (b6t_polydisc c) (Set.Subset.refl _) t)
  hbranch : ∀ t, b4_branchSet ℂ ℂ
    (b63d_projection c C atlas.f (b6t_polydisc c) (Set.Subset.refl _) t) =
      Set.range (b6_branch t.val)
  hrot : ∀ t (j : Fin 13), ∃ x : b65z_fibre c C t,
    b63d_projection c C atlas.f (b6t_polydisc c) (Set.Subset.refl _) t x =
      b6_branch t.val j ∧ b4_IsRotGen ℂ x (g j)
  Q₀ : LinearMap.BilinForm ℤ (b3_periodLattice ℂ C)
  hQ₀ : b3_IsIntersectionForm ℂ Q₀
  Q : (t : b6t_polydisc c) → LinearMap.BilinForm ℤ (b3_periodLattice ℂ (b65z_fibre c C t))
  hQ : ∀ t, b3_IsIntersectionForm ℂ (Q t)
  P : (t : b6t_polydisc c) → b6m_H1 (b65z_fibre c C t) →ₗ[ℤ]
    b3_periodLattice ℂ (b65z_fibre c C t)
  hP : ∀ t (δ : b3_SmoothLoop ℂ (b65z_fibre c C t)),
    P t (b6m_loopClass _ δ) = b3_latticePeriod ℂ _ δ
  A : (t : b6t_polydisc c) →
    b63l_parameterLattice c C hC (b6t_polydisc c) (Set.Subset.refl _) t →ₗ[ℤ]
      b63l_parameterLattice c C hC (b6t_polydisc c) (Set.Subset.refl _) t
  hA : ∀ t x, (A t x).val =
    b63d_operator c C hC (b6t_polydisc c) (Set.Subset.refl _) t x.val

attribute [local instance] b65z_SharedFamily.topC b65z_SharedFamily.chartC
  b65z_SharedFamily.manC b65z_SharedFamily.t2C b65z_SharedFamily.compactC
  b65z_SharedFamily.connectedC b65z_SharedFamily.actionC b65z_SharedFamily.totalChart
  b65z_SharedFamily.totalMan b65z_SharedFamily.fibreChart b65z_SharedFamily.fibreMan
  b65z_SharedFamily.fibreT2 b65z_SharedFamily.fibreCompact b65z_SharedFamily.fibreConnected
  b65z_SharedFamily.fibreFaithful
attribute [local instance] rf8_SharedFamily.topC rf8_SharedFamily.chartC
  rf8_SharedFamily.manC rf8_SharedFamily.t2C rf8_SharedFamily.compactC
  rf8_SharedFamily.connectedC rf8_SharedFamily.actionC rf8_SharedFamily.totalChart
  rf8_SharedFamily.totalMan rf8_SharedFamily.fibreChart rf8_SharedFamily.fibreMan
  rf8_SharedFamily.fibreT2 rf8_SharedFamily.fibreCompact rf8_SharedFamily.fibreConnected
  rf8_SharedFamily.fibreFaithful

/-- The atlas of a family carries the admissibility of its centre. -/
example {c : Fin 10 → ℂ} {g : Fin 13 → b4b_Group} (D : b65z_SharedFamily c g) :
    c ∈ b6_chart := D.atlas.hb

/-- **What specializes.** A retained `mr_base` family is a family at the centre `mr_base` with
the tuple `b4b_root`, field for field.
Source: `rf8_SharedFamily`; the definition of `b65z_SharedFamily`. -/
def b65z_ofRetained (R : rf8_SharedFamily) : b65z_SharedFamily mr_base b4b_root where
  C := R.C
  hC := R.hC
  atlas := R.atlas
  hincl := R.hincl
  hG := R.hG
  hk := R.hk
  hsurj := R.hsurj
  hgal := R.hgal
  hbranch := R.hbranch
  hrot := R.hrot
  Q₀ := R.Q₀
  hQ₀ := R.hQ₀
  Q := R.Q
  hQ := R.hQ
  P := R.P
  hP := R.hP
  A := R.A
  hA := R.hA

example (R : rf8_SharedFamily) : (b65z_ofRetained R).atlas.f = R.atlas.f := rfl

/-- **Satisfiability of the structure, rank twelve.** A family at the centre `mr_base` exists,
and its reference lattice has rank twelve; this uses only statements with bodies
(`rf8_shared_root`, `b63gR_basis`). -/
example : ∃ D : b65z_SharedFamily mr_base b4b_root,
    Module.finrank ℤ (b63l_parameterLattice mr_base D.C D.hC (b6t_polydisc mr_base)
      (Subset.refl _) b63gP_s₀) = 12 := by
  obtain ⟨R, -⟩ := rf8_shared_root
  exact ⟨b65z_ofRetained R,
    (Module.finrank_eq_card_basis (b63gR_basis R)).trans (Fintype.card_fin _)⟩

/-- The reference parameter `c` of the polydisc about `c`.
Source: `b65z_centre_mem`; `b63gP_s₀` with `mr_base` replaced by `c`. -/
def b65z_s₀ (c : Fin 10 → ℂ) : b6t_polydisc c := ⟨c, b65z_centre_mem c⟩

example (c : Fin 10 → ℂ) : (b65z_s₀ c : Fin 10 → ℂ) = c := rfl

/-- At `mr_base` the reference parameter is `b63gP_s₀`. -/
example : b65z_s₀ mr_base = b63gP_s₀ := rfl

/-- **The local period function**: period coordinates of the family about `c` in a rational
marking of the lattice at a reference parameter `s`.
Source: `b64c_geomPeriod`; `b64i_period` with `mr_base` replaced by `c`; Griffiths, Periods I,
§1. -/
def b65z_period {c : Fin 10 → ℂ} {g : Fin 13 → b4b_Group} (D : b65z_SharedFamily c g)
    (s : b6t_polydisc c)
    (m : (ℚ ⊗[ℤ] b63l_parameterLattice c D.C D.hC (b6t_polydisc c) (Subset.refl _) s) ≃ₗ[ℚ]
      (ℚ ⊗[ℤ] b60_Lattice)) :
    (Fin 10 → ℂ) → Fin 9 → ℂ :=
  b64c_geomPeriod c D.C D.hC (b6t_polydisc c) (Subset.refl _) D.P s m

/-- At `mr_base` the local period function of a specialized family is `b64i_period`. -/
example (R : rf8_SharedFamily) (s : b6t_polydisc mr_base)
    (m : (ℚ ⊗[ℤ] b63l_parameterLattice mr_base R.C R.hC (b6t_polydisc mr_base)
      (Subset.refl _) s) ≃ₗ[ℚ] (ℚ ⊗[ℤ] b60_Lattice)) :
    b65z_period (b65z_ofRetained R) s m = b64i_period R s m := rfl

open Classical in
/-- The transported filtration of the family about `c`, extended by zero off the polydisc.
Source: `b63e_transportedF`; `rf8_transportedFamily` with `mr_base` replaced by `c`. -/
def b65z_transportedFamily {c : Fin 10 → ℂ} {g : Fin 13 → b4b_Group} (D : b65z_SharedFamily c g)
    (s : b6t_polydisc c) (t : Fin 10 → ℂ) :
    Submodule ℂ (ℂ ⊗[ℤ] b63l_parameterLattice c D.C D.hC (b6t_polydisc c) (Subset.refl _) s) :=
  if ht : t ∈ b6t_polydisc c then
    b63e_transportedF c D.C D.hC (b6t_polydisc c) (Subset.refl _) D.P s ⟨t, ht⟩
  else ⊥

example {c : Fin 10 → ℂ} {g : Fin 13 → b4b_Group} (D : b65z_SharedFamily c g)
    (s t : b6t_polydisc c) :
    b65z_transportedFamily D s t.val =
      b63e_transportedF c D.C D.hC (b6t_polydisc c) (Subset.refl _) D.P s t := by
  simp only [b65z_transportedFamily, dite_eq_left t.property]

/-- **The retained Prym fibre** of the family about `c` at `t`: the B5 model of the reference
lattice at `b65z_s₀ c` in a basis `B`, with the filtration transported from `t`.
Source: `b63g5_fiber`; G32 v0.16, Definition 3.2 and Lemma 3.3 (`A_ρ(C)`). -/
def b65z_fiber {c : Fin 10 → ℂ} {g : Fin 13 → b4b_Group} (D : b65z_SharedFamily c g)
    (B : Module.Basis (Fin 12) ℤ
      (b63l_parameterLattice c D.C D.hC (b6t_polydisc c) (Subset.refl _) (b65z_s₀ c)))
    (t : b6t_polydisc c) : g32t_Sixfold :=
  b63g5_fiber c D.C D.hC (b6t_polydisc c) (Subset.refl _) D.hG D.atlas.hb D.atlas.f D.atlas.hf
    D.atlas.hsurj D.hk D.Q₀ D.hQ₀ D.Q D.hQ D.P D.hP (b65z_s₀ c) B t

/-- At `mr_base` the retained fibres are the fibres of `b63gR_family`. -/
example (R : rf8_SharedFamily) (t : b6t_polydisc mr_base) :
    b65z_fiber (b65z_ofRetained R) (b63gR_basis R) t = (b63gR_family R).fiber t := rfl

/-- **`P` is indexed by the retained fibres about `c`.** An equivalence from the polydisc to the
index type of `P` carrying the tuple matrices of `g` and the retained fibres `b65z_fiber D B`.
Source: G32 v0.16, Definition 3.5 and Lemma 3.6; `b63gP_IsMarked` with `mr_base` replaced by
`c`. -/
def b65z_IsLocalPrym {c : Fin 10 → ℂ} {g : Fin 13 → b4b_Group} (D : b65z_SharedFamily c g)
    (B : Module.Basis (Fin 12) ℤ
      (b63l_parameterLattice c D.C D.hC (b6t_polydisc c) (Subset.refl _) (b65z_s₀ c)))
    (P : g32h_PrymFamily) : Prop :=
  ∃ j : b6t_polydisc c ≃ P.S, ∀ t,
    P.tuple (j t) = (fun i ↦ b4b_toMatrix (g i)) ∧ P.fiber (j t) = b65z_fiber D B t

/-- **Satisfiability of `b65z_IsLocalPrym`.** The retained `mr_base` family and `b63gR_family`
satisfy it; this uses only definitions. -/
example (R : rf8_SharedFamily) :
    b65z_IsLocalPrym (b65z_ofRetained R) (b63gR_basis R) (b63gR_family R) :=
  ⟨Equiv.refl _, fun _ ↦ ⟨rfl, rfl⟩⟩

/-- **Non-degeneracy.** The empty family is never indexed by the retained fibres: the polydisc
is nonempty. -/
example {c : Fin 10 → ℂ} {g : Fin 13 → b4b_Group} (D : b65z_SharedFamily c g)
    (B : Module.Basis (Fin 12) ℤ
      (b63l_parameterLattice c D.C D.hC (b6t_polydisc c) (Subset.refl _) (b65z_s₀ c))) :
    ¬ b65z_IsLocalPrym D B b63gP_emptyFamily := by
  rintro ⟨j, -⟩
  exact (j (b65z_s₀ c)).elim

/-- **Non-degeneracy.** A tuple in the G32 Nielsen class is not trivial: some entry is not `1`,
since the entries generate `G`, which contains the reflection `r₁ ≠ 1`. -/
example (g : Fin 13 → b4b_Group) (hg : g32h_Nielsen (fun i ↦ b4b_toMatrix (g i))) :
    ∃ j, g j ≠ 1 := by
  by_contra h
  push Not at h
  have hr : b4b_generators 0 ≠ 1 := by
    intro h1
    have ho := b63_root_order (0 : Fin 13)
    rw [show b4b_root 0 = b4b_generators 0 from rfl, h1, orderOf_one] at ho
    norm_num at ho
  apply hr
  have hmem : (b4b_generators 0 : b4b_Group).val ∈
      Submonoid.closure (Set.range (fun i ↦ b4b_toMatrix (g i))) :=
    by rw [hg.2.2]; exact (b4b_generators 0).property
  have hrange : Set.range (fun i ↦ b4b_toMatrix (g i)) ⊆ {1} := by
    rintro _ ⟨i, rfl⟩
    simp [h i]
  have hsub := Submonoid.closure_mono hrange hmem
  rw [Submonoid.closure_singleton_one, Submonoid.mem_bot] at hsub
  exact Subtype.ext hsub

end HodgeLean.Foundations.Program
