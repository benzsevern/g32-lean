import HodgeLean.Foundations.Program.RelativeFrameFamilyDefs
import HodgeLean.Foundations.Program.RelativeFrameRestated

/-! # Shared geometric inputs for the marked root family
The filling, total atlas and fibre structures are retained together. No plumbing datum or
frame is a field. HC no distance; AV milestone no distance.
-/
noncomputable section
open Set Manifold Filter Topology
open scoped ContDiff TensorProduct
namespace HodgeLean.Foundations.Program
attribute [local instance] b4cov_sphChartedSpace b4cov_sph_isManifold

/-- The fibre over the full marked-root polydisc.
Source: `b63l_parameterFibre`. -/
abbrev rf8_fibre (C : Type) [TopologicalSpace C] (t : b6t_polydisc mr_base) :=
  b63l_parameterFibre mr_base C (b6t_polydisc mr_base) (Set.Subset.refl _) t

example (C : Type) [TopologicalSpace C] (t : b6t_polydisc mr_base) :
    rf8_fibre C t ≃ₜ C := b6m_coordinate mr_base C t

/-- Geometric and integral data retained from one filling and atlas construction.
Source: `PeriodFunctionChecks.lean` on `origin/main`, lines 447–555; review of
`docs/specs/RelativeFrameFamily.md`, item 10a. -/
structure rf8_SharedFamily where
  C : Type
  [topC : TopologicalSpace C]
  [chartC : ChartedSpace ℂ C]
  [manC : IsManifold 𝓘(ℂ, ℂ) ω C]
  [t2C : T2Space C]
  [compactC : CompactSpace C]
  [connectedC : ConnectedSpace C]
  [actionC : MulAction b4b_Group C]
  hC : ∀ g : b4b_Group, Continuous (fun x : C ↦ g • x)
  [totalChart : ChartedSpace ((Fin 10 → ℂ) × ℂ) (b6t_polydisc mr_base × C)]
  [totalMan : IsManifold 𝓘(ℂ, (Fin 10 → ℂ) × ℂ) ω (b6t_polydisc mr_base × C)]
  atlas : rf7_HurwitzAtlas mr_base b4b_Group C
  [fibreChart : ∀ t, ChartedSpace ℂ (rf8_fibre C t)]
  [fibreMan : ∀ t, IsManifold 𝓘(ℂ, ℂ) ω (rf8_fibre C t)]
  [fibreT2 : ∀ t, T2Space (rf8_fibre C t)]
  [fibreCompact : ∀ t, CompactSpace (rf8_fibre C t)]
  [fibreConnected : ∀ t, ConnectedSpace (rf8_fibre C t)]
  [fibreFaithful : ∀ t, FaithfulSMul b4b_Group (rf8_fibre C t)]
  hincl : ∀ t, ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, (Fin 10 → ℂ) × ℂ) ω
    (fun x : rf8_fibre C t ↦ x.val)
  hG : ∀ t (g : b4b_Group), ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω
    (fun x : rf8_fibre C t ↦ g • x)
  hk : ∀ t, ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω
    (b63d_projection mr_base C atlas.f (b6t_polydisc mr_base) (Set.Subset.refl _) t)
  hsurj : ∀ t, Function.Surjective
    (b63d_projection mr_base C atlas.f (b6t_polydisc mr_base) (Set.Subset.refl _) t)
  hgal : ∀ t, b4_IsGaloisCover b4b_Group
    (b63d_projection mr_base C atlas.f (b6t_polydisc mr_base) (Set.Subset.refl _) t)
  hbranch : ∀ t, b4_branchSet ℂ ℂ
    (b63d_projection mr_base C atlas.f (b6t_polydisc mr_base) (Set.Subset.refl _) t) =
      Set.range (b6_branch t.val)
  hrot : ∀ t (j : Fin 13), ∃ x : rf8_fibre C t,
    b63d_projection mr_base C atlas.f (b6t_polydisc mr_base) (Set.Subset.refl _) t x =
      b6_branch t.val j ∧ b4_IsRotGen ℂ x (b4b_root j)
  Q₀ : LinearMap.BilinForm ℤ (b3_periodLattice ℂ C)
  hQ₀ : b3_IsIntersectionForm ℂ Q₀
  Q : (t : b6t_polydisc mr_base) → LinearMap.BilinForm ℤ (b3_periodLattice ℂ (rf8_fibre C t))
  hQ : ∀ t, b3_IsIntersectionForm ℂ (Q t)
  P : (t : b6t_polydisc mr_base) → b6m_H1 (rf8_fibre C t) →ₗ[ℤ]
    b3_periodLattice ℂ (rf8_fibre C t)
  hP : ∀ t (δ : b3_SmoothLoop ℂ (rf8_fibre C t)),
    P t (b6m_loopClass _ δ) = b3_latticePeriod ℂ _ δ
  A : (t : b6t_polydisc mr_base) →
    b63l_parameterLattice mr_base C hC (b6t_polydisc mr_base) (Set.Subset.refl _) t →ₗ[ℤ]
      b63l_parameterLattice mr_base C hC (b6t_polydisc mr_base) (Set.Subset.refl _) t
  hA : ∀ t x, (A t x).val =
    b63d_operator mr_base C hC (b6t_polydisc mr_base) (Set.Subset.refl _) t x.val

attribute [local instance] rf8_SharedFamily.topC rf8_SharedFamily.chartC
  rf8_SharedFamily.manC rf8_SharedFamily.t2C rf8_SharedFamily.compactC
  rf8_SharedFamily.connectedC rf8_SharedFamily.actionC rf8_SharedFamily.totalChart
  rf8_SharedFamily.totalMan rf8_SharedFamily.fibreChart rf8_SharedFamily.fibreMan
  rf8_SharedFamily.fibreT2 rf8_SharedFamily.fibreCompact rf8_SharedFamily.fibreConnected
  rf8_SharedFamily.fibreFaithful

example (R : rf8_SharedFamily) (t : b6t_polydisc mr_base) :
    ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, (Fin 10 → ℂ) × ℂ) ω
      (fun x : rf8_fibre R.C t ↦ x.val) := R.hincl t

/-- Rotation of a moving root by one constant scalar.
Source: `docs/specs/RelativeFrameFamily.md`, review item 10b. -/
def rf8_rotate {X : Type} (ζ : ℂ) (w : X → ℂ) : X → ℂ := fun x ↦ ζ * w x

example {X : Type} (w : X → ℂ) : rf8_rotate 1 w = w := by
  funext x
  exact one_mul _

open Classical in
/-- The transported filtration on the parameter space, extended by zero off the polydisc.
Source: `PeriodFunctionDefs.lean` on `origin/main`, `b64c_transportedFamily`. -/
def rf8_transportedFamily (R : rf8_SharedFamily) (s : b6t_polydisc mr_base)
    (t : Fin 10 → ℂ) :
    Submodule ℂ (ℂ ⊗[ℤ] b63l_parameterLattice mr_base R.C R.hC
      (b6t_polydisc mr_base) (Subset.refl _) s) :=
  if ht : t ∈ b6t_polydisc mr_base then
    b63e_transportedF mr_base R.C R.hC (b6t_polydisc mr_base) (Subset.refl _) R.P s ⟨t, ht⟩
  else ⊥

example (R : rf8_SharedFamily) (s t : b6t_polydisc mr_base) :
    rf8_transportedFamily R s t.val =
      b63e_transportedF mr_base R.C R.hC (b6t_polydisc mr_base) (Subset.refl _) R.P s t := by
  simp only [rf8_transportedFamily, dite_eq_left t.property]

end HodgeLean.Foundations.Program
