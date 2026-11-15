module

public import Mathlib.Topology.OpenPartialHomeomorph.Basic
public import Mathlib.GroupTheory.GroupAction.SubMulAction
public import Mathlib.Algebra.Group.Action.End
public import Mathlib.Algebra.Group.End
public import HodgeLean.Foundations.Program.FiniteGroupLinearization
public import Mathlib.Analysis.Calculus.FDeriv.Analytic

/-! # Transporting an invariant local action to coordinates
The coordinate action extends by the identity outside the chart image.
-/
public section
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

/-- Transport the action on an invariant set through a chart and extend it on
coordinate space, fixing the complement of the chart image.
Source: Takamura, Linearization of Quotient Families, J. Math. Sci. Univ.
Tokyo 26 (2019), p. 381, action in local coordinates; Mathlib,
`Equiv.Perm.extendDomainHom`. -/
def coordinateExtendedAction
    (G : Type*) [Group G] {A E : Type*} [TopologicalSpace A] [TopologicalSpace E]
    [MulAction G A] (S : SubMulAction G A) (e : OpenPartialHomeomorph A E)
    (hS : (S : Set A) ⊆ e.source) : G →* Equiv.Perm E := by
  classical
  exact (Equiv.Perm.extendDomainHom
    (e.homeomorphOfImageSubsetSource hS rfl).toEquiv).comp (MulAction.toPermHom G S)

/-- The transported action agrees with the actual group action at every point
of the invariant chart domain.
Source: Takamura, Linearization of Quotient Families, J. Math. Sci. Univ.
Tokyo 26 (2019), p. 381, coordinate identification of the action. -/
theorem coordinateExtendedAction_apply_chart
    (G : Type*) [Group G] {A E : Type*} [TopologicalSpace A] [TopologicalSpace E]
    [MulAction G A] (S : SubMulAction G A) (e : OpenPartialHomeomorph A E)
    (hS : (S : Set A) ⊆ e.source) (g : G) (x : S) :
    coordinateExtendedAction G S e hS g (e x) = e (g • (x : A)) := by
  classical
  let f := (e.homeomorphOfImageSubsetSource hS rfl).toEquiv
  change (MulAction.toPermHom G S g).extendDomain f (f x) = _
  rw [Equiv.Perm.extendDomain_apply_image]
  rfl

example (G : Type*) [Group G] {A E : Type*} [TopologicalSpace A] [TopologicalSpace E]
    [MulAction G A] (S : SubMulAction G A) (e : OpenPartialHomeomorph A E)
    (hS : (S : Set A) ⊆ e.source) : coordinateExtendedAction G S e hS 1 = 1 := map_one _

/-- At every point of the chart image the extension has the required coordinate formula.
Source: Takamura, Linearization of Quotient Families, J. Math. Sci. Univ.
Tokyo 26 (2019), p. 381, action in local coordinates. -/
theorem coordinateExtendedAction_apply_image
    (G : Type*) [Group G] {A E : Type*} [TopologicalSpace A] [TopologicalSpace E]
    [MulAction G A] (S : SubMulAction G A) (e : OpenPartialHomeomorph A E)
    (hS : (S : Set A) ⊆ e.source) (g : G) (z : E) (hz : z ∈ e '' (S : Set A)) :
    coordinateExtendedAction G S e hS g z = e (g • e.symm z) := by
  obtain ⟨x, hx, rfl⟩ := hz
  have he : e.symm (e x) = x := e.left_inv (hS hx)
  rw [he]
  exact coordinateExtendedAction_apply_chart G S e hS g ⟨x, hx⟩

/-- The extended action has the same germ as the chart expression on an open invariant set.
Source: Takamura, Linearization of Quotient Families, J. Math. Sci. Univ.
Tokyo 26 (2019), p. 381, action in local coordinates. -/
theorem coordinateExtendedAction_eventuallyEq
    (G : Type*) [Group G] {A E : Type*} [TopologicalSpace A] [TopologicalSpace E]
    [MulAction G A] (S : SubMulAction G A) (e : OpenPartialHomeomorph A E)
    (hS : (S : Set A) ⊆ e.source) (hopen : IsOpen (S : Set A))
    (g : G) (z : E) (hz : z ∈ e '' (S : Set A)) :
    (coordinateExtendedAction G S e hS g : E → E) =ᶠ[nhds z]
      (fun y => e (g • e.symm y)) := by
  exact Filter.mem_of_superset
    ((e.isOpen_image_of_subset_source hopen hS).mem_nhds hz)
    (fun y hy => coordinateExtendedAction_apply_image G S e hS g y hy)

/-- A fixed point placed at the coordinate origin is fixed by the extended action.
Source: Takamura, Linearization of Quotient Families, J. Math. Sci. Univ.
Tokyo 26 (2019), p. 381, coordinates centered at the fixed point. -/
theorem coordinateExtendedAction_zero
    (G : Type*) [Group G] {A E : Type*} [TopologicalSpace A] [TopologicalSpace E] [Zero E]
    [MulAction G A] (S : SubMulAction G A) (e : OpenPartialHomeomorph A E)
    (hS : (S : Set A) ⊆ e.source) (x₀ : S) (hezero : e x₀ = 0)
    (hfixed : ∀ g : G, g • (x₀ : A) = x₀) (g : G) :
    coordinateExtendedAction G S e hS g 0 = 0 := by
  calc
    coordinateExtendedAction G S e hS g 0 =
        coordinateExtendedAction G S e hS g (e x₀) := congrArg _ hezero.symm
    _ = e (g • (x₀ : A)) := coordinateExtendedAction_apply_chart G S e hS g x₀
    _ = 0 := by rw [hfixed g, hezero]

/-- Analytic coordinate action maps give locally invertible equivariant coordinates;
the tangent representation and the coordinate map are constructed.
Source: Takamura, Linearization of Quotient Families, J. Math. Sci. Univ.
Tokyo 26 (2019), pp. 381–382, construction and Lemma 3.6. -/
theorem coordinate_action_local_linearization
    (G : Type*) [Group G] [Fintype G]
    {A E : Type*} [TopologicalSpace A]
    [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    [MulAction G A] (S : SubMulAction G A) (e : OpenPartialHomeomorph A E)
    (hS : (S : Set A) ⊆ e.source) (hopen : IsOpen (S : Set A))
    (x₀ : S) (hezero : e x₀ = 0) (hfixed : ∀ g : G, g • (x₀ : A) = x₀)
    (hana : ∀ g : G, AnalyticAt ℂ (fun z => e (g • e.symm z)) 0) :
    ∃ ρ : G →* (E ≃L[ℂ] E), ∃ F : OpenPartialHomeomorph E E,
      (0 : E) ∈ F.source ∧ F 0 = 0 ∧
      ∀ g (x : S), F (e (g • (x : A))) = ρ g (F (e x)) := by
  let P := coordinateExtendedAction G S e hS
  let a : G → E → E := fun g => P g
  have h1 (z : E) : a 1 z = z :=
    congrArg (fun f : Equiv.Perm E => f z) P.map_one
  have hm (g h : G) (z : E) : a (g * h) z = a g (a h z) :=
    congrArg (fun f : Equiv.Perm E => f z) (P.map_mul g h)
  have hz (g : G) : a g 0 = 0 :=
    coordinateExtendedAction_zero G S e hS x₀ hezero hfixed g
  have h0 : (0 : E) ∈ e '' (S : Set A) := ⟨x₀, x₀.property, hezero⟩
  have hd (g : G) : ∃ D : E →L[ℂ] E, HasStrictFDerivAt (a g) D 0 := by
    obtain ⟨p, hp⟩ := hana g
    refine ⟨_, hp.hasStrictFDerivAt.congr_of_eventuallyEq ?_⟩
    exact (coordinateExtendedAction_eventuallyEq G S e hS hopen g 0 h0).symm
  obtain ⟨ρ, hρ⟩ := action_tangent_representation G a h1 hm hz hd
  obtain ⟨F, _, hF0, hFzero, hFeq⟩ :=
    finiteGroupAveragedChart_localHomeomorph G a hm hz ρ hρ
  refine ⟨ρ, F, hF0, hFzero, ?_⟩
  intro g x
  have heq : a g (e x) = e (g • (x : A)) :=
    coordinateExtendedAction_apply_chart G S e hS g x
  rw [← heq]
  exact hFeq g (e x)

end HodgeLean.Foundations.Program
