import HodgeLean.Foundations.Program.PrymFamilyCentre
import HodgeLean.Foundations.Program.MarkedRootCover

/-! # B6-3g, part 5: the marked Prym family (definitions)

Stage 3g part 5 assembles the fields of `g32h_PrymFamily` over a parameter set
`V ⊆ b6t_polydisc mr_base`, on the B6-2 family of the marked root cover (`MarkedRootCover*`).
This file holds the objects:

* `b63g5_tuple`: the marked Nielsen tuple `b4b_toMatrix ∘ b4b_root`, the based monodromy of the
  marked root cover along the explicit loops `mr_curve` (the same tuple at every parameter);
* `b63g5_fibreMap`: the embedding `u ↦ (t, ι u)` of the covering domain into the filled fibre at
  `t`, through which the fibre is a filling of the transported cover;
* the topological instances of a filled fibre (`T2Space`, `CompactSpace`, `ConnectedSpace`,
  `FaithfulSMul`), carried from the base filling by the coordinate homeomorphism
  `b6m_coordinate`;
* `b63g5_fiber`: the sixfold of the family at `t`, the part 2 sixfold `b63g2_sixfold` of the
  saturated lattice `Λ_{s₀}` at a fixed reference parameter `s₀`, the filtration transported from
  `t`, the original form and the operator `1 + 2ω`. All fibres share the lattice, the form and the
  operator; only the filtration moves, so the family is marked by `Λ_{s₀}`.

The proof arguments of `b63g5_fiber` are the theorems `b63e_weight_one_riemann`,
`b63g2_operator_sq` and `b63g2_operator_filtration`, which have bodies. No definition selects a
witness from an open statement, and no definition is a proposition.
HC no distance; AV milestone no distance.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry AlgebraicTopology.Singular HodgeLean.RealDefs
open HodgeLean.Adapters HodgeLean.Foundations HodgeLean.Foundations.AppellHumbert
open HodgeLean.Foundations.Symplectic HodgeLean.Papers
open scoped TensorProduct Manifold ContDiff

namespace HodgeLean.Foundations.Program
attribute [local instance] b4cov_sphChartedSpace b4cov_sph_isManifold

/-! ## The marked tuple -/

/-- **The marked Nielsen tuple**: the matrices of the root entries `b4b_root i`, the values of the
based monodromy of the marked root cover on the explicit loops `mr_curve i` (`mr_rootCover`), and
of its transport to every parameter of the polydisc (`mr_rootCover_family`). No orbit is chosen:
the tuple is `b4b_root` itself.
Source: G32 v0.16, Definition 3.5 and Subsection 3.1; `b4b_root`, `b4b_toMatrix`,
`mr_rootCover_family`. -/
def b63g5_tuple : Fin 13 → Matrix (Fin 4) (Fin 4) ℂ :=
  fun i ↦ b4b_toMatrix (b4b_root i)

/-- The marked tuple lies in the Nielsen class (`b63d_root_nielsen`, which has a body). -/
example : g32h_Nielsen b63g5_tuple := b63d_root_nielsen

/-! ## The filled fibres -/

/-- **The covering domain in the filled fibre at `t`**: `u ↦ (t, ι u)`.
Source: Harris–Morrison, *Moduli of Curves*, §1.G; `b6m_coordinate`. -/
def b63g5_fibreMap (b : Fin 10 → ℂ) {U C : Type} (ι : U → C) (V : Set (Fin 10 → ℂ))
    (hV : V ⊆ b6t_polydisc b) (t : V) : U → b63l_parameterFibre b C V hV t :=
  fun u ↦ ⟨(⟨t.val, hV t.property⟩, ι u), rfl⟩

/-- The projection of the fibre at `t` on the embedded covering domain is the transported
projection `b6t_projection b t π` when `f ∘ ι = π`. -/
example (b : Fin 10 → ℂ) {U C : Type} (π : U → b6t_punctured b) (f : C → OnePoint ℂ)
    (ι : U → C) (hproj : ∀ u, f (ι u) = π u) (V : Set (Fin 10 → ℂ))
    (hV : V ⊆ b6t_polydisc b) (t : V) (u : U) :
    b63d_projection b C f V hV t (b63g5_fibreMap b ι V hV t u) = b6t_projection b t.val π u := by
  simp [b63d_projection, b63g5_fibreMap, b6a_map, b6t_projection, hproj]

/-- A filled fibre is Hausdorff when the base filling is: `b6m_coordinate` is a homeomorphism.
Source: `b6m_coordinate`; Mathlib `Homeomorph.t2Space`. -/
instance b63g5_fibre_t2Space (b : Fin 10 → ℂ) (C : Type) [TopologicalSpace C] [T2Space C]
    (t : b6t_polydisc b) : T2Space (b6m_Fibre b C t) :=
  (b6m_coordinate b C t).symm.t2Space

/-- A filled fibre is compact when the base filling is.
Source: `b6m_coordinate`; Mathlib `Homeomorph.compactSpace`. -/
instance b63g5_fibre_compactSpace (b : Fin 10 → ℂ) (C : Type) [TopologicalSpace C]
    [CompactSpace C] (t : b6t_polydisc b) : CompactSpace (b6m_Fibre b C t) :=
  (b6m_coordinate b C t).symm.compactSpace

/-- A filled fibre is connected when the base filling is.
Source: `b6m_coordinate`; Mathlib `Function.Surjective.connectedSpace`. -/
instance b63g5_fibre_connectedSpace (b : Fin 10 → ℂ) (C : Type) [TopologicalSpace C]
    [ConnectedSpace C] (t : b6t_polydisc b) : ConnectedSpace (b6m_Fibre b C t) :=
  (b6m_coordinate b C t).symm.surjective.connectedSpace (b6m_coordinate b C t).symm.continuous

/-- The inherited deck action on a filled fibre is faithful when it is on the base filling: it
acts by `g` on the second coordinate.
Source: `b63l_fibreAction`; Mathlib `FaithfulSMul`. -/
instance b63g5_fibre_faithful (b : Fin 10 → ℂ) (C : Type) [MulAction b4b_Group C]
    [FaithfulSMul b4b_Group C] (t : b6t_polydisc b) :
    FaithfulSMul b4b_Group (b6m_Fibre b C t) :=
  ⟨fun h ↦ eq_of_smul_eq_smul fun x ↦
    congrArg (fun q : b6m_Fibre b C t ↦ q.val.2) (h ⟨(t, x), rfl⟩)⟩

/-- The instances apply to the parameter fibres of B6-3. -/
example (b : Fin 10 → ℂ) (C : Type) [TopologicalSpace C] [T2Space C] [CompactSpace C]
    [ConnectedSpace C] [MulAction b4b_Group C] [FaithfulSMul b4b_Group C]
    (V : Set (Fin 10 → ℂ)) (hV : V ⊆ b6t_polydisc b) (t : V) :
    T2Space (b63l_parameterFibre b C V hV t) ∧ CompactSpace (b63l_parameterFibre b C V hV t) ∧
      ConnectedSpace (b63l_parameterFibre b C V hV t) ∧
      FaithfulSMul b4b_Group (b63l_parameterFibre b C V hV t) :=
  ⟨inferInstance, inferInstance, inferInstance, inferInstance⟩

/-! ## The sixfold of the family -/

/-- **The fibre of the marked family at `t`**: `b63g2_sixfold` of the saturated lattice
`Λ_{s₀} = b63l_parameterLattice … s₀` at the reference parameter `s₀` (free and finite by the
supplied basis `B`), the filtration `b63e_transportedF … s₀ t` transported from `t`, the original
form `b63e_singularQ … s₀ (P s₀) (Q s₀)` and the operator `b63g2_operator … s₀ = 1 + 2ω`. The
certificates are `b63e_weight_one_riemann`, `b63g2_operator_sq` and `b63g2_operator_filtration`,
which have bodies.
Source: G32 v0.16, Subsections 3.2–3.3, Lemma 3.3 and Lemma 3.6 (`A_ρ(C_t)` with its action of
`K` and restricted polarization); Griffiths, *Periods of integrals on algebraic manifolds I*, §2
(the marked period map); `b63g2_sixfold`. -/
def b63g5_fiber (b : Fin 10 → ℂ) (C : Type) [TopologicalSpace C]
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
    (t : V) : g32t_Sixfold :=
  letI : Module.Free ℤ (b63l_parameterLattice b C hC V hV s₀) := Module.Free.of_basis B
  letI : Module.Finite ℤ (b63l_parameterLattice b C hC V hV s₀) := Module.Finite.of_basis B
  b63g2_sixfold _ _
    (b63e_weight_one_riemann b C hC V hV hG hb f hf hs hk Q₀ hQ₀ Q hQ P hP s₀ t).1 _
    (b63e_weight_one_riemann b C hC V hV hG hb f hf hs hk Q₀ hQ₀ Q hQ P hP s₀ t).2
    (b63g2_operator b C hC V hV s₀).toAddMonoidHom (b63g2_operator_sq b C hC V hV s₀ (hG s₀))
    (b63g2_operator_filtration b C hC V hV hG P hP s₀ t)

/-- The fibre at `t` is the B5 model of the reference lattice with the filtration transported
from `t`, and its class is the model class of the original form. -/
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
    letI : Module.Free ℤ (b63l_parameterLattice b C hC V hV s₀) := Module.Free.of_basis B
    letI : Module.Finite ℤ (b63l_parameterLattice b C hC V hV s₀) := Module.Finite.of_basis B
    (b63g5_fiber b C hC V hV hG hb f hf hs hk Q₀ hQ₀ Q hQ P hP s₀ B t).X =
      b5_model (b63l_parameterLattice b C hC V hV s₀) (b63e_transportedF b C hC V hV P s₀ t)
        (b63e_weight_one_riemann b C hC V hV hG hb f hf hs hk Q₀ hQ₀ Q hQ P hP s₀ t).1
        (b63e_singularQ b C hC V hV s₀ (P s₀) (Q s₀)) := rfl

end HodgeLean.Foundations.Program
