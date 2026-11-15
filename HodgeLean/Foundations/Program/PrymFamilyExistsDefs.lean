import HodgeLean.Foundations.Program.PrymFamilyMarked
import HodgeLean.Foundations.Program.PrymFamilyPositivity
import HodgeLean.Foundations.Program.HeckeSpreadingPrym
import HodgeLean.Papers.G32Narrow
import HodgeLean.Papers.QuasiInverse

/-! # The Prym family `P`: the named family on the marked root cover (definitions)

Stage `P` of B6-3g names one element of `g32h_PrymFamily`, the marked family of part 5 over the
whole polydisc `b6t_polydisc mr_base`, with the field `positive` from part 4. This file holds the
objects:

* `b63gP_s₀`: the reference parameter `mr_base` of the polydisc (so the polydisc is nonempty);
* `b63gP_basePoint`, `b63gP_loops`: the base point `mr_basePoint` of the punctured sphere at
  `mr_base` and the explicit loop classes of `mr_curve` there, chosen from
  `mr_loop_existsUnique` (a theorem with a body), with uniqueness of each class;
* `b63gP_IsMarked F`: the property of an element `F` of `g32h_PrymFamily` of being the marked
  family of a marked root cover for the loops `b63gP_loops`, indexed by the polydisc, with tuple
  `b63g5_tuple` and fibres `b63g5_fiber … t` at every `t`;
* `b63gP_emptyFamily`: the element with empty index type, which every field allows; it is the
  degenerate case that the existence statement rules out;
* `b63gP_family`: Hilbert's choice `Classical.epsilon` of an element that is marked and has a
  nonempty index type, where `b63gP_emptyFamily` supplies the nonemptiness proof required by `epsilon`; without an existence witness, its value is unspecified.

`b63gP_family` is a genuine definition: it uses no statement, open or proved, and evaluates the
choice operator on a property. Its pinning properties follow from the existence statement
`b63gP_exists` of `PrymFamilyExists.lean`. No definition selects a witness from an open
statement, and no definition is a proposition without parameters.
HC no distance; AV milestone no distance.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint AlgebraicTopology.Singular
open HodgeLean.RealDefs HodgeLean.Adapters HodgeLean.Foundations HodgeLean.Papers
open TopologicalSpace
open scoped Manifold ContDiff

namespace HodgeLean.Foundations.Program
attribute [local instance] b4cov_sphChartedSpace b4cov_sph_isManifold

/-! ## The base -/

/-- **The reference parameter**: `mr_base` as a point of its own polydisc.
Source: `b6t_polydisc_neighbourhood` (the polydisc contains its centre); `mr_base_mem_chart`. -/
def b63gP_s₀ : b6t_polydisc mr_base :=
  ⟨mr_base, (b6t_polydisc_neighbourhood mr_base mr_base_mem_chart).1⟩

/-- The polydisc about `mr_base` is nonempty. -/
example : Nonempty (b6t_polydisc mr_base) := ⟨b63gP_s₀⟩

example : (b63gP_s₀ : Fin 10 → ℂ) = mr_base := rfl

/-- **The base point** `mr_basePoint` of the punctured sphere at `mr_base`: the starting point
of the outer explicit curve, off the thirteen marks.
Source: `mr_basePoint`, `mr_curve_avoids` (a theorem with a body). -/
def b63gP_basePoint : b6t_punctured mr_base :=
  ⟨((mr_basePoint : ℂ) : OnePoint ℂ), by
    have h0 : mr_curve 12 ((0 : unitInterval) : ℝ) = ((mr_basePoint : ℂ) : OnePoint ℂ) := by
      simp [mr_curve, mr_outer, mr_basePoint]
    have h := (mr_curve_avoids mr_base b63gP_s₀.property 12 0).1
    rw [h0] at h
    exact h⟩

example : (b63gP_basePoint : OnePoint ℂ) = ((mr_basePoint : ℂ) : OnePoint ℂ) := rfl

/-- **The explicit loop classes** at `b63gP_basePoint`: the unique class traced by
`mr_curve i`.
Source: `mr_loop_existsUnique` (a theorem with a body); Hatcher, *Algebraic Topology*, §1.1. -/
def b63gP_loops (i : Fin 13) : FundamentalGroup (b6t_punctured mr_base) b63gP_basePoint :=
  (mr_loop_existsUnique mr_base b63gP_s₀.property b63gP_basePoint rfl i).exists.choose

/-- Each chosen class is a loop class of `mr_curve i`, and the only one. -/
example (i : Fin 13) (c : FundamentalGroup (b6t_punctured mr_base) b63gP_basePoint)
    (hc : mr_IsLoop mr_base b63gP_basePoint i c) :
    mr_IsLoop mr_base b63gP_basePoint i (b63gP_loops i) ∧ c = b63gP_loops i :=
  ⟨(mr_loop_existsUnique mr_base b63gP_s₀.property b63gP_basePoint rfl i).exists.choose_spec,
    (mr_loop_existsUnique mr_base b63gP_s₀.property b63gP_basePoint rfl i).unique hc
      (mr_loop_existsUnique mr_base b63gP_s₀.property b63gP_basePoint rfl i).exists.choose_spec⟩

/-! ## The marked property -/

/-- **`F` is the marked family of a marked root cover over the polydisc.** There are

* a connected Galois `b4b_Group`-covering `π : U → b6t_punctured mr_base` with a point `u₀` over
  `b63gP_basePoint` whose based monodromy sends `b63gP_loops i` to `op (b4b_root i)` (the
  conclusion of `mr_rootCover` for these loops);
* its compact holomorphic Galois filling `f : C → ℙ¹`, with the open embedding `ι : U → C` and
  every other clause of `mr_rootCover`;
* complex structures on the filled fibres `b63l_parameterFibre mr_base C (b6t_polydisc mr_base) _ t`
  with holomorphic projection and deck maps, intersection forms `Q₀`, `Q t`, period comparisons
  `P t`, and a basis of rank twelve of the reference lattice at `b63gP_s₀`;
* an equivalence `j` from the polydisc to `F.S`;

such that at every parameter `t`, `F.tuple (j t) = b63g5_tuple` and
`F.fiber (j t) = b63g5_fiber … t` for these data. The rank-twelve basis excludes the zero lattice.
Source: G32 v0.16, Definition 3.5 and Lemma 3.6 (`Hur°` and the factor `A_ρ(C)`); `mr_rootCover`,
`b63g5_fiber`, `b63g5_tuple`; Griffiths, *Periods of integrals on algebraic manifolds I*, §2. -/
def b63gP_IsMarked (F : g32h_PrymFamily) : Prop :=
  ∃ (U : Type) (_ : TopologicalSpace U) (_ : MulAction b4b_Group U)
    (_ : ConnectedSpace U) (π : U → b6t_punctured mr_base)
    (hπ : IsQuotientCoveringMap π b4b_Group) (u₀ : π ⁻¹' {b63gP_basePoint}),
    (∀ i, hπ.fundamentalGroupToMulOpposite u₀ (b63gP_loops i) = MulOpposite.op (b4b_root i)) ∧
    ∃ (C : Type) (_ : TopologicalSpace C) (_ : ChartedSpace ℂ C)
      (_ : IsManifold 𝓘(ℂ, ℂ) ω C) (_ : T2Space C) (_ : CompactSpace C)
      (_ : ConnectedSpace C) (_ : MulAction b4b_Group C) (_ : FaithfulSMul b4b_Group C)
      (f : C → OnePoint ℂ) (ι : U → C) (hf : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω f)
      (hsurj : Function.Surjective f)
      (hact : ∀ g : b4b_Group, ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω (fun x : C ↦ g • x)),
      b4_IsGaloisCover b4b_Group f ∧
      Topology.IsOpenEmbedding ι ∧ Set.range ι = f ⁻¹' (Set.range (b6_branch mr_base))ᶜ ∧
      (∀ u, f (ι u) = π u) ∧ (∀ (g : b4b_Group) (u : U), ι (g • u) = g • ι u) ∧
      (∀ x, f x ∉ Set.range (b6_branch mr_base) → MulAction.stabilizer b4b_Group x = ⊥) ∧
      (∀ j, ∃ x, f x = b6_branch mr_base j ∧ b4_IsRotGen ℂ x (b4b_root j)) ∧
      ∃ (_ : ∀ t : b6t_polydisc mr_base,
          ChartedSpace ℂ (b63l_parameterFibre mr_base C (b6t_polydisc mr_base) Set.Subset.rfl t))
        (_ : ∀ t : b6t_polydisc mr_base, IsManifold 𝓘(ℂ, ℂ) ω
          (b63l_parameterFibre mr_base C (b6t_polydisc mr_base) Set.Subset.rfl t))
        (hG : ∀ (t : b6t_polydisc mr_base) (g : b4b_Group), ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω
          (fun x : b63l_parameterFibre mr_base C (b6t_polydisc mr_base) Set.Subset.rfl t ↦ g • x))
        (hk : ∀ t : b6t_polydisc mr_base, ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω
          (b63d_projection mr_base C f (b6t_polydisc mr_base) Set.Subset.rfl t))
        (Q₀ : LinearMap.BilinForm ℤ (b3_periodLattice ℂ C)) (hQ₀ : b3_IsIntersectionForm ℂ Q₀)
        (Q : (t : b6t_polydisc mr_base) → LinearMap.BilinForm ℤ (b3_periodLattice ℂ
          (b63l_parameterFibre mr_base C (b6t_polydisc mr_base) Set.Subset.rfl t)))
        (hQ : ∀ t, b3_IsIntersectionForm ℂ (Q t))
        (P : (t : b6t_polydisc mr_base) →
          b6m_H1 (b63l_parameterFibre mr_base C (b6t_polydisc mr_base) Set.Subset.rfl t) →ₗ[ℤ]
            b3_periodLattice ℂ
              (b63l_parameterFibre mr_base C (b6t_polydisc mr_base) Set.Subset.rfl t))
        (hP : ∀ (t : b6t_polydisc mr_base) (γ : b3_SmoothLoop ℂ
            (b63l_parameterFibre mr_base C (b6t_polydisc mr_base) Set.Subset.rfl t)),
          P t (b6m_loopClass _ γ) = b3_latticePeriod ℂ _ γ)
        (B : Module.Basis (Fin 12) ℤ (b63l_parameterLattice mr_base C
          (fun g ↦ (hact g).continuous) (b6t_polydisc mr_base) Set.Subset.rfl b63gP_s₀))
        (j : b6t_polydisc mr_base ≃ F.S),
        ∀ t : b6t_polydisc mr_base, F.tuple (j t) = b63g5_tuple ∧
          F.fiber (j t) = b63g5_fiber mr_base C (fun g ↦ (hact g).continuous)
            (b6t_polydisc mr_base) Set.Subset.rfl hG mr_base_mem_chart f hf hsurj hk Q₀ hQ₀ Q hQ
            P hP b63gP_s₀ B t

/-- A marked family has the marked tuple at every index: `j` is surjective. -/
example (F : g32h_PrymFamily) (hF : b63gP_IsMarked F) (s : F.S) : F.tuple s = b63g5_tuple := by
  obtain ⟨_, _, _, _, _, _, _, -, _, _, _, _, _, _, _, _, _, _, _, _, _, _, -, -, -, -, -, -, -,
    _, _, _, _, _, _, _, _, _, _, _, j, hj⟩ := hF
  simpa using (hj (j.symm s)).1

/-- A marked family is indexed by a nonempty type: the polydisc contains `b63gP_s₀`. -/
example (F : g32h_PrymFamily) (hF : b63gP_IsMarked F) : Nonempty F.S := by
  obtain ⟨_, _, _, _, _, _, _, -, _, _, _, _, _, _, _, _, _, _, _, _, _, _, -, -, -, -, -, -, -,
    _, _, _, _, _, _, _, _, _, _, _, j, -⟩ := hF
  exact ⟨j b63gP_s₀⟩

/-! ## The empty family and the named family -/

/-- **The empty family**: index type `Empty`, every field vacuous. Every field of
`g32h_PrymFamily` quantifies over the index type, so this is an element; it supplies the
nonemptiness proof the choice below requires (without an existence witness the choice's value
is unspecified), and it is the degenerate case that `b63gP_exists` excludes.
Source: the fields of `g32h_PrymFamily` (`G32FamilyDefs.lean`); `Empty.elim`. -/
def b63gP_emptyFamily : g32h_PrymFamily where
  S := Empty
  tuple := Empty.elim
  tuple_nielsen := fun s ↦ s.elim
  fiber := Empty.elim
  dim_eq := fun s ↦ s.elim
  hodge := fun s ↦ s.elim
  nondegenerate := fun s ↦ s.elim
  rosati := fun s ↦ s.elim
  positive := fun s ↦ s.elim

/-- The empty family has no fibre, so it is not marked. -/
example : IsEmpty b63gP_emptyFamily.S := inferInstanceAs (IsEmpty Empty)

example : ¬ b63gP_IsMarked b63gP_emptyFamily := by
  rintro ⟨_, _, _, _, _, _, _, -, _, _, _, _, _, _, _, _, _, _, _, _, _, _, -, -, -, -, -, -, -,
    _, _, _, _, _, _, _, _, _, _, _, j, -⟩
  exact (j b63gP_s₀).elim

/-- **The Prym family `P`**: the choice `Classical.epsilon` of an element of `g32h_PrymFamily`
that is marked (`b63gP_IsMarked`) and has a nonempty index type; `b63gP_emptyFamily` supplies the nonemptiness proof required by `epsilon`; without an existence witness, its value is unspecified. Once such an element exists (`b63gP_exists`), the choice is one.
Source: G32 v0.16, Lemma 3.6 (the family `A_ρ(C)` over `Hur°`); `b63gP_IsMarked`; Hilbert's
choice operator, Mathlib `Classical.epsilon_spec`. -/
def b63gP_family : g32h_PrymFamily :=
  @Classical.epsilon g32h_PrymFamily ⟨b63gP_emptyFamily⟩
    (fun F ↦ b63gP_IsMarked F ∧ Nonempty F.S)

/-- The choice property: any marked, nonempty element makes `b63gP_family` one. -/
example (h : ∃ F : g32h_PrymFamily, b63gP_IsMarked F ∧ Nonempty F.S) :
    b63gP_IsMarked b63gP_family ∧ Nonempty b63gP_family.S :=
  @Classical.epsilon_spec g32h_PrymFamily (fun F ↦ b63gP_IsMarked F ∧ Nonempty F.S) h

end HodgeLean.Foundations.Program
