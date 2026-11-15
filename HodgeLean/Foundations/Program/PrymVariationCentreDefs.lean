import HodgeLean.Foundations.Program.PrymVariationLattice

/-! # B6-3d: central operators and eigenspaces

Data on the actual parameter fibres and their saturated period lattices.
No restricted operator or geometric model is selected from a statement.
HC no distance; AV milestone no distance.
-/

noncomputable section
open CategoryTheory AlgebraicTopology.Singular HodgeLean.Papers
open scoped Manifold ContDiff TensorProduct
namespace HodgeLean.Foundations.Program
attribute [local instance] b4cov_sphChartedSpace b4cov_sph_isManifold

/-- The central matrix scalar acting on integral singular homology.
Source: G32 v0.16, §3.3 and Appendix A; Hatcher, §2.1. -/
def b63d_centre (b : Fin 10 → ℂ) (C : Type) [TopologicalSpace C]
    [MulAction b4b_Group C]
    (hC : ∀ g : b4b_Group, Continuous (fun x : C ↦ g • x))
    (V : Set (Fin 10 → ℂ)) (hV : V ⊆ b6t_polydisc b) (t : V) :
    b6m_H1 (b63l_parameterFibre b C V hV t) →ₗ[ℤ] b6m_H1 (b63l_parameterFibre b C V hV t) :=
  ∑ g : b4b_Group, if b4b_toMatrix g = g32h_omega • (1 : Matrix (Fin 4) (Fin 4) ℂ)
    then homologyMap ℤ 1 (TopCat.ofHom (b6m_deck b b4b_Group C hC
      ⟨t.val, hV t.property⟩ g)) else 0

example (b : Fin 10 → ℂ) (C : Type) [TopologicalSpace C]
    [MulAction b4b_Group C]
    (hC : ∀ g : b4b_Group, Continuous (fun x : C ↦ g • x))
    (V : Set (Fin 10 → ℂ)) (hV : V ⊆ b6t_polydisc b) (t : V) : b63d_centre b C hC V hV t 0 = 0 := map_zero _

/-- The integral expression for the square root of minus three on ambient homology.
Source: G32 v0.16, §3.3, the expression 1 + 2ω. -/
def b63d_operator (b : Fin 10 → ℂ) (C : Type) [TopologicalSpace C]
    [MulAction b4b_Group C]
    (hC : ∀ g : b4b_Group, Continuous (fun x : C ↦ g • x))
    (V : Set (Fin 10 → ℂ)) (hV : V ⊆ b6t_polydisc b) (t : V) :
    b6m_H1 (b63l_parameterFibre b C V hV t) →ₗ[ℤ] b6m_H1 (b63l_parameterFibre b C V hV t) :=
  LinearMap.id + 2 • b63d_centre b C hC V hV t

example (b : Fin 10 → ℂ) (C : Type) [TopologicalSpace C]
    [MulAction b4b_Group C]
    (hC : ∀ g : b4b_Group, Continuous (fun x : C ↦ g • x))
    (V : Set (Fin 10 → ℂ)) (hV : V ⊆ b6t_polydisc b) (t : V) : b63d_operator b C hC V hV t 0 = 0 := map_zero _

/-- The ambient period expression for 1 + 2ω.
Source: G32 v0.16, §3.3; Birkenhake–Lange, §12.2. -/
def b63d_periodOperator (C : Type) [TopologicalSpace C] [ChartedSpace ℂ C]
    [IsManifold 𝓘(ℂ, ℂ) ω C] [MulAction b4b_Group C]
    (hG : ∀ g : b4b_Group, ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω (fun x : C ↦ g • x)) :
    b3_periodLattice ℂ C →ₗ[ℤ] b3_periodLattice ℂ C :=
  LinearMap.id + 2 • (b4b_centreAct C hG).toIntLinearMap

example (C : Type) [TopologicalSpace C] [ChartedSpace ℂ C]
    [IsManifold 𝓘(ℂ, ℂ) ω C] [MulAction b4b_Group C]
    (hG : ∀ g : b4b_Group, ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω (fun x : C ↦ g • x)) : b63d_periodOperator C hG 0 = 0 := map_zero _

/-- The central eigenpart of the saturated period filtration, computed in the ambient space.
Source: G32 v0.16, Proposition 3.1 and Lemma 3.3; Birkenhake–Lange, §12.2. -/
def b63d_eigenF (C : Type) [TopologicalSpace C] [ChartedSpace ℂ C]
    [IsManifold 𝓘(ℂ, ℂ) ω C] [MulAction b4b_Group C]
    (hG : ∀ g : b4b_Group, ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω (fun x : C ↦ g • x)) (z : ℂ) :
    Submodule ℂ (ℂ ⊗[ℤ] b63l_periodLattice C) :=
  b63l_periodF C ⊓ (LinearMap.ker
    ((b4b_centreAct C hG).toIntLinearMap.baseChange ℂ - z • LinearMap.id)).comap
      ((b63l_periodLattice C).subtype.baseChange ℂ)

example (C : Type) [TopologicalSpace C] [ChartedSpace ℂ C]
    [IsManifold 𝓘(ℂ, ℂ) ω C] [MulAction b4b_Group C]
    (hG : ∀ g : b4b_Group, ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω (fun x : C ↦ g • x)) (z : ℂ) :
    (0 : ℂ ⊗[ℤ] b63l_periodLattice C) ∈ b63d_eigenF C hG z := Submodule.zero_mem _

/-- The actual moving sphere projection in the fixed topological marking.
Source: Fulton, Ann. Math. 90 (1969), 542–575; `b6a_map`. -/
def b63d_projection (b : Fin 10 → ℂ) (C : Type) (f : C → OnePoint ℂ)
    (V : Set (Fin 10 → ℂ)) (hV : V ⊆ b6t_polydisc b) (t : V) :
    b63l_parameterFibre b C V hV t → OnePoint ℂ :=
  fun q ↦ b6a_map b f q.val

example (b : Fin 10 → ℂ) (C : Type) (f : C → OnePoint ℂ)
    (V : Set (Fin 10 → ℂ)) (hV : V ⊆ b6t_polydisc b) (t : V)
    (q : b63l_parameterFibre b C V hV t) :
    b63d_projection b C f V hV t q = b6t_sphere b q.val.1.val (f q.val.2) := rfl

end HodgeLean.Foundations.Program
