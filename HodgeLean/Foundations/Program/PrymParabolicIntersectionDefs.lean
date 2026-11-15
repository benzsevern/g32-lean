import HodgeLean.Foundations.Program.PrymParabolicProjected
import HodgeLean.Foundations.Singular.Cup

/-! # Definitions for stage H4, geometric part, first stage

On the lifted complex `X̃(b4b_root)` and its step-B realization in the filling `C`:

- the scalar Alexander–Whitney cup product of two cellular `1`-cochains, evaluated on the
  orientation chain `hg2_orient` (`hga_cupEval`);
- the transport of a `Δ`-map along a continuous map (`hga_mapDelta`), used for the product
  coordinate of a parameter fibre (`hga_fibreMap`);
- the singular `2`-chain of the orientation chain (`hga_fundChain`) and its class in `H₂`
  (`hga_fundClass`); it is a cycle because `∂₂ hg2_orient = 0` (`hga_bd2_orient`, from H3b's
  `hg2_cycles2`, which has a body);
- the B3 intersection form of a fibre pulled back to cellular `H₁` through `hg9_toFibre` and a
  period comparison (`hga_cellIntersection`), and the associated Weil value
  `B(a, Jw) + √−3 B(a, w)` on the saturated cellular lattice (`hga_cellWeil`).

Nothing here compares a cup product with an intersection form, identifies a fundamental class
or fixes an orientation sign; those are the statements of `PrymParabolicIntersection.lean`.
HC no distance; AV milestone no distance.
-/

noncomputable section

open CategoryTheory AlgebraicTopology AlgebraicTopology.Singular Convexity
open scoped Manifold ContDiff TensorProduct

namespace HodgeLean.Foundations.Program

/-! ## The scalar cellular cup evaluation -/

/-- The Alexander–Whitney cup product of two scalar `1`-cochains of `X̃(g)` evaluated on the
orientation chain: `Σ_τ hg2_orient(τ) · α(face₂ τ) · β(face₀ τ)`, the front edge `[v₀, v₁]` and
the back edge `[v₁, v₂]` of each triangle.
Source: Hatcher, *Algebraic Topology*, §3.2 (cup product on a Δ-complex); `hg2_orient`,
`hg2_face2`, `hg2_face0`. -/
def hga_cupEval (R : Type*) [CommRing R] {G : Type*} [Group G] [Fintype G] {r : ℕ}
    (g : Fin r → G) (α β : hg2_Edge G r → R) : R :=
  hg2_orient.sum fun τ n => (n : R) * (α (hg2_face2 τ) * β (hg2_face0 g τ))

example (R : Type*) [CommRing R] {G : Type*} [Group G] [Fintype G] {r : ℕ} (g : Fin r → G)
    (β : hg2_Edge G r → R) : hga_cupEval R g 0 β = 0 := by
  simp [hga_cupEval]

/-! ## Transport of `Δ`-maps and the fibre realization -/

/-- The composite of a `Δ`-map with a continuous map: triangles, edges and vertices are composed
with `φ`; faces and endpoints are preserved.
Source: Hatcher, *Algebraic Topology*, §2.1 (singular simplices push forward); `hg8_DeltaMap`. -/
def hga_mapDelta {G : Type} [Group G] {r : ℕ} {g : Fin r → G} {T T' : Type}
    [TopologicalSpace T] [TopologicalSpace T'] (F : hg8_DeltaMap g T) (φ : C(T, T')) :
    hg8_DeltaMap g T' where
  tri τ := φ.comp (F.tri τ)
  edge ε := φ.comp (F.edge ε)
  vert v := φ (F.vert v)
  faces τ := by
    obtain ⟨h0, h1, h2⟩ := F.faces τ
    exact ⟨congrArg φ.comp h0, congrArg φ.comp h1, congrArg φ.comp h2⟩
  ends ε := ⟨congrArg φ (F.ends ε).1, congrArg φ (F.ends ε).2⟩

example {G : Type} [Group G] {r : ℕ} {g : Fin r → G} {T : Type} [TopologicalSpace T]
    (F : hg8_DeltaMap g T) (v : hg2_Vert g) :
    (hga_mapDelta F (ContinuousMap.id T)).vert v = F.vert v := rfl

/-- The realization of `X̃(g)` in the actual parameter fibre: the cells of `F` composed with the
inverse product coordinate, the same map that `hg9_toFibre` uses on `H₁`.
Source: `b6m_coordinate`, `hg9_toFibre`; Harris–Morrison, *Moduli of Curves*, §1.G. -/
def hga_fibreMap {G : Type} [Group G] {r : ℕ} {g : Fin r → G} {C : Type} [TopologicalSpace C]
    (F : hg8_DeltaMap g C) (V : Set (Fin 10 → ℂ)) (hV : V ⊆ b6t_polydisc mr_base) (t : V) :
    hg8_DeltaMap g (b63l_parameterFibre mr_base C V hV t) :=
  hga_mapDelta F ⟨(b6m_coordinate mr_base C ⟨t.val, hV t.property⟩).symm,
    (b6m_coordinate mr_base C ⟨t.val, hV t.property⟩).symm.continuous⟩

example {G : Type} [Group G] {r : ℕ} {g : Fin r → G} {C : Type} [TopologicalSpace C]
    (F : hg8_DeltaMap g C) (V : Set (Fin 10 → ℂ)) (hV : V ⊆ b6t_polydisc mr_base) (t : V)
    (v : hg2_Vert g) :
    (hga_fibreMap F V hV t).vert v = ⟨(⟨t.val, hV t.property⟩, F.vert v), rfl⟩ := rfl

/-! ## The fundamental chain and class -/

/-- `∂₂ hg2_orient = 0` on the complex of the G32 root.
Source: `hg2_cycles2` (with a body), `b63d_root_product`, `b63d_root_subgroup`. -/
theorem hga_bd2_orient : hg2_bd2 ℤ b4b_root hg2_orient = 0 := by
  have h : hg2_orient ∈ LinearMap.ker (hg2_bd2 ℤ b4b_root) := by
    rw [hg2_cycles2 b4b_root b63d_root_product b63d_root_subgroup]
    exact Submodule.mem_span_singleton_self _
  exact h

/-- The singular `2`-chain `Σ_τ hg2_orient(τ) [tri τ]` of a `Δ`-map of `X̃(b4b_root)`.
Source: Hatcher, *Algebraic Topology*, §3.3 (fundamental cycles of triangulated surfaces);
`hg5_chain2`, `hg2_orient`. -/
def hga_fundChain {T : Type} [TopologicalSpace T] (F : hg8_DeltaMap b4b_root T) :
    Simplicial.ChainGroup ℤ (TopCat.toSSet.obj (TopCat.of T)) 2 :=
  hg5_chain2 F.tri hg2_orient

example {T : Type} [TopologicalSpace T] (F : hg8_DeltaMap b4b_root T) :
    hga_fundChain F = hg5_chain2 F.tri hg2_orient := rfl

theorem hga_d_fundChain {T : Type} [TopologicalSpace T] (F : hg8_DeltaMap b4b_root T) (j : ℕ) :
    ((SingularChainComplex ℤ (TopCat.of T)).d 2 j).hom (hga_fundChain F) = 0 := by
  by_cases hj : j = 1
  · subst hj
    change Simplicial.boundary ℤ 1 (hg5_chain2 F.tri hg2_orient) = 0
    rw [hg5_bd_chain2 F.tri F.edge _ _ _ F.faces hg2_orient]
    change hg5_chain1 F.edge (hg2_bd2 ℤ b4b_root hg2_orient) = 0
    rw [hga_bd2_orient, map_zero]
  · rw [HomologicalComplex.shape _ _ _ (by simp only [ComplexShape.down_Rel]; omega)]
    rfl

/-- The class in `H₂(T; ℤ)` of the singular orientation cycle.
Source: Hatcher, *Algebraic Topology*, §3.3 (the fundamental class); `hga_fundChain`. -/
def hga_fundClass {T : Type} [TopologicalSpace T] (F : hg8_DeltaMap b4b_root T) :
    Homology ℤ (TopCat.of T) 2 :=
  ((SingularChainComplex ℤ (TopCat.of T)).sc 2).moduleCatHomologyClass
    ⟨hga_fundChain F, hga_d_fundChain F _⟩

example {T : Type} [TopologicalSpace T] (F : hg8_DeltaMap b4b_root T) :
    hga_fundClass F = ((SingularChainComplex ℤ (TopCat.of T)).sc 2).moduleCatHomologyClass
      ⟨hga_fundChain F, hga_d_fundChain F _⟩ := rfl

/-! ## The pulled-back intersection form and the cellular Weil value -/

/-- The bilinear form `(x, y) ↦ Q(P(e x), P(e y))` on cellular `H₁(X̃(b4b_root); ℤ)`, with
`e = hg9_toFibre` the step-C comparison into the fibre at `t`, `P` a period comparison and `Q` a
form on the period lattice of that fibre.
Source: Farkas–Kra, *Riemann Surfaces*, Ch. III (the intersection form on `H₁`); `hg9_toFibre`,
`b63e_singularQ` (the same pullback on the saturated singular lattice). -/
def hga_cellIntersection {C : Type} [TopologicalSpace C] (F : hg8_DeltaMap b4b_root C)
    (V : Set (Fin 10 → ℂ)) (hV : V ⊆ b6t_polydisc mr_base) (t : V)
    [ChartedSpace ℂ (b63l_parameterFibre mr_base C V hV t)]
    [IsManifold 𝓘(ℂ, ℂ) ω (b63l_parameterFibre mr_base C V hV t)]
    (P : b6m_H1 (b63l_parameterFibre mr_base C V hV t) →ₗ[ℤ]
      b3_periodLattice ℂ (b63l_parameterFibre mr_base C V hV t))
    (Q : LinearMap.BilinForm ℤ (b3_periodLattice ℂ (b63l_parameterFibre mr_base C V hV t))) :
    LinearMap.BilinForm ℤ (hg2_H1 ℤ b4b_root) :=
  Q.compl₁₂ (P ∘ₗ hg9_toFibre F V hV t) (P ∘ₗ hg9_toFibre F V hV t)

example {C : Type} [TopologicalSpace C] (F : hg8_DeltaMap b4b_root C)
    (V : Set (Fin 10 → ℂ)) (hV : V ⊆ b6t_polydisc mr_base) (t : V)
    [ChartedSpace ℂ (b63l_parameterFibre mr_base C V hV t)]
    [IsManifold 𝓘(ℂ, ℂ) ω (b63l_parameterFibre mr_base C V hV t)]
    (P : b6m_H1 (b63l_parameterFibre mr_base C V hV t) →ₗ[ℤ]
      b3_periodLattice ℂ (b63l_parameterFibre mr_base C V hV t))
    (Q : LinearMap.BilinForm ℤ (b3_periodLattice ℂ (b63l_parameterFibre mr_base C V hV t)))
    (x y : hg2_H1 ℤ b4b_root) :
    hga_cellIntersection F V hV t P Q x y = Q (P (hg9_toFibre F V hV t x))
      (P (hg9_toFibre F V hV t y)) := rfl

/-- The Weil value `B(a, J w) + √−3 · B(a, w) ∈ K` of an integral form `B` on the saturated
cellular lattice, with `J = hg6_cellOperator = 1 + 2Z`; the convention of `weilHermitian`
(`E(x, Jy) + ω E(x, y)`, conjugate-linear in `x`).
Source: van Geemen, LNM 1594, §5.2; `weilHermitian`, `b64b_latticeH`, `hg6_cellOperator`. -/
def hga_cellWeil (B : LinearMap.BilinForm ℤ (hg2_H1 ℤ b4b_root)) (a w : hg6_cellLattice) : hp_K :=
  ((B a (hg6_cellOperator w) : ℤ) : hp_K) + QuadraticAlgebra.omega * ((B a w : ℤ) : hp_K)

example (a w : hg6_cellLattice) : hga_cellWeil 0 a w = 0 := by
  simp [hga_cellWeil]

end HodgeLean.Foundations.Program
