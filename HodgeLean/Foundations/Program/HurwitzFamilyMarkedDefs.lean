import HodgeLean.Foundations.Program.HurwitzFamilyAnalyticDefs
import HodgeLean.Adapters.HolomorphicPeriodsCocycleProofs

/-! # B6-2c: integral homology of the actual product fibres

Implication from the product topology of B6-2b to explicit fibre coordinates and
functorial integral homology maps. No analytic structure is selected here.
HC no distance; AV milestone no distance.
-/

noncomputable section
open CategoryTheory
open AlgebraicTopology AlgebraicTopology.Singular
open scoped Manifold ContDiff

namespace HodgeLean.Foundations.Program

/-- The actual fibre of the product projection, including its filled points.
Source: Fulton, Ann. Math. 90 (1969), 542–575, local Hurwitz construction;
Harris–Morrison, *Moduli of Curves*, §1.G. -/
def b6m_Fibre (b : Fin 10 → ℂ) (C : Type) (t : b6t_polydisc b) :=
  {q : b6t_polydisc b × C // q.1 = t}

instance (b : Fin 10 → ℂ) (C : Type) [TopologicalSpace C] (t : b6t_polydisc b) :
    TopologicalSpace (b6m_Fibre b C t) := inferInstanceAs (TopologicalSpace {q : b6t_polydisc b × C // q.1 = t})

example (b : Fin 10 → ℂ) (C : Type) (t : b6t_polydisc b) (x : C) :
    b6m_Fibre b C t := ⟨(t, x), rfl⟩

/-- Coordinates on a filled fibre, using the unchanged product topology.
Source: Harris–Morrison, *Moduli of Curves*, §1.G, topological marking. -/
def b6m_coordinate (b : Fin 10 → ℂ) (C : Type) [TopologicalSpace C]
    (t : b6t_polydisc b) : b6m_Fibre b C t ≃ₜ C where
  toFun q := q.val.2
  invFun x := ⟨(t, x), rfl⟩
  left_inv q := by apply Subtype.ext; exact Prod.ext q.property.symm rfl
  right_inv _ := rfl
  continuous_toFun := continuous_snd.comp continuous_subtype_val
  continuous_invFun := (continuous_const.prodMk continuous_id).subtype_mk _

example (b : Fin 10 → ℂ) (C : Type) [TopologicalSpace C]
    (t : b6t_polydisc b) (x : C) : (b6m_coordinate b C t).symm x = ⟨(t, x), rfl⟩ := rfl

/-- Filled topological transport induced by the identity on the B6-2a covering domain.
Source: Fulton, Ann. Math. 90 (1969), 542–575; Harris–Morrison, §1.G. -/
def b6m_transport (b : Fin 10 → ℂ) (C : Type) [TopologicalSpace C]
    (s t : b6t_polydisc b) : b6m_Fibre b C s ≃ₜ b6m_Fibre b C t :=
  (b6m_coordinate b C s).trans (b6m_coordinate b C t).symm

example (b : Fin 10 → ℂ) (C : Type) [TopologicalSpace C]
    (s t : b6t_polydisc b) (x : C) :
    b6m_transport b C s t ⟨(s, x), rfl⟩ = ⟨(t, x), rfl⟩ := rfl

/-- Integral degree-one singular homology.
Source: Hatcher, *Algebraic Topology*, §2.1; `AlgebraicTopology.Singular.Homology`. -/
abbrev b6m_H1 (C : Type) [TopologicalSpace C] :=
  Homology ℤ (TopCat.of C) 1

example (C : Type) [TopologicalSpace C] : Module ℤ (b6m_H1 C) := inferInstance

/-- The integral homology equivalence induced by a specified homeomorphism.
Source: Hatcher, *Algebraic Topology*, §2.1, functoriality; Mathlib `Functor.mapIso`. -/
def b6m_H1Equiv {C D : Type} [TopologicalSpace C] [TopologicalSpace D]
    (e : C ≃ₜ D) : b6m_H1 C ≃ₗ[ℤ] b6m_H1 D :=
  (((singularHomologyFunctor.{0} (ModuleCat.{0} ℤ) 1).obj (ModuleCat.of ℤ ℤ)).mapIso
    (TopCat.isoOfHomeo (X := TopCat.of C) (Y := TopCat.of D) e)).toLinearEquiv

example {C D : Type} [TopologicalSpace C] [TopologicalSpace D] (e : C ≃ₜ D) :
    (b6m_H1Equiv e).toLinearMap = homologyMap ℤ 1 (TopCat.ofHom ⟨e, e.continuous⟩) := rfl

/-- Integral class of a smooth periodic loop, via its actual singular cycle.
Source: Hatcher, *Algebraic Topology*, §2.A; B3 smooth-loop period convention. -/
def b6m_loopClass (C : Type) [TopologicalSpace C] [ChartedSpace ℂ C]
    [IsManifold 𝓘(ℂ, ℂ) ω C] (γ : b3_SmoothLoop ℂ C) : b6m_H1 C :=
  ((SingularChainComplex ℤ (TopCat.of C)).sc 1).moduleCatHomologyClass
    (HodgeLean.Adapters.loopCycle ℤ
      ⟨γ.2.1.lift, by
        rw [← QuotientAddGroup.isOpenQuotientMap_mk.continuous_comp_iff]
        exact γ.2.2.continuous⟩)

example (C : Type) [TopologicalSpace C] [ChartedSpace ℂ C]
    [IsManifold 𝓘(ℂ, ℂ) ω C] (γ : b3_SmoothLoop ℂ C) :
    b6m_H1 C := b6m_loopClass C γ

/-- Deck action on the actual filled fibre in its product coordinates.
Source: Harris–Morrison, *Moduli of Curves*, §1.G, equivariant marking. -/
def b6m_deck (b : Fin 10 → ℂ) (G C : Type) [Group G]
    [TopologicalSpace C] [MulAction G C]
    (hC : ∀ g : G, Continuous (fun x : C ↦ g • x))
    (t : b6t_polydisc b) (g : G) : C(b6m_Fibre b C t, b6m_Fibre b C t) :=
  ⟨fun q ↦ ⟨(t, g • q.val.2), rfl⟩,
    (continuous_const.prodMk ((hC g).comp
      (continuous_snd.comp continuous_subtype_val))).subtype_mk _⟩

example (b : Fin 10 → ℂ) (G C : Type) [Group G]
    [TopologicalSpace C] [MulAction G C]
    (hC : ∀ g : G, Continuous (fun x : C ↦ g • x))
    (t : b6t_polydisc b) (g : G) (x : C) :
    b6m_deck b G C hC t g ⟨(t, x), rfl⟩ = ⟨(t, g • x), rfl⟩ := rfl

/-- The product fibres and their geometric transport as a topological functor.
Source: Fulton, Ann. Math. 90 (1969), 542–575; Harris–Morrison, §1.G.
A path keeps the filled surface coordinate fixed throughout the product family. -/
def b6m_topologicalFibres (b : Fin 10 → ℂ) (C : Type) [TopologicalSpace C] :
    FundamentalGroupoid (b6t_polydisc b) ⥤ TopCat where
  obj t := TopCat.of (b6m_Fibre b C t.as)
  map {s t} _ := TopCat.ofHom ⟨b6m_transport b C s.as t.as,
    (b6m_transport b C s.as t.as).continuous⟩
  map_id t := by
    ext q
    apply Subtype.ext
    exact Prod.ext q.property.symm rfl
  map_comp _ _ := by ext q; rfl

example (b : Fin 10 → ℂ) (C : Type) [TopologicalSpace C]
    (t : b6t_polydisc b) :
    (b6m_topologicalFibres b C).obj (.mk t) = TopCat.of (b6m_Fibre b C t) := rfl

/-- The integral local system obtained by applying singular homology to geometric transport.
Source: Hatcher, *Algebraic Topology*, §2.1; Harris–Morrison, §1.G;
G32 v0.16, §5, the integral lattice underlying Prym variation. -/
def b6m_integralLocalSystem (b : Fin 10 → ℂ) (C : Type) [TopologicalSpace C] :
    FundamentalGroupoid (b6t_polydisc b) ⥤ ModuleCat ℤ :=
  b6m_topologicalFibres b C ⋙
    (singularHomologyFunctor.{0} (ModuleCat.{0} ℤ) 1).obj (ModuleCat.of ℤ ℤ)

example (b : Fin 10 → ℂ) (C : Type) [TopologicalSpace C]
    (t : b6t_polydisc b) :
    (b6m_integralLocalSystem b C).obj (.mk t) = b6m_H1 (b6m_Fibre b C t) := rfl

end HodgeLean.Foundations.Program
