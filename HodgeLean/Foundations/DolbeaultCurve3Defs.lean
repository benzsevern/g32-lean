import Mathlib.Topology.Sheaves.Flasque

/-! # Soft sheaves and lifting near closed sets (FROZEN DEFINITIONS)

Two predicates on sheaves of abelian groups on a topological space `T`, phrased with open sets only:

* `IsSoft F`: every section of `F` over an open neighbourhood of a closed set `K` agrees, on a
  smaller open neighbourhood of `K`, with a global section. On a paracompact space a section over
  the closed set `K` is the germ along `K` of a section over an open neighbourhood (Godement,
  Théorème II.3.3.1), so this is softness in the sense of Godement and Bredon.
* `LiftsNear g K c`: for a morphism of sheaves `g : B ⟶ C`, the section `c` of `C` over an open set
  lifts through `g` on some open neighbourhood of `K`.
-/

noncomputable section
open CategoryTheory TopologicalSpace Opposite

universe u

namespace HodgeLean.Foundations

variable {T : TopCat.{u}}

/-- A sheaf of abelian groups `F` on `T` is soft when, for every closed `K ⊆ T`, every section of `F`
over an open `U ⊇ K` agrees with the restriction of a global section on some open `V` with
`K ⊆ V ⊆ U`. On a paracompact space this says that every section over a closed set extends to a
global section.
Source: Godement, *Topologie algébrique et théorie des faisceaux*, Hermann (1958), II.3.1
(définition des faisceaux mous) and Théorème II.3.3.1 (sections over a closed set of a paracompact
space are germs of sections over open neighbourhoods); Bredon, *Sheaf Theory*, 2nd ed., GTM 170
(1997), II.9.1 and II.9.5. -/
def IsSoft (F : TopCat.Sheaf AddCommGrpCat.{u} T) : Prop :=
  ∀ (K : Set T) (U : Opens T), IsClosed K → K ⊆ U → ∀ s : F.obj.obj (op U),
    ∃ (V : Opens T) (hV : V ≤ U), K ⊆ V ∧ ∃ t : F.obj.obj (op ⊤),
      F.obj.map (homOfLE le_top : V ⟶ ⊤).op t = F.obj.map (homOfLE hV).op s

/-- The condition is automatic for sections that are already global. -/
example (F : TopCat.Sheaf AddCommGrpCat.{u} T) (K : Set T) (s : F.obj.obj (op ⊤)) :
    ∃ (V : Opens T) (hV : V ≤ ⊤), K ⊆ V ∧ ∃ t : F.obj.obj (op ⊤),
      F.obj.map (homOfLE le_top : V ⟶ ⊤).op t = F.obj.map (homOfLE hV).op s :=
  ⟨⊤, le_rfl, fun _ _ => trivial, s, rfl⟩

/-- For a morphism of sheaves `g : B ⟶ C`, a set `K ⊆ T` and a section `c` of `C` over an open `U`,
`c` lifts through `g` near `K`: there are an open `V` with `K ⊆ V ⊆ U` and a section `b` of `B`
over `V` with `g b = c` on `V`.
Source: Godement, *Topologie algébrique et théorie des faisceaux*, II.3.5 (proof of Théorème
II.3.5.2); Bredon, *Sheaf Theory*, 2nd ed., proof of Theorem II.9.9. -/
def LiftsNear {B C : TopCat.Sheaf AddCommGrpCat.{u} T} (g : B ⟶ C) (K : Set T) {U : Opens T}
    (c : C.obj.obj (op U)) : Prop :=
  ∃ (V : Opens T) (hV : V ≤ U), K ⊆ V ∧ ∃ b : B.obj.obj (op V),
    g.hom.app (op V) b = C.obj.map (homOfLE hV).op c

/-- A section in the image of `g` lifts near every subset of its domain. -/
example {B C : TopCat.Sheaf AddCommGrpCat.{u} T} (g : B ⟶ C) {U : Opens T} (K : Set T)
    (hK : K ⊆ U) (b : B.obj.obj (op U)) : LiftsNear g K (g.hom.app (op U) b) :=
  ⟨U, le_rfl, hK, b, by simp⟩

end HodgeLean.Foundations
