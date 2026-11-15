import HodgeLean.Foundations.Program.SchoenTowerDefs
import HodgeConjecture.Definitions.AlgebraicTopology.Sheaf.Constant
import Mathlib.Topology.LocallyConstant.Algebra
import Mathlib.Topology.Sheaves.Functors
import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import Mathlib.Topology.Sheaves.Abelian

/-! # The covering sheaf and its actual character projector
Sections are locally constant complex functions on inverse images of opens.
The generator acts by precomposition, with the singular pullback convention.
HC no distance; AV milestone no distance.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits TopologicalSpace
open scoped BigOperators
namespace HodgeLean.Foundations.Program

/-- Locally constant functions on inverse images of opens.
Source: Bredon, Sheaf Theory, II.4; G32 v0.16, Lemma 4.3, finite pushforward. -/
def s2c_coverPresheaf {X E : TopCat} (f : X ⟶ E) : TopCat.Presheaf AddCommGrpCat E where
  obj U := AddCommGrpCat.of (LocallyConstant {x : X // f x ∈ U.unop} ℂ)
  map {U V} i := AddCommGrpCat.ofHom (LocallyConstant.comapAddMonoidHom (Z := ℂ)
    ⟨fun x => ⟨x.val, i.unop.le x.property⟩,
      continuous_subtype_val.subtype_mk _⟩)
  map_id _ := by ext; rfl
  map_comp _ _ := by ext; rfl

example {X E : TopCat} (f : X ⟶ E) (U : Opens E) :
    (s2c_coverPresheaf f).obj (.op U) =
      AddCommGrpCat.of (LocallyConstant {x : X // f x ∈ U} ℂ) := rfl

/-- Pullback by the specified generator on the covering presheaf.
Source: G32 v0.16, Lemma 4.3, the residual action on the finite pushforward. -/
def s2c_coverPresheafDeck {X E : TopCat} (f : X ⟶ E) (d : X ⟶ X)
    (hd : d ≫ f = f) : s2c_coverPresheaf f ⟶ s2c_coverPresheaf f where
  app U := AddCommGrpCat.ofHom (LocallyConstant.comapAddMonoidHom (Z := ℂ)
    (show C({x : X // f x ∈ U.unop}, {x : X // f x ∈ U.unop}) from
    ⟨fun x => ⟨d x.val, by
        have hx : f (d x.val) = f x.val := congrArg (fun g : X ⟶ E => g x.val) hd
        rw [hx]; exact x.property⟩,
      by fun_prop⟩))
  naturality := by
    intro U V i
    ext s
    rfl

example {X E : TopCat} (f : X ⟶ E) (d : X ⟶ X) (hd : d ≫ f = f)
    (U : Opens E) (s : LocallyConstant {x : X // f x ∈ U} ℂ)
    (x : {x : X // f x ∈ U}) :
    (show LocallyConstant {x : X // f x ∈ U} ℂ from
      (s2c_coverPresheafDeck f d hd).app (.op U) s) x =
      s ⟨d x.val, by
        have hx : f (d x.val) = f x.val := congrArg (fun g : X ⟶ E => g x.val) hd
        rw [hx]; exact x.property⟩ := rfl

/-- Multiplication of section values by a complex coefficient.
Source: G32 v0.16, Lemma 4.3, complex character projector. -/
def s2c_coverPresheafScalar {X E : TopCat} (f : X ⟶ E) (c : ℂ) :
    s2c_coverPresheaf f ⟶ s2c_coverPresheaf f where
  app _ := AddCommGrpCat.ofHom (c • AddMonoidHom.id _)
  naturality := by
    intro U V i
    ext s
    rfl

example {X E : TopCat} (f : X ⟶ E) (c : ℂ) (U : Opens E)
    (s : LocallyConstant {x : X // f x ∈ U} ℂ) :
    (s2c_coverPresheafScalar f c).app (.op U) s = c • s := rfl

/-- The covering sheaf, using sheafification of its explicit section presheaf.
Source: Bredon, Sheaf Theory, I.1 and II.4; G32 v0.16, Lemma 4.3. -/
def s2c_coverSheaf {X E : TopCat} (f : X ⟶ E) : TopCat.Sheaf AddCommGrpCat E :=
  (presheafToSheaf (Opens.grothendieckTopology E) AddCommGrpCat).obj (s2c_coverPresheaf f)

example {X E : TopCat} (f : X ⟶ E) : s2c_coverSheaf f =
    (presheafToSheaf (Opens.grothendieckTopology E) AddCommGrpCat).obj
      (s2c_coverPresheaf f) := rfl

/-- The same generator on the associated covering sheaf.
Source: G32 v0.16, Lemma 4.3. -/
def s2c_coverSheafDeck {X E : TopCat} (f : X ⟶ E) (d : X ⟶ X)
    (hd : d ≫ f = f) : s2c_coverSheaf f ⟶ s2c_coverSheaf f :=
  (presheafToSheaf _ _).map (s2c_coverPresheafDeck f d hd)

example {X E : TopCat} (f : X ⟶ E) (d : X ⟶ X) (hd : d ≫ f = f) :
    s2c_coverSheafDeck f d hd = (presheafToSheaf _ _).map
      (s2c_coverPresheafDeck f d hd) := rfl

/-- Coefficient multiplication on the covering sheaf.
Source: G32 v0.16, Lemma 4.3. -/
def s2c_coverSheafScalar {X E : TopCat} (f : X ⟶ E) (c : ℂ) :
    s2c_coverSheaf f ⟶ s2c_coverSheaf f :=
  (presheafToSheaf _ _).map (s2c_coverPresheafScalar f c)

example {X E : TopCat} (f : X ⟶ E) (c : ℂ) :
    s2c_coverSheafScalar f c = (presheafToSheaf _ _).map
      (s2c_coverPresheafScalar f c) := rfl

/-- Averaging projector for the eigenvalue ζ of the pullback generator.
Source: G32 v0.16, Lemma 4.3; Serre, Linear Representations of Finite Groups, §2. -/
def s2c_characterProjector {X E : TopCat} (f : X ⟶ E) (d : X ⟶ X)
    (hd : d ≫ f = f) (m : ℕ) (ζ : ℂ) : s2c_coverSheaf f ⟶ s2c_coverSheaf f :=
  ∑ t ∈ Finset.range m, s2c_coverSheafScalar f ((m : ℂ)⁻¹ * ζ ^ (-(t : ℤ))) ≫
    ((End.of (s2c_coverSheafDeck f d hd)) ^ t).asHom

example {X E : TopCat} (f : X ⟶ E) (d : X ⟶ X) (hd : d ≫ f = f) (ζ : ℂ) :
    s2c_characterProjector f d hd 0 ζ = 0 := by
  simp only [s2c_characterProjector, Finset.range_zero, Finset.sum_empty]

/-- The image of the character projector on the actual covering sheaf.
Source: G32 v0.16, Lemma 4.3, character summand. -/
def s2c_characterSheaf {X E : TopCat} (f : X ⟶ E) (d : X ⟶ X)
    (hd : d ≫ f = f) (m : ℕ) (ζ : ℂ) : TopCat.Sheaf AddCommGrpCat E :=
  image (s2c_characterProjector f d hd m ζ)

example {X E : TopCat} (f : X ⟶ E) (d : X ⟶ X) (hd : d ≫ f = f)
    (m : ℕ) (ζ : ℂ) : s2c_characterSheaf f d hd m ζ =
      image (s2c_characterProjector f d hd m ζ) := rfl

end HodgeLean.Foundations.Program
