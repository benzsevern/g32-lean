import HodgeLean.Foundations.Curves.Picard.Families.Defs
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree

/-! # Invertible module sheaves and pointed curve families

The objects are module sheaves on actual schemes. Tensor products are sheafified
sectionwise tensor products. No Picard representing scheme is selected here.
HC no distance; AV milestone no distance.
-/

noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped MonoidalCategory
namespace HodgeLean.Foundations.Curves.Picard.LineBundles
open Families

/-- The structure module on a scheme.
Source: Stacks Project, Tag 01CR. -/
abbrev unit (X : Scheme) : X.Modules := SheafOfModules.unit X.ringCatSheaf

example (X : Scheme) : unit X ⟶ unit X := 𝟙 _

/-- Tensor product over the structure sheaf, with sheafification included.
Source: Stacks Project, Tag 01CA. -/
def tensor {X : Scheme} (M N : X.Modules) : X.Modules :=
  (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).obj
    (PresheafOfModulesOfCommRing.Monoidal.tensorObj
      (R := X.presheaf) M.val N.val)

example (X : Scheme) : X.Modules := tensor (unit X) (unit X)

/-- A rank-one module sheaf with local triviality at every point.
Source: Stacks Project, Tag 01CR, invertible modules. -/
structure Line (X : Scheme) where
  module : X.Modules
  trivial : ∀ x : X, ∃ U : X.Opens, x ∈ U ∧
    Nonempty (module.restrict U.ι ≅ unit U.toScheme)

example {X : Scheme} (L : Line X) (x : X) :
    ∃ U : X.Opens, x ∈ U ∧ Nonempty (L.module.restrict U.ι ≅ unit U.toScheme) :=
  L.trivial x

/-- The trivial invertible module, retaining its sheaf structure.
Source: Stacks Project, Tag 01CR. -/
def trivialLine (X : Scheme) : Line X where
  module := unit X
  trivial _x := ⟨⊤, trivial, ⟨Scheme.Modules.restrictUnitIso _⟩⟩

example (X : Scheme) : (trivialLine X).module = unit X := rfl

/-- The ideal module O(-D), as the kernel of restriction to the actual subscheme.
Source: Stacks Project, Tags 01HO and 01WQ. -/
def idealModule {X : Scheme} (I : X.IdealSheafData) : X.Modules :=
  kernel (SheafOfModules.unitToPushforwardObjUnit I.subschemeι.toRingCatSheafHom)

example {X : Scheme} (I : X.IdealSheafData) :
    idealModule I ⟶ unit X := kernel.ι _

/-- The section of the product specified by a complex base point.
Source: Kleiman, The Picard scheme, §4, rigidification along a section. -/
def pointSection (C T : Over (Spec ↧ℂ))
    (b : Over.mk (𝟙 (Spec ↧ℂ)) ⟶ C) : T.left ⟶ Product C T :=
  pullback.lift (T.hom ≫ b.left) (𝟙 _) (by simp)

example (C T : Over (Spec ↧ℂ)) (b : Over.mk (𝟙 (Spec ↧ℂ)) ⟶ C) :
    pointSection C T b ≫ pullback.snd C.hom T.hom = 𝟙 _ := by
  simp [pointSection]

/-- A line with a specified trivialization along the base-point section.
Source: Kleiman, The Picard scheme, §4. -/
structure Rigidified (C T : Over (Spec ↧ℂ))
    (b : Over.mk (𝟙 (Spec ↧ℂ)) ⟶ C) where
  line : Line (Product C T)
  rigid : (Scheme.Modules.pullback (pointSection C T b)).obj line.module ≅ unit T.left

example {C T : Over (Spec ↧ℂ)} {b} (L : Rigidified C T b) :
    (Scheme.Modules.pullback (pointSection C T b)).obj L.line.module ⟶ unit T.left :=
  L.rigid.hom

/-- A morphism preserving the specified base-point trivializations.
Source: Kleiman, The Picard scheme, §4. -/
structure RigidIso {C T : Over (Spec ↧ℂ)} {b} (L M : Rigidified C T b) where
  iso : L.line.module ≅ M.line.module
  respects : (Scheme.Modules.pullback (pointSection C T b)).map iso.hom ≫ M.rigid.hom =
    L.rigid.hom

example {C T : Over (Spec ↧ℂ)} {b} (L : Rigidified C T b) : RigidIso L L :=
  ⟨Iso.refl _, by simp⟩

/-- Transition of two frames of the same restricted module.
Source: Hartshorne, Algebraic Geometry, II.5, transition functions. -/
def transition {X : Scheme} {M : X.Modules} {U : X.Opens}
    (e f : M.restrict U.ι ≅ unit U.toScheme) : unit U.toScheme ≅ unit U.toScheme :=
  e.symm ≪≫ f

example {X : Scheme} {M : X.Modules} {U : X.Opens}
    (e : M.restrict U.ι ≅ unit U.toScheme) : transition e e = Iso.refl _ := by
  ext; simp [transition]

/-- Zariski descent data in frames, on all subordinate opens.
The restriction law and the cocycle are required for actual units of O_X.
Source: Stacks Project, Tags 00AK and 023T. -/
structure Cocycle (X : Scheme) where
  I : Type
  opens : I → X.Opens
  covers : ∀ x : X, ∃ i, x ∈ opens i
  value : ∀ i j (V : X.Opens), V ≤ opens i → V ≤ opens j → Γ(X, V)ˣ
  restrict : ∀ i j (V W : X.Opens) (hWi : W ≤ opens i) (hWj : W ≤ opens j)
    (hVi : V ≤ opens i) (hVj : V ≤ opens j) (hWV : W ≤ V),
    Units.map (X.presheaf.map (homOfLE hWV).op).hom (value i j V hVi hVj) =
      value i j W hWi hWj
  identity : ∀ i V (h : V ≤ opens i), value i i V h h = 1
  cocycle : ∀ i j k V (hi : V ≤ opens i) (hj : V ≤ opens j) (hk : V ≤ opens k),
    value i j V hi hj * value j k V hj hk = value i k V hi hk

example {X : Scheme} (c : Cocycle X) (i : c.I) (V : X.Opens) (h : V ≤ c.opens i) :
    c.value i i V h h = 1 := c.identity i V h

/-- Compatible local coordinates for the line specified by a transition cocycle.
Source: Stacks Project, Tag 00AK, construction by matching sections. -/
structure Matching {X : Scheme} (c : Cocycle X) (V : X.Opens) where
  value : ∀ i, Γ(X, V ⊓ c.opens i)
  compatible : ∀ i j,
    (X.presheaf.map (homOfLE (show V ⊓ c.opens i ⊓ c.opens j ≤ V ⊓ c.opens j from
      le_inf (inf_le_left.trans inf_le_left) inf_le_right)).op).hom (value j) =
    (c.value i j (V ⊓ c.opens i ⊓ c.opens j)
      (inf_le_left.trans inf_le_right) inf_le_right : Γ(X, V ⊓ c.opens i ⊓ c.opens j)) *
    (X.presheaf.map (homOfLE inf_le_left).op).hom (value i)

example {X : Scheme} (c : Cocycle X) (V : X.Opens) : Matching c V :=
  ⟨fun _ => 0, by intro i j; simp⟩

/-- Equal-degree divisor presentations for a rigidified line, locally in the parameter.
This is a divisor-presented degree-zero family, without a Picard representability claim.
Source: Kleiman, The Picard scheme, §4; Milne, Jacobian Varieties, §4. -/
structure DegreeZero (C T : Over (Spec ↧ℂ))
    (b : Over.mk (𝟙 (Spec ↧ℂ)) ⟶ C) where
  bundle : Rigidified C T b
  presentation : ∀ t : T.left, ∃ U : T.left.Opens, t ∈ U ∧
    ∃ (n : ℕ) (D F : Family C (Over.mk (U.ι ≫ T.hom)) n),
      Nonempty (tensor
        ((Scheme.Modules.pullback (productMap C (Over.homMk U.ι))).obj bundle.line.module)
        (idealModule D.ideal) ≅ idealModule F.ideal)

example {C T : Over (Spec ↧ℂ)} {b} (L : DegreeZero C T b) :
    (Scheme.Modules.pullback (pointSection C T b)).obj L.bundle.line.module ≅ unit T.left :=
  L.bundle.rigid

end HodgeLean.Foundations.Curves.Picard.LineBundles
