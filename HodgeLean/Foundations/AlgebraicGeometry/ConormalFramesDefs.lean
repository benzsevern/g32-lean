import HodgeLean.Foundations.Program.SchoenTowerConormalDefs
import Mathlib.RingTheory.Smooth.Basic
import Mathlib.Algebra.Module.Projective
import Mathlib.RingTheory.LocalRing.Module
import Mathlib.AlgebraicGeometry.Morphisms.Etale

/-! # General conormal modules and frames
Source: Hartshorne, Algebraic Geometry, II.5 and II.8.
HC no distance; AV milestone no distance. -/

noncomputable section
open CategoryTheory AlgebraicGeometry

namespace AlgebraicGeometry.Conormal

/-- The existing kernel ideal module, with its original definitional identity.
Source: Hartshorne, Algebraic Geometry, II.5. -/
abbrev idealModule {Q W : Scheme} (i : Q ⟶ W) : W.Modules :=
  HodgeLean.Foundations.Program.s2c_idealModule i

/-- The existing pullback ideal module representing the conormal sheaf.
Source: Hartshorne, Algebraic Geometry, II.8. -/
abbrev sheaf {Q W : Scheme} (i : Q ⟶ W) : Q.Modules :=
  HodgeLean.Foundations.Program.s2c_conormal i

example {Q W : Scheme} (i : Q ⟶ W) :
    idealModule i = HodgeLean.Foundations.Program.s2c_idealModule i := rfl

example {Q W : Scheme} (i : Q ⟶ W) :
    sheaf i = (Scheme.Modules.pullback i).obj (idealModule i) := rfl

end AlgebraicGeometry.Conormal
