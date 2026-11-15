import HodgeLean.Foundations.Mathlib.GenericFlatSmoothProofs

/-!
# Generic flatness and generic smoothness (FROZEN SPEC)

This specification isolates implications from finite-type and Noetherian hypotheses to generic
flatness, and from a dominant morphism whose source is smooth over a characteristic-zero field to
generic smoothness. It claims no effective description of the open sets and no transversality or
cycle-class result. HC no distance; AV milestone no distance.
-/

noncomputable section

open CategoryTheory TopologicalSpace

namespace AlgebraicGeometry

universe u

variable {X Y : Scheme.{u}}

/-- A finite-type morphism to an integral locally Noetherian scheme is flat after restriction to
a dense open subset of the target.
Source: EGA IV, Théorème 6.9.1; Stacks Project, Tag 052B. -/
theorem gfs_exists_flat_over_dense_open (f : X ⟶ Y)
    [LocallyOfFiniteType f] [QuasiCompact f] [IsIntegral Y] [IsLocallyNoetherian Y] :
    ∃ U : Y.Opens, Dense (U : Set Y) ∧ Flat (f ∣_ U) :=
  gfs_exists_flat_over_dense_open_aux f

example (f : X ⟶ Y) [LocallyOfFiniteType f] [QuasiCompact f]
    [IsIntegral Y] [IsLocallyNoetherian Y] :
    ∃ U : Y.Opens, Dense (U : Set Y) ∧ Flat (f ∣_ U) :=
  gfs_exists_flat_over_dense_open f

/-- The generic point of the source lies in the smooth locus of a dominant map from a smooth
integral variety in characteristic zero.
Source: Hartshorne, *Algebraic Geometry*, III, Corollary 10.7; EGA IV, 17.15. -/
theorem gfs_genericPoint_mem_smoothLocus
    {k : Type u} [Field k] [CharZero k]
    (sX : X ⟶ Spec ↧k) (sY : Y ⟶ Spec ↧k) (f : X ⟶ Y)
    [IsIntegral X] [IsIntegral Y] [LocallyOfFinitePresentation f]
    [LocallyOfFiniteType sX] [LocallyOfFiniteType sY] [Smooth sX]
    (hf : f ≫ sY = sX) [IsDominant f] :
    genericPoint X ∈ f.smoothLocus :=
  gfs_genericPoint_mem_smoothLocus_aux sX sY f hf

example {k : Type u} [Field k] [CharZero k]
    (sX : X ⟶ Spec ↧k) (sY : Y ⟶ Spec ↧k) (f : X ⟶ Y)
    [IsIntegral X] [IsIntegral Y] [LocallyOfFinitePresentation f]
    [LocallyOfFiniteType sX] [LocallyOfFiniteType sY] [Smooth sX]
    (hf : f ≫ sY = sX) [IsDominant f] :
    genericPoint X ∈ f.smoothLocus :=
  gfs_genericPoint_mem_smoothLocus sX sY f hf

/-- The fibre over the generic point of the target lies in the smooth locus of a dominant map
from a smooth integral variety in characteristic zero.
Source: Hartshorne, *Algebraic Geometry*, III, Corollary 10.7; EGA IV, 17.15. -/
theorem gfs_genericFiber_subset_smoothLocus
    {k : Type u} [Field k] [CharZero k]
    (sX : X ⟶ Spec ↧k) (sY : Y ⟶ Spec ↧k) (f : X ⟶ Y)
    [IsIntegral X] [IsIntegral Y] [LocallyOfFinitePresentation f] [QuasiCompact f]
    [LocallyOfFiniteType sX] [LocallyOfFiniteType sY] [Smooth sX]
    (hf : f ≫ sY = sX) [IsDominant f] :
    ∀ x : X, f x = genericPoint Y → x ∈ f.smoothLocus :=
  gfs_genericFiber_subset_smoothLocus_aux sX sY f hf

example {k : Type u} [Field k] [CharZero k]
    (sX : X ⟶ Spec ↧k) (sY : Y ⟶ Spec ↧k) (f : X ⟶ Y)
    [IsIntegral X] [IsIntegral Y] [LocallyOfFinitePresentation f] [QuasiCompact f]
    [LocallyOfFiniteType sX] [LocallyOfFiniteType sY] [Smooth sX]
    (hf : f ≫ sY = sX) [IsDominant f] :
    ∀ x : X, f x = genericPoint Y → x ∈ f.smoothLocus :=
  gfs_genericFiber_subset_smoothLocus sX sY f hf

/-- info: 'AlgebraicGeometry.gfs_genericFiber_subset_smoothLocus' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms gfs_genericFiber_subset_smoothLocus

/-- The nonsmooth locus of a dominant map from a smooth integral variety in characteristic zero
does not have dense image in the target.
Source: Hartshorne, *Algebraic Geometry*, III, Corollary 10.7; EGA IV, 17.15. -/
theorem gfs_nonsmoothLocus_not_dense_over_target
    {k : Type u} [Field k] [CharZero k]
    (sX : X ⟶ Spec ↧k) (sY : Y ⟶ Spec ↧k) (f : X ⟶ Y)
    [IsIntegral X] [IsIntegral Y] [LocallyOfFinitePresentation f] [QuasiCompact f]
    [LocallyOfFiniteType sX] [LocallyOfFiniteType sY] [Smooth sX]
    (hf : f ≫ sY = sX) [IsDominant f] :
    closure (f '' ((f.smoothLocus : Set X)ᶜ)) ≠ Set.univ :=
  gfs_nonsmoothLocus_not_dense_over_target_aux sX sY f hf

example {k : Type u} [Field k] [CharZero k]
    (sX : X ⟶ Spec ↧k) (sY : Y ⟶ Spec ↧k) (f : X ⟶ Y)
    [IsIntegral X] [IsIntegral Y] [LocallyOfFinitePresentation f] [QuasiCompact f]
    [LocallyOfFiniteType sX] [LocallyOfFiniteType sY] [Smooth sX]
    (hf : f ≫ sY = sX) [IsDominant f] :
    closure (f '' ((f.smoothLocus : Set X)ᶜ)) ≠ Set.univ :=
  gfs_nonsmoothLocus_not_dense_over_target sX sY f hf

/-- A dominant map from a smooth integral variety over a characteristic-zero field is smooth
after restriction to a dense open subset of its integral target.
Source: Hartshorne, *Algebraic Geometry*, III, Corollary 10.7; EGA IV, 17.15. -/
theorem gfs_exists_smooth_over_dense_open
    {k : Type u} [Field k] [CharZero k]
    (sX : X ⟶ Spec ↧k) (sY : Y ⟶ Spec ↧k) (f : X ⟶ Y)
    [IsIntegral X] [IsIntegral Y] [LocallyOfFinitePresentation f] [QuasiCompact f]
    [LocallyOfFiniteType sX] [LocallyOfFiniteType sY] [Smooth sX]
    (hf : f ≫ sY = sX) [IsDominant f] :
    ∃ U : Y.Opens, Dense (U : Set Y) ∧ Smooth (f ∣_ U) :=
  gfs_exists_smooth_over_dense_open_aux sX sY f hf

example {k : Type u} [Field k] [CharZero k]
    (sX : X ⟶ Spec ↧k) (sY : Y ⟶ Spec ↧k) (f : X ⟶ Y)
    [IsIntegral X] [IsIntegral Y] [LocallyOfFinitePresentation f] [QuasiCompact f]
    [LocallyOfFiniteType sX] [LocallyOfFiniteType sY] [Smooth sX]
    (hf : f ≫ sY = sX) [IsDominant f] :
    ∃ U : Y.Opens, Dense (U : Set Y) ∧ Smooth (f ∣_ U) :=
  gfs_exists_smooth_over_dense_open sX sY f hf

end AlgebraicGeometry
