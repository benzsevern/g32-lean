import Mathlib.Algebra.Category.Ring.Basic
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-! # Kernels in pushouts of surjective ring maps
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
open CategoryTheory

namespace AlgebraicGeometry.Conormal

/-- A pushout of a surjective ring map has the extended kernel. -/
lemma pushout_kernel_eq
    {R A S B : CommRingCat.{0}} (p : R ⟶ A) (f : R ⟶ S)
    (k : A ⟶ B) (q : S ⟶ B) (sq : IsPushout p f k q)
    (hp : Function.Surjective p.hom) :
    (RingHom.ker p.hom).map f.hom = RingHom.ker q.hom := by
  let J := (RingHom.ker p.hom).map f.hom
  have hle : J ≤ RingHom.ker q.hom := by
    rw [Ideal.map_le_iff_le_comap, RingHom.comap_ker]
    intro x hx
    have h := congrArg (fun t : R ⟶ B => t x) sq.w
    change k (p x) = q (f x) at h
    change q (f x) = 0
    rw [← h, hx, map_zero]
  let v : S ⟶ CommRingCat.of (S ⧸ J) := CommRingCat.ofHom (Ideal.Quotient.mk J)
  have hv : RingHom.ker p.hom ≤ RingHom.ker (f ≫ v).hom := by
    intro x hx
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_map_of_mem f.hom hx)
  let l : A ⟶ CommRingCat.of (S ⧸ J) :=
    CommRingCat.ofHom (p.hom.liftOfSurjective hp ⟨(f ≫ v).hom, hv⟩)
  have hl : p ≫ l = f ≫ v :=
    CommRingCat.hom_ext (RingHom.liftOfSurjective_comp p.hom hp _)
  let d := sq.desc l v hl
  apply le_antisymm hle
  intro x hx
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  have hd := congrArg (fun t : S ⟶ CommRingCat.of (S ⧸ J) => t x) (sq.inr_desc l v hl)
  change d (q x) = Ideal.Quotient.mk J x at hd
  rw [hx, map_zero] at hd
  exact hd.symm

end AlgebraicGeometry.Conormal
