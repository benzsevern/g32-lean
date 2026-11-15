import HodgeLean.Foundations.Program.SchoenCycleStep1Symmetric
import HodgeLean.Foundations.AlgebraicGeometry.SingularCycles.Reduced
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-! # Identifying an actual smooth fibre from the original point image -/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace HodgeLean.Foundations.Program.G32Native
open HodgeLean.Foundations.Program

/-- An immersion into a smooth fibre is its actual scheme isomorphism when
its original point image exhausts that fibre.
Source: EGA I, 4.5.10; a surjective immersion into a reduced scheme. -/
theorem residual_fibre_immersion_isIso_of_point_image
    (P B J : Over (Spec ↧ℂ)) (a : B ⟶ J) [Smooth a.left]
    (z : Over.mk (𝟙 (Spec ↧ℂ)) ⟶ J) [IsClosedImmersion z.left]
    (i : P ⟶ B)
    (l : P.left ⟶ pullback a.left z.left) [IsClosedImmersion l]
    (hl₁ : l ≫ pullback.fst a.left z.left = i.left)
    (hl₂ : l ≫ pullback.snd a.left z.left = P.hom)
    (himage : ∀ q : ComplexPoint B, Point.map a q = z →
      ∃ p : ComplexPoint P, Point.map i p = q) : IsIso l := by
  let F : Over (Spec ↧ℂ) := Over.mk (pullback.snd a.left z.left)
  let L : P ⟶ F := Over.homMk l hl₂
  let j : F ⟶ B := Over.homMk (pullback.fst a.left z.left) (by
    change pullback.fst a.left z.left ≫ B.hom = pullback.snd a.left z.left
    calc
      _ = (pullback.fst a.left z.left ≫ a.left) ≫ J.hom := by
        rw [Category.assoc, Over.w a]
      _ = (pullback.snd a.left z.left ≫ z.left) ≫ J.hom :=
        congrArg (fun t => t ≫ J.hom) pullback.condition
      _ = _ := by
        rw [Category.assoc, Over.w z]
        change pullback.snd a.left z.left ≫ 𝟙 _ = _
        exact Category.comp_id _)
  have hpoint : Function.Surjective (Point.map L) := by
    intro q
    have hq : Point.map a (Point.map j q) = z := by
      apply Over.OverMorphism.ext
      change q.left ≫ pullback.fst a.left z.left ≫ a.left = z.left
      rw [pullback.condition, ← Category.assoc]
      have hbase := Over.w q
      change q.left ≫ pullback.snd a.left z.left = 𝟙 (Spec ↧ℂ) at hbase
      rw [hbase]
      exact Category.id_comp z.left
    obtain ⟨p, hp⟩ := himage (Point.map j q) hq
    refine ⟨p, ?_⟩
    apply Over.OverMorphism.ext
    apply (cancel_mono (pullback.fst a.left z.left)).mp
    have h := congrArg (fun t : _ ⟶ B => t.left) hp
    change p.left ≫ i.left = q.left ≫ pullback.fst a.left z.left at h
    change (p.left ≫ l) ≫ pullback.fst a.left z.left = q.left ≫ pullback.fst a.left z.left
    exact (Category.assoc _ _ _).trans ((congrArg (fun t => p.left ≫ t) hl₁).trans h)
  letI : Smooth F.hom := inferInstanceAs (Smooth (pullback.snd a.left z.left))
  letI : IsClosedImmersion L.left := inferInstanceAs (IsClosedImmersion l)
  letI : IsReduced (pullback a.left z.left) :=
    SingularCycles.smooth_reduced_integral F.hom
  letI : Surjective l := s2e_step1_surjective_of_complexPoint_surjective P F L hpoint
  exact isIso_of_isClosedImmersion_of_surjective l

#print axioms residual_fibre_immersion_isIso_of_point_image
end HodgeLean.Foundations.Program.G32Native
