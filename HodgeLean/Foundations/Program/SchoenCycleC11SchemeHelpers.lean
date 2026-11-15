import HodgeLean.Foundations.Program.SchoenCycleC11SubProofs
import HodgeConjecture.Lemmas.AlgebraicGeometry.ComplexPoint.ClosedImmersion
import Mathlib.AlgebraicGeometry.Morphisms.FlatMono
import Mathlib.AlgebraicGeometry.Morphisms.IsIso

/-! # Finite morphisms and complex points
Implication from finite morphisms and point functions to scheme properties.
HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.ComplexPoint
namespace HodgeLean.Foundations.Program

/-- Point surjectivity detects surjectivity for a finite complex morphism.
Source: Hartshorne, Algebraic Geometry, II.3.14, density of rational points. -/
theorem s2e_c11_surjective_of_point_surjective
    (X Y : Over (Spec ↧ℂ)) [LocallyOfFiniteType Y.hom]
    (f : X ⟶ Y) [IsFinite f.left]
    (hs : Function.Surjective (Point.map f)) : Surjective f.left := by
  have hr : IsClosed (Set.range f.left) := f.left.isClosedMap.isClosed_range
  have h := s2e_c11_complex_points_detect_complement_aux Y 1
    (fun _ ↦ Set.range f.left) (fun _ ↦ hr) (by
      intro y
      obtain ⟨x, rfl⟩ := hs y
      exact ⟨0, x.underlying, (Point.underlying_map f x).symm⟩)
  exact ⟨fun y ↦ (h y).choose_spec⟩

/-- Bijectivity on complex points detects an isomorphism of finite etale schemes.
Source: SGA 1, Expose I, Proposition 5.1, finite etale rank one. -/
theorem s2e_c11_finite_etale_point_bijective_isIso
    (X Y : Over (Spec ↧ℂ)) [LocallyOfFiniteType X.hom]
    [LocallyOfFiniteType Y.hom] (f : X ⟶ Y) [IsFinite f.left] [Etale f.left]
    (hb : Function.Bijective (Point.map f)) : IsIso f.left := by
  have : Surjective f.left := s2e_c11_surjective_of_point_surjective X Y f hb.2
  let P : Over (Spec ↧ℂ) := Over.mk (pullback.fst f.left f.left ≫ X.hom)
  let d : X ⟶ P := Over.homMk (pullback.diagonal f.left) (by simp [P])
  have : LocallyOfFiniteType P.hom := by
    change LocallyOfFiniteType (pullback.fst f.left f.left ≫ X.hom)
    infer_instance
  have hd : Function.Surjective (Point.map d) := by
    intro z
    let x : Point ℂ X := Over.homMk (z.left ≫ pullback.fst f.left f.left)
      (by simpa only [P, Over.mk_hom, Category.assoc] using Over.w z)
    let y : Point ℂ X := Over.homMk (z.left ≫ pullback.snd f.left f.left) (by
      calc
        (z.left ≫ pullback.snd f.left f.left) ≫ X.hom =
            z.left ≫ (pullback.snd f.left f.left ≫ f.left) ≫ Y.hom := by
          simp only [Category.assoc, Over.w f]
        _ = z.left ≫ (pullback.fst f.left f.left ≫ f.left) ≫ Y.hom := by
          rw [pullback.condition]
        _ = z.left ≫ P.hom := by simp only [P, Over.mk_hom, Category.assoc, Over.w f]
        _ = _ := Over.w z)
    have hxy : Point.map f x = Point.map f y := by
      apply Over.OverMorphism.ext
      exact Category.assoc _ _ _ |>.trans
        ((congrArg (fun g ↦ z.left ≫ g) (pullback.condition (f := f.left) (g := f.left))).trans
          (Category.assoc _ _ _).symm)
    have heq : x.left = y.left := congrArg Over.Hom.left (hb.1 hxy)
    refine ⟨x, ?_⟩
    apply Over.OverMorphism.ext
    apply pullback.hom_ext
    · simp [d, x, Point.map, Category.assoc]
    · simpa [d, x, y, Point.map, Category.assoc] using heq
  have : IsFinite d.left := by
    change IsFinite (pullback.diagonal f.left)
    infer_instance
  have : Surjective (pullback.diagonal f.left) :=
    s2e_c11_surjective_of_point_surjective X P d hd
  have : IsIso (pullback.diagonal f.left) := Flat.isIso_of_surjective_of_mono _
  have : Mono f.left := (pullback.isIso_diagonal_iff f.left).mp inferInstance
  exact Flat.isIso_of_surjective_of_mono f.left

/-- An algebraic open with the exact points of a section maps isomorphically to the base.
Source: SGA 1, Expose I, Proposition 5.1, finite etale rank one. -/
theorem s2e_c11_selected_open_isIso
    (X Y : Over (Spec ↧ℂ)) [LocallyOfFiniteType X.hom]
    [LocallyOfFiniteType Y.hom] (f : X ⟶ Y) [IsFinite f.left] [Etale f.left]
    (s : Point ℂ Y → Point ℂ X) (hs : ∀ y, Point.map f (s y) = y)
    (U : X.left.Opens) (hU : IsClosed (U : Set X.left))
    (hpoints : Point.underlying ⁻¹' (U : Set X.left) = Set.range s) :
    IsIso (U.ι ≫ f.left) := by
  have : IsClosedImmersion U.ι := IsClosedImmersion.of_isPreimmersion _ (by
    simpa only [Scheme.Opens.range_ι] using hU)
  let A : Over (Spec ↧ℂ) := Over.mk (U.ι ≫ X.hom)
  let i : A ⟶ X := Over.homMk U.ι rfl
  let g : A ⟶ Y := i ≫ f
  have : LocallyOfFiniteType A.hom := by
    change LocallyOfFiniteType (U.ι ≫ X.hom)
    infer_instance
  have : IsFinite g.left := inferInstanceAs (IsFinite (U.ι ≫ f.left))
  have : Etale g.left := inferInstanceAs (Etale (U.ι ≫ f.left))
  have hi : IsClosedImmersion i.left := inferInstanceAs (IsClosedImmersion U.ι)
  have hr : Set.range (Point.map i) = Set.range s := by
    rw [range_map_of_closedImmersion i]
    change Point.underlying ⁻¹' Set.range U.ι = Set.range s
    rw [Scheme.Opens.range_ι]
    exact hpoints
  have hgs (x : Point ℂ A) : Point.map i x = s (Point.map g x) := by
    obtain ⟨y, hy⟩ := hr ▸ Set.mem_range_self x
    have heq : y = Point.map g x := by
      rw [← hs y, hy]
      rfl
    exact hy.symm.trans (congrArg s heq)
  have hb : Function.Bijective (Point.map g) := by
    constructor
    · intro x y hxy
      apply map_injective_of_mono i
      rw [hgs x, hgs y, hxy]
    · intro y
      obtain ⟨x, hx⟩ := hr.symm ▸ Set.mem_range_self y
      refine ⟨x, ?_⟩
      change Point.map f (Point.map i x) = y
      rw [hx]
      exact hs y
  exact s2e_c11_finite_etale_point_bijective_isIso A Y g hb

/-- Inversion of the selected algebraic sheet recovers the specified point section.
Source: SGA 1, Expose I, Proposition 5.1, and inverse morphism identities. -/
theorem s2e_c11_section_from_selected_open
    (X Y : Over (Spec ↧ℂ)) [LocallyOfFiniteType X.hom]
    [LocallyOfFiniteType Y.hom] (f : X ⟶ Y) [IsFinite f.left] [Etale f.left]
    (s : Point ℂ Y → Point ℂ X) (hs : ∀ y, Point.map f (s y) = y)
    (U : X.left.Opens) (hU : IsClosed (U : Set X.left))
    (hpoints : Point.underlying ⁻¹' (U : Set X.left) = Set.range s) :
    ∃ j : Y ⟶ X, Point.map j = s ∧ j ≫ f = 𝟙 _ := by
  have : IsClosedImmersion U.ι := IsClosedImmersion.of_isPreimmersion _ (by
    simpa only [Scheme.Opens.range_ι] using hU)
  let A : Over (Spec ↧ℂ) := Over.mk (U.ι ≫ X.hom)
  let i : A ⟶ X := Over.homMk U.ι rfl
  let g : A ⟶ Y := i ≫ f
  have hg : IsIso g.left := s2e_c11_selected_open_isIso X Y f s hs U hU hpoints
  have : IsIso ((Over.forget (Spec ↧ℂ)).map g) := hg
  have : IsIso g := isIso_of_reflects_iso g (Over.forget _)
  let j : Y ⟶ X := inv g ≫ i
  have hj : j ≫ f = 𝟙 _ := by
    change (inv g ≫ i) ≫ f = _
    rw [Category.assoc]
    exact IsIso.inv_hom_id g
  refine ⟨j, ?_, hj⟩
  funext y
  have hi : IsClosedImmersion i.left := inferInstanceAs (IsClosedImmersion U.ι)
  have hr : Set.range (Point.map i) = Set.range s := by
    rw [range_map_of_closedImmersion i]
    change Point.underlying ⁻¹' Set.range U.ι = Set.range s
    rw [Scheme.Opens.range_ι]
    exact hpoints
  have hm : Point.map j y ∈ Set.range (Point.map i) :=
    ⟨Point.map (inv g) y, rfl⟩
  obtain ⟨z, hz⟩ := hr ▸ hm
  have hzy : z = y := by
    calc
      z = Point.map f (s z) := (hs z).symm
      _ = Point.map f (Point.map j y) := congrArg (Point.map f) hz
      _ = y := by rw [← Point.map_comp_apply, hj, Point.map_id]
  exact hz.symm.trans (congrArg s hzy)

end HodgeLean.Foundations.Program
