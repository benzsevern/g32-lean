import HodgeLean.Foundations.AlgebraicGeometry.RamifiedNormalization.StageFour.LiteralIntegralCoefficientSlice
import HodgeLean.Foundations.AlgebraicGeometry.RamifiedNormalization.StageFour.LiteralChartSliceRatio

noncomputable section
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.RamifiedNormalization.StageFour

/-- Both actual literal integral-chart fibres retain their original covering points, cover the actual slice, and preserve the two exceptional ratio coordinates. -/
theorem literal_reciprocal_slice_chart_data
    {R A A₂ L : Type} [CommRing R] [CommRing A] [CommRing A₂] [Field L]
    [Algebra ℂ R] [Algebra ℂ A] [Algebra ℂ A₂] [Algebra A L] [Algebra A₂ L]
    [Algebra ℂ L] [IsScalarTower ℂ A L] [IsScalarTower ℂ A₂ L]
    {W X Bbase N : Over (Spec ↧ℂ)} [IsSeparated Bbase.hom]
    (βN : W ⟶ X) (p : X ⟶ Bbase) (x : ComplexPoint Bbase)
    (JN : N ⟶ W) [IsOpenImmersion JN.left]
    (lN : coveringSlice βN p x ⟶ N)
    (hlN : lN ≫ JN = pullback.fst βN (pullback.fst p x))
    (JA : Over.mk (ComplexPoint.affineSpecStructureMap (integralClosure A L)) ⟶ N)
    (JB : Over.mk (ComplexPoint.affineSpecStructureMap (integralClosure A₂ L)) ⟶ N)
    [IsOpenImmersion JA.left] [IsOpenImmersion JB.left]
    (jO : Over.mk (ComplexPoint.affineSpecStructureMap A) ⟶ X)
    (jB : Over.mk (ComplexPoint.affineSpecStructureMap A₂) ⟶ X)
    (hJAbase : JA.left ≫ JN.left ≫ βN.left =
      Spec.map (CommRingCat.ofHom (algebraMap A (integralClosure A L))) ≫ jO.left)
    (hJBbase : JB.left ≫ JN.left ≫ βN.left =
      Spec.map (CommRingCat.ofHom (algebraMap A₂ (integralClosure A₂ L))) ≫ jB.left)
    (hJArange : Set.range (JA.left ≫ JN.left) = βN.left ⁻¹' Set.range jO.left)
    (hJBrange : Set.range (JB.left ≫ JN.left) = βN.left ⁻¹' Set.range jB.left)
    (hcovN : ∀ z : N.left, (∃ a, JA.left a = z) ∨ ∃ b, JB.left b = z)
    (fA : R →ₐ[ℂ] A) (fB : R →ₐ[ℂ] A₂)
    (c : Over.mk (ComplexPoint.affineSpecStructureMap R) ⟶ Bbase) [Mono c]
    (hjAsq : jO ≫ p = Over.homMk (Spec.map (CommRingCat.ofHom fA.toRingHom))
      (ComplexPoint.specMap_comp_affineSpecStructureMap fA) ≫ c)
    (hjBsq : jB ≫ p = Over.homMk (Spec.map (CommRingCat.ofHom fB.toRingHom))
      (ComplexPoint.specMap_comp_affineSpecStructureMap fB) ≫ c)
    (φ : R →ₐ[ℂ] ℂ) (hxφ : Point.map c ((ComplexPoint.affineSpecEquiv R).symm φ) = x)
    (vE vE₂ : ComplexPoint (exceptionalSlice p x) → OnePoint ℂ) (rA : A) (rB : A₂)
    (hcoordA : ∀ z y, Point.map jO y = Point.map (pullback.fst p x) z →
      vE z = ((ComplexPoint.affineSpecEquiv A y rA : ℂ) : OnePoint ℂ))
    (hcoordB : ∀ z y, Point.map jB y = Point.map (pullback.fst p x) z →
      vE₂ z = ((ComplexPoint.affineSpecEquiv A₂ y rB : ℂ) : OnePoint ℂ)) :
    let Fs := coveringSlice βN p x
    let Ps := sliceProjection βN p x
    let As := pullback.fst p x
    let U₁ : Set (ComplexPoint Fs) := {z | (Point.map As (Point.map Ps z)).left
      (IsLocalRing.closedPoint ℂ) ∈ Set.range jO.left}
    let U₂ : Set (ComplexPoint Fs) := {z | (Point.map As (Point.map Ps z)).left
      (IsLocalRing.closedPoint ℂ) ∈ Set.range jB.left}
    ∃ (Hc₁ : integralCoefficientFibre (L := L) fA φ ≃ₜ U₁)
      (Hc₂ : integralCoefficientFibre (L := L) fB φ ≃ₜ U₂),
      (∀ z, Point.map (pullback.fst βN (pullback.fst p x)) (Hc₁ z).val =
        Point.map (JA ≫ JN) ((ComplexPoint.affineSpecEquiv (integralClosure A L)).symm z.val)) ∧
      (∀ z, Point.map (pullback.fst βN (pullback.fst p x)) (Hc₂ z).val =
        Point.map (JB ≫ JN) ((ComplexPoint.affineSpecEquiv (integralClosure A₂ L)).symm z.val)) ∧
      (∀ z : ComplexPoint Fs, z ∈ U₁ ∨ z ∈ U₂) ∧
      (∀ z, vE (Point.map Ps (Hc₁ z).val) =
        ((z.val (algebraMap A (integralClosure A L) rA) : ℂ) : OnePoint ℂ)) ∧
      (∀ z, vE₂ (Point.map Ps (Hc₂ z).val) =
        ((z.val (algebraMap A₂ (integralClosure A₂ L) rB) : ℂ) : OnePoint ℂ)) := by
  let Fs := coveringSlice βN p x
  let Ps := sliceProjection βN p x
  let As := pullback.fst p x
  let aN := pullback.fst βN As
  let iA := JA ≫ JN
  let iB := JB ≫ JN
  haveI : IsOpenImmersion iA.left := by dsimp [iA]; infer_instance
  haveI : IsOpenImmersion iB.left := by dsimp [iB]; infer_instance
  let nA : Over.mk (ComplexPoint.affineSpecStructureMap (integralClosure A L)) ⟶
      Over.mk (ComplexPoint.affineSpecStructureMap A) :=
    Over.homMk (Spec.map (CommRingCat.ofHom (algebraMap A (integralClosure A L))))
      (ComplexPoint.specMap_comp_affineSpecStructureMap (IsScalarTower.toAlgHom ℂ A (integralClosure A L)))
  let nB : Over.mk (ComplexPoint.affineSpecStructureMap (integralClosure A₂ L)) ⟶
      Over.mk (ComplexPoint.affineSpecStructureMap A₂) :=
    Over.homMk (Spec.map (CommRingCat.ofHom (algebraMap A₂ (integralClosure A₂ L))))
      (ComplexPoint.specMap_comp_affineSpecStructureMap (IsScalarTower.toAlgHom ℂ A₂ (integralClosure A₂ L)))
  have hiAbase : nA ≫ jO = iA ≫ βN := by
    apply Over.OverMorphism.ext
    change Spec.map (CommRingCat.ofHom (algebraMap A (integralClosure A L))) ≫ jO.left =
      (JA.left ≫ JN.left) ≫ βN.left
    simpa only [Category.assoc] using hJAbase.symm
  have hiBbase : nB ≫ jB = iB ≫ βN := by
    apply Over.OverMorphism.ext
    change Spec.map (CommRingCat.ofHom (algebraMap A₂ (integralClosure A₂ L))) ≫ jB.left =
      (JB.left ≫ JN.left) ≫ βN.left
    simpa only [Category.assoc] using hJBbase.symm
  have hirA : Set.range iA.left = βN.left ⁻¹' Set.range jO.left := hJArange
  have hirB : Set.range iB.left = βN.left ⁻¹' Set.range jB.left := hJBrange
  obtain ⟨Hc₁, hHc₁⟩ := literal_integral_coefficient_slice (R := R) (A := A) (L := L) βN p x iA jO hiAbase
    fA c hjAsq φ hxφ hirA
  obtain ⟨Hc₂, hHc₂⟩ := literal_integral_coefficient_slice (R := R) (A := A₂) (L := L) βN p x iB jB hiBbase
    fB c hjBsq φ hxφ hirB
  let U₁ : Set (ComplexPoint Fs) := {z | (Point.map As (Point.map Ps z)).left
    (IsLocalRing.closedPoint ℂ) ∈ Set.range jO.left}
  let U₂ : Set (ComplexPoint Fs) := {z | (Point.map As (Point.map Ps z)).left
    (IsLocalRing.closedPoint ℂ) ∈ Set.range jB.left}
  let pA := fun z : integralCoefficientFibre (L := L) fA φ =>
    (ComplexPoint.affineSpecEquiv (integralClosure A L)).symm z.val
  let pB := fun z : integralCoefficientFibre (L := L) fB φ =>
    (ComplexPoint.affineSpecEquiv (integralClosure A₂ L)).symm z.val
  have hpointbase (z : ComplexPoint Fs) : Point.map As (Point.map Ps z) = Point.map βN (Point.map aN z) := by
    rw [← Point.map_comp_apply, ← Point.map_comp_apply]
    exact congrArg (fun k => Point.map k z) (pullback.condition (f := βN) (g := As)).symm
  have hcovU (z : ComplexPoint Fs) : z ∈ U₁ ∨ z ∈ U₂ := by
    have he : JN.left ((Point.map lN z).left (IsLocalRing.closedPoint ℂ)) =
        (Point.map aN z).left (IsLocalRing.closedPoint ℂ) := by
      have hh := congrArg (fun k => (Point.map k z).left (IsLocalRing.closedPoint ℂ)) hlN
      exact hh
    rcases hcovN ((Point.map lN z).left (IsLocalRing.closedPoint ℂ)) with ⟨y, hy⟩ | ⟨y, hy⟩
    · left
      have hh : (Point.map aN z).left (IsLocalRing.closedPoint ℂ) ∈ Set.range iA.left :=
        ⟨y, (congrArg JN.left hy).trans he⟩
      rw [hirA] at hh
      change (Point.map As (Point.map Ps z)).left (IsLocalRing.closedPoint ℂ) ∈ Set.range jO.left
      rw [hpointbase z]
      exact hh
    · right
      have hh : (Point.map aN z).left (IsLocalRing.closedPoint ℂ) ∈ Set.range iB.left :=
        ⟨y, (congrArg JN.left hy).trans he⟩
      rw [hirB] at hh
      change (Point.map As (Point.map Ps z)).left (IsLocalRing.closedPoint ℂ) ∈ Set.range jB.left
      rw [hpointbase z]
      exact hh
  have hratio₁ := literal_chart_slice_ratio (A := A) (L := L)
    (TA := integralCoefficientFibre (L := L) fA φ) βN p x iA jO hiAbase
    (fun z => z.val) (fun z => (Hc₁ z).val) hHc₁ vE rA hcoordA
  have hratio₂ := literal_chart_slice_ratio (A := A₂) (L := L)
    (TA := integralCoefficientFibre (L := L) fB φ) βN p x iB jB hiBbase
    (fun z => z.val) (fun z => (Hc₂ z).val) hHc₂ vE₂ rB hcoordB
  exact ⟨Hc₁, Hc₂, hHc₁, hHc₂, hcovU, hratio₁, hratio₂⟩

end AlgebraicGeometry.RamifiedNormalization.StageFour
