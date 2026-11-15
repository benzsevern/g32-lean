import HodgeLean.Foundations.Program.SchoenCycleC1NormalizationRestrictionHelpers
import HodgeLean.Foundations.Program.SchoenCycleC1NormalizationMapHelpers
import HodgeLean.Foundations.Program.SchoenCycleC1GenericOpenHelpers
import HodgeConjecture.Lemmas.AlgebraicGeometry.ComplexPoint.Open

/-! Singleton fibres on the actual isomorphic normalization opens. -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open HodgeLean.Foundations.Program
namespace HodgeLean.Foundations.QuotientDuality

theorem point_fibre_injective_of_open_iso
    (X Y : Over (Spec ↧ℂ)) (f : X ⟶ Y)
    (A : X.left.Opens) (B : Y.left.Opens) (E : A.toScheme ≅ B.toScheme)
    (hE : E.hom ≫ B.ι = A.ι ≫ f.left)
    (hpre : ∀ z : ComplexPoint X, Point.map f z ∈ Point.overOpen B → z ∈ Point.overOpen A)
    (x : ComplexPoint X) (hx : Point.map f x ∈ Point.overOpen B) :
    ∀ z, Point.map f z = Point.map f x → z = x := by
  intro z hz
  have hxA := hpre x hx
  have hzA := hpre z (by rw [hz]; exact hx)
  let u := liftToOpen X A z hzA
  let v := liftToOpen X A x hxA
  have huvE : u ≫ E.hom = v ≫ E.hom := by
    apply (cancel_mono B.ι).mp
    calc
      (u ≫ E.hom) ≫ B.ι = z.left ≫ f.left := by
        rw [Category.assoc, hE, ← Category.assoc]
        exact congrArg (fun t => t ≫ f.left) (liftToOpen_fac X A z hzA)
      _ = x.left ≫ f.left := congrArg Over.Hom.left hz
      _ = (v ≫ E.hom) ≫ B.ι := by
        rw [Category.assoc, hE, ← Category.assoc]
        exact congrArg (fun t => t ≫ f.left) (liftToOpen_fac X A x hxA).symm
  have huv : u = v := (cancel_mono E.hom).mp huvE
  apply Over.OverMorphism.ext
  exact (liftToOpen_fac X A z hzA).symm.trans
    ((congrArg (fun t => t ≫ A.ι) huv).trans (liftToOpen_fac X A x hxA))

theorem normalization_transition_singleton_fibre
    {K : Type} [Field K] (X Y : Over (Spec ↧ℂ))
    [IsIntegral X.left] [IsIntegral Y.left] [IsSeparated Y.hom]
    (f : Spec (CommRingCat.of K) ⟶ X.left)
    (g : Spec (CommRingCat.of K) ⟶ Y.left)
    [QuasiCompact f] [QuasiSeparated f] [IsDominant f]
    [QuasiCompact g] [QuasiSeparated g] [IsDominant g]
    (b : X ⟶ Y) (hfg : f ≫ b.left = g)
    (w : s2b_normalizationOver X f ⟶ s2b_normalizationOver Y g)
    (hw : f.toNormalization ≫ w.left = g.toNormalization)
    (V : Y.left.Opens) (hV : (V : Set Y.left).Nonempty)
    [IsIso (b.left ∣_ V)]
    (x : ComplexPoint (s2b_normalizationOver X f))
    (hx : Point.map (s2b_normalizationMap X f ≫ b) x ∈ Point.overOpen V) :
    ∀ z, Point.map w z = Point.map w x → z = x := by
  let U := b.left ⁻¹ᵁ V
  have hU : (U : Set X.left).Nonempty := by
    obtain ⟨y, hy⟩ := hV
    obtain ⟨x, _⟩ := (b.left ∣_ V).surjective ⟨y, hy⟩
    exact ⟨x.val, x.property⟩
  obtain ⟨fU, hfqc, hfqs, hf⟩ := s2e_c1_generic_source_lift_to_open X.left f U hU
  obtain ⟨gV, hgqc, hgqs, hg⟩ := s2e_c1_generic_source_lift_to_open Y.left g V hV
  letI := hfqc
  letI := hfqs
  letI := hgqc
  letI := hgqs
  let e := asIso (b.left ∣_ V)
  have hb : e.hom ≫ V.ι = U.ι ≫ b.left := morphismRestrict_ι b.left V
  have he : fU ≫ e.hom = gV := by
    rw [← cancel_mono V.ι, Category.assoc, hb,
      ← Category.assoc, hf, hg, hfg]
  have hwb := s2e_c1_normalization_transition_over X Y b f g hfg w hw
  have hwb' : w.left ≫ g.fromNormalization = f.fromNormalization ≫ b.left :=
    congrArg Over.Hom.left hwb
  obtain ⟨E, hE⟩ := s2e_c1_normalization_transition_open_iso f g b.left w.left hw hwb'
    U V e (morphismRestrict_ι b.left V) fU gV hf hg he
  apply point_fibre_injective_of_open_iso (s2b_normalizationOver X f)
    (s2b_normalizationOver Y g) w (f.fromNormalization ⁻¹ᵁ U)
    (g.fromNormalization ⁻¹ᵁ V) E hE
  · intro z hz
    change b.left (f.fromNormalization z.underlying) ∈ V
    change g.fromNormalization (w.left z.underlying) ∈ V at hz
    have heq := congrArg (fun m => m z.underlying) hwb'
    exact heq ▸ hz
  · change g.fromNormalization (w.left x.underlying) ∈ V
    change b.left (f.fromNormalization x.underlying) ∈ V at hx
    have heq := congrArg (fun m => m x.underlying) hwb'
    exact heq.symm ▸ hx

#print axioms normalization_transition_singleton_fibre
end HodgeLean.Foundations.QuotientDuality
