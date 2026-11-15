import HodgeLean.Foundations.Program.SchoenTowerI2bSpecInertia
import HodgeLean.Foundations.Program.SchoenTowerI2bGenericSuppliers

/-! Detecting a retained deck period on a dominant field source.
HC no distance; AV milestone no distance. -/
noncomputable section
set_option maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- Iterated postcomposition is postcomposition by the categorical endomorphism power.
Source: the endomorphism monoid convention and induction on the iterate. -/
theorem s2v_i2b_postcomp_iterate
    {C : Type*} [Category C] {T X : C} (d : X ⟶ X) (p : T ⟶ X) (n : ℕ) :
    (fun q : T ⟶ X => q ≫ d)^[n] p = p ≫ ((End.of d) ^ n).asHom := by
  induction n with
  | zero => simp only [Function.iterate_zero, id_eq, pow_zero, End.one_asHom, Category.comp_id]
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih, pow_succ', End.mul_asHom, Category.assoc]

/-- A period of the field action is a period on every point of the retained reduced cover.
Source: the dominant generic-source square and separatedness over the complex base. -/
theorem s2v_i2b_field_period_on_cover
    {R K : Type} [CommRing R] [Field K] [Algebra R K]
    (X : Over (Spec ↧ℂ)) [IsReduced X.left] [IsSeparated X.hom]
    (f : Spec ↧K ⟶ X.left) [IsDominant f] (d : X ⟶ X)
    (δ : K ≃ₐ[R] K)
    (hδ : Spec.map (CommRingCat.ofHom δ.toRingHom) ≫ f = f ≫ d.left)
    (n : ℕ) (hn : δ ^ n = 1) :
    ∀ w : ComplexPoint X, (Point.map d)^[n] w = w := by
  have hs : Function.Semiconj (fun q : Spec ↧K ⟶ Spec ↧K => q ≫ f)
      (fun q => q ≫ Spec.map (CommRingCat.ofHom δ.toRingHom))
      (fun q => q ≫ d.left) := by
    intro q
    change (q ≫ Spec.map (CommRingCat.ofHom δ.toRingHom)) ≫ f = (q ≫ f) ≫ d.left
    rw [Category.assoc, hδ, Category.assoc]
  have hiter := hs.iterate_right n (𝟙 (Spec ↧K))
  have hspec := s2v_i2b_spec_point_iterate (𝟙 (Spec ↧K)) δ n
  have hidmap : Spec.map (CommRingCat.ofHom (δ ^ n).toRingHom) = 𝟙 (Spec ↧K) := by
    rw [hn]
    change Spec.map (𝟙 (CommRingCat.of K)) = 𝟙 (Spec ↧K)
    exact Spec.map_id _
  rw [hidmap, Category.comp_id] at hspec
  rw [hspec] at hiter
  simp only [Category.id_comp] at hiter
  rw [s2v_i2b_postcomp_iterate] at hiter
  have hbase : ∀ j : ℕ, ((End.of d.left) ^ j).asHom ≫ X.hom = X.hom := by
    intro j
    induction j with
    | zero => simp only [pow_zero, End.one_asHom, Category.id_comp]
    | succ j ih => rw [pow_succ', End.mul_asHom, Category.assoc, d.w, ih]
  have hdense : ((End.of d.left) ^ n).asHom = 𝟙 X.left := by
    apply ext_of_isDominant_of_isSeparated X.hom (by rw [hbase, Category.id_comp]) f
    simpa only [Category.comp_id] using hiter.symm
  have hpoint : Function.Semiconj (fun w : ComplexPoint X => w.left)
      (Point.map d) (fun q => q ≫ d.left) := fun _ => rfl
  intro w
  apply Over.OverMorphism.ext
  have hleft := hpoint.iterate_right n w
  rw [s2v_i2b_postcomp_iterate, hdense, Category.comp_id] at hleft
  exact hleft

end HodgeLean.Foundations.Program
