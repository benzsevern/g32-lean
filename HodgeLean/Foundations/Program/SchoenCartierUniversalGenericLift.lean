import HodgeLean.Foundations.Program.SchoenDominantFieldFactor
import HodgeLean.Foundations.Program.SchoenGenericIdealPullback
import HodgeLean.Foundations.Program.SchoenBirationalFactor

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- The actual Cartier universal property supplies a dominant lift of the base function field and makes the integral base modification birational. -/
theorem s2_cartierUniversal_genericLift (B' B : Over (Spec ↧ℂ))
    [IsIntegral B'.left] [IsIntegral B.left]
    (b : B' ⟶ B) (I : B.left.IdealSheafData) (hI : I.support ≠ ⊤)
    (huniv : ∀ (T : Over (Spec ↧ℂ)) (f : T ⟶ B),
      (∀ x : T.left, ∃ U : T.left.affineOpens, x ∈ U.1 ∧
        Nonempty (((I.comap f.left).ideal U) ≃ₗ[Γ(T.left, U)] Γ(T.left, U))) →
      ∃! u : T ⟶ B', u ≫ b = f) :
    ∃ u : Spec B.left.functionField ⟶ B'.left,
      u ≫ b.left = B.left.fromSpecStalk (genericPoint B.left) ∧
      IsDominant u ∧ zmtiso_IsBirational b.left := by
  let g := B.left.fromSpecStalk (genericPoint B.left)
  haveI : IsDominant g := s2_genericPointMorphism_dominant B.left
  let T := Over.mk (g ≫ B.hom)
  haveI : IsIntegral T.left := by
    change IsIntegral (Spec B.left.functionField)
    infer_instance
  let f : T ⟶ B := Over.homMk g
  obtain ⟨u, hu, _⟩ := huniv T f (s2_dominant_fieldPoint_cartier g I hI)
  have hub : u.left ≫ b.left = g := congrArg Over.Hom.left hu
  haveI : IsDominant b.left := by
    haveI : IsDominant (u.left ≫ b.left) := by rw [hub]; infer_instance
    exact IsDominant.of_comp u.left b.left
  let g' := B'.left.fromSpecStalk (genericPoint B'.left)
  haveI : IsDominant g' := s2_genericPointMorphism_dominant B'.left
  let s := s2_dominantFieldFactor (g' ≫ b.left)
  have hs : s ≫ g = g' ≫ b.left := s2_dominantFieldFactor_comp (g' ≫ b.left)
  have hsu : (s ≫ u.left) ≫ b.left = g' ≫ b.left := by rw [Category.assoc, hub, hs]
  let T' := Over.mk (g' ≫ B'.hom)
  let f' : T' ⟶ B := Over.homMk (g' ≫ b.left)
  let v : T' ⟶ B' := Over.homMk (s ≫ u.left) (by
    calc
      (s ≫ u.left) ≫ B'.hom = ((s ≫ u.left) ≫ b.left) ≫ B.hom := by
        simp only [Category.assoc, Over.w b]
      _ = (g' ≫ b.left) ≫ B.hom := congrArg (fun k => k ≫ B.hom) hsu
      _ = g' ≫ B'.hom := by rw [Category.assoc, Over.w b])
  let v' : T' ⟶ B' := Over.homMk g'
  obtain ⟨_, _, huniq⟩ := huniv T' f' (s2_dominant_fieldPoint_cartier (g' ≫ b.left) I hI)
  have hv : v ≫ b = f' := Over.OverMorphism.ext hsu
  have hv' : v' ≫ b = f' := rfl
  have he : s ≫ u.left = g' :=
    congrArg Over.Hom.left ((huniq v hv).trans (huniq v' hv').symm)
  haveI : IsDominant u.left := by
    haveI : IsDominant (s ≫ u.left) := by rw [he]; infer_instance
    exact IsDominant.of_comp s u.left
  refine ⟨u.left, hub, inferInstance, ?_⟩
  apply s2_birational_of_dominant_factor u.left b.left
  rw [hub]
  exact s2_genericPointMorphism_birational B.left

end HodgeLean.Foundations.Program
