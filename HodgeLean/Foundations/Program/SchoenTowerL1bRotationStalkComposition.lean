import HodgeLean.Foundations.Program.SchoenCycleFixedStalkScalars

noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- Composition of fixed-point pullbacks agrees with composition of the
underlying scheme morphisms. -/
theorem s2v_l1b_rotation_stalk_comp
    (X : Scheme) (f g : X ⟶ X) (p : X)
    (hf : f p = p) (hg : g p = p) :
    s2e_fixed_point_stalkPullback X (f ≫ g) p (by change g (f p) = p; rw [hf, hg]) =
      (s2e_fixed_point_stalkPullback X f p hf).comp
        (s2e_fixed_point_stalkPullback X g p hg) := by
  exact (Scheme.FixedPointStalk.pullback_laws X p).2 f g hf hg

/-- A finite scheme iterate equal to the identity gives the same period on
the transported fixed-point stalk pullback. -/
theorem s2v_l1b_rotation_stalk_periodic
    (X : Scheme) (f : X ⟶ X) (p : X) (hf : f p = p)
    (F : ℕ → (X ⟶ X)) (hzero : F 0 = 𝟙 X)
    (hsucc : ∀ n, F (n + 1) = F n ≫ f)
    (N : ℕ) (hN : F N = 𝟙 X) :
    ∀ v, (s2e_fixed_point_stalkPullback X f p hf)^[N] v = v := by
  have hid (g : X ⟶ X) (hg : g p = p) (he : g = 𝟙 X) :
      s2e_fixed_point_stalkPullback X g p hg = RingHom.id _ := by
    subst g
    exact (Scheme.FixedPointStalk.pullback_laws X p).1
  have hcongr (g k : X ⟶ X) (hg : g p = p) (hk : k p = p) (he : g = k) :
      s2e_fixed_point_stalkPullback X g p hg = s2e_fixed_point_stalkPullback X k p hk := by
    subst k
    rfl
  have hfix (n : ℕ) : F n p = p := by
    induction n with
    | zero => rw [hzero]; rfl
    | succ n ih => rw [hsucc]; change f (F n p) = p; rw [ih, hf]
  have hi (n : ℕ) (v : X.presheaf.stalk p) :
      (s2e_fixed_point_stalkPullback X f p hf)^[n] v =
        s2e_fixed_point_stalkPullback X (F n) p (hfix n) v := by
    induction n generalizing v with
    | zero => rw [hid (F 0) (hfix 0) hzero]; rfl
    | succ n ih =>
      rw [Function.iterate_succ_apply, ih]
      have he := s2v_l1b_rotation_stalk_comp X (F n) f p (hfix n) hf
      rw [hcongr (F (n + 1)) (F n ≫ f) (hfix (n + 1))
        (by change f (F n p) = p; rw [hfix, hf]) (hsucc n), he]
      rfl
  intro v
  rw [hi]
  rw [hid (F N) (hfix N) hN]
  rfl

/-- A finite power relation in the retained scheme action gives periodicity
of its actual fixed-point stalk pullback. -/
theorem s2v_l1b_rotation_action_stalk_periodic
    {G : Type*} [Monoid G] (X : Over (Spec ↧ℂ))
    (a : G → (X ⟶ X)) (ha1 : a 1 = 𝟙 X)
    (hamul : ∀ u v, a (u * v) = a v ≫ a u)
    (u : G) (p : X.left) (hp : (a u).left p = p)
    (N : ℕ) (hN : u ^ N = 1) :
    ∀ v, (s2e_fixed_point_stalkPullback X.left (a u).left p hp)^[N] v = v := by
  apply s2v_l1b_rotation_stalk_periodic X.left (a u).left p hp
    (fun n => (a (u ^ n)).left)
  · rw [pow_zero, ha1]
    rfl
  · intro n
    rw [pow_succ', hamul]
    rfl
  · rw [hN, ha1]
    rfl

end HodgeLean.Foundations.Program
