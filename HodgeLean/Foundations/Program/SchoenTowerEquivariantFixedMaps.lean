import HodgeLean.Foundations.Program.SchoenTowerInvariantLifting

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace HodgeLean.Foundations.Program

/-- An equivariant coefficient-algebra map restricts to the actual fixed subalgebras. -/
def s2t_fixedSubalgebraMap {K A B G : Type*}
    [CommRing K] [CommRing A] [CommRing B] [Algebra K A] [Algebra K B]
    [Group G] [MulSemiringAction G A] [MulSemiringAction G B]
    [SMulCommClass G K A] [SMulCommClass G K B]
    (f : A →ₐ[K] B) (heq : ∀ (g : G) (a : A), f (g • a) = g • f a) :
    FixedPoints.subalgebra K A G →ₐ[K] FixedPoints.subalgebra K B G := by
  let φ := f.comp (FixedPoints.subalgebra K A G).val
  refine φ.codRestrict (FixedPoints.subalgebra K B G) ?_
  intro a g
  change g • f (a : A) = f (a : A)
  rw [← heq, (FixedPoints.mem_subalgebra (A := K)).mp a.property g]

/-- An equivariant bijection of coefficient algebras induces the actual fixed-ring
isomorphism, also when the acting group is relabeled. -/
def s2t_fixedSubalgebraEquivOfEquivariant {K A B G H : Type*}
    [CommRing K] [CommRing A] [CommRing B] [Algebra K A] [Algebra K B]
    [Group G] [Group H] [MulSemiringAction G A] [MulSemiringAction H B]
    [SMulCommClass G K A] [SMulCommClass H K B]
    (e : G ≃* H) (f : A →ₐ[K] B) (hbij : Function.Bijective f)
    (heq : ∀ (g : G) (a : A), f (g • a) = e g • f a) :
    FixedPoints.subalgebra K A G ≃+* FixedPoints.subalgebra K B H := by
  let F : FixedPoints.subalgebra K A G →+* FixedPoints.subalgebra K B H :=
    (f.toRingHom.comp (FixedPoints.subalgebra K A G).toSubring.subtype).codRestrict _ (by
      intro a h
      change h • f (a : A) = f (a : A)
      have hh := heq (e.symm h) (a : A)
      rw [e.apply_symm_apply, (FixedPoints.mem_subalgebra (A := K)).mp a.property (e.symm h)] at hh
      exact hh.symm)
  apply RingEquiv.ofBijective F
  constructor
  · intro a b h
    apply Subtype.ext
    apply hbij.injective
    exact congrArg Subtype.val h
  · intro b
    obtain ⟨a, ha⟩ := hbij.surjective (b : B)
    have hfix (g : G) : g • a = a := by
      apply hbij.injective
      calc
        f (g • a) = e g • f a := heq g a
        _ = (b : B) := by
          rw [ha]
          exact (FixedPoints.mem_subalgebra (A := K)).mp b.property (e g)
        _ = f a := ha.symm
    exact ⟨⟨a, hfix⟩, Subtype.ext ha⟩

end HodgeLean.Foundations.Program
