import HodgeLean.Foundations.Program.G32SelectedRealizationProjector

noncomputable section
namespace HodgeLean.Foundations.Program

def g32y_stabilizer_coset_equiv {G X : Type*} [Group G] [MulAction G X]
    (H : Subgroup G) (x : X) (g : G)
    (hg : MulAction.stabilizer G x = Subgroup.zpowers g) (a : G) :
    MulAction.stabilizer H (a⁻¹ • x) ≃
      MulAction.stabilizer (Subgroup.zpowers g) (a : G ⧸ H) where
  toFun k := by
    let z : G := a * ((k : H) : G) * a⁻¹
    have hz : z ∈ Subgroup.zpowers g := by
      rw [← hg]
      change z • x = x
      have hk : ((k : H) : G) • (a⁻¹ • x) = a⁻¹ • x := k.property
      have hh := congrArg (fun v : X ↦ a • v) hk
      simpa only [z, mul_smul, smul_inv_smul] using hh
    refine ⟨⟨z, hz⟩, ?_⟩
    change ((z * a : G) : G ⧸ H) = (a : G ⧸ H)
    apply Eq.symm
    apply QuotientGroup.eq.mpr
    have he : a⁻¹ * (z * a) = ((k : H) : G) := by dsimp [z]; group
    rw [he]
    exact (k : H).property
  invFun q := by
    let z : G := (q : Subgroup.zpowers g)
    have hq : ((z * a : G) : G ⧸ H) = (a : G ⧸ H) := q.property
    have hzH : a⁻¹ * z * a ∈ H := by
      simpa only [mul_assoc] using QuotientGroup.eq.mp hq.symm
    have hz : z • x = x := by
      have hm : z ∈ Subgroup.zpowers g := (q : Subgroup.zpowers g).property
      rw [← hg] at hm
      exact hm
    refine ⟨⟨a⁻¹ * z * a, hzH⟩, ?_⟩
    change (a⁻¹ * z * a) • (a⁻¹ • x) = a⁻¹ • x
    simp only [mul_smul, smul_inv_smul, hz]
  left_inv k := by
    apply Subtype.ext
    apply Subtype.ext
    change a⁻¹ * (a * ((k : H) : G) * a⁻¹) * a = ((k : H) : G)
    group
  right_inv q := by
    apply Subtype.ext
    apply Subtype.ext
    change a * (a⁻¹ * ((q : Subgroup.zpowers g) : G) * a) * a⁻¹ =
      ((q : Subgroup.zpowers g) : G)
    group

end HodgeLean.Foundations.Program
