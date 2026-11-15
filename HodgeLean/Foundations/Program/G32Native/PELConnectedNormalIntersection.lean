import HodgeLean.Foundations.Program.G32Native.PELFiniteNormalizedSubgroup

noncomputable section
namespace HodgeLean.Foundations.Program.GeneralTypeIII
variable {k : Type*} [Field k] {n : ℕ}

/-- The normalized intersection in the identity-component argument is
infinite whenever the supplied witness is noncentral. -/
theorem pel_identityComponent_normal_intersection_infinite
    (G : MatrixAlgGroup k n)
    (H : Subgroup (Matrix.GeneralLinearGroup (Fin n) k))
    (hn : ∀ g ∈ g1_identityComponent G, ∀ x ∈ H, g⁻¹ * x * g ∈ H)
    (x : Matrix.GeneralLinearGroup (Fin n) k) (hx : x ∈ H)
    (hxG : x ∈ g1_identityComponent G)
    (hnoncentral : ∃ g ∈ g1_identityComponent G, ¬ Commute x g) :
    ((H ⊓ g1_identityComponentSubgroup G : Subgroup _) :
      Set (Matrix.GeneralLinearGroup (Fin n) k)).Infinite := by
  exact pel_zariski_normal_intersection_infinite H (g1_identityComponentSubgroup G)
    (@isPreconnected_connectedComponentIn _ (g1_zariski k n) _ _) hn x hx hxG hnoncentral

/-- The noncentrality requirement excludes the central scalar of order two;
mere nonidentity would not exclude it. -/
theorem pel_negative_identity_commutes (g : Matrix.GeneralLinearGroup (Fin n) k) :
    Commute (-1 : Matrix.GeneralLinearGroup (Fin n) k) g := by
  change (-1 : Matrix.GeneralLinearGroup (Fin n) k) * g = g * (-1)
  apply Units.ext
  simp only [Units.val_mul, Units.val_neg, Units.val_one, Matrix.neg_mul,
    Matrix.mul_neg, Matrix.one_mul, Matrix.mul_one]

#print axioms pel_identityComponent_normal_intersection_infinite
#print axioms pel_negative_identity_commutes
end HodgeLean.Foundations.Program.GeneralTypeIII
