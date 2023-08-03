import Mathlib.Tactic
import Mathlib.Data.Real.Basic
import Mathlib.GroupTheory.PGroup


#check IsCyclic.exists_generator
#check Subgroup.card_subgroup_dvd_card
#check IsCyclic.commGroup



/-- group structure -/
class Group4Ele (G : Type _) extends Group G, Fintype G where
  card_eq4 : Fintype.card G = 4


/-- |G| = 4, G : noncyclic, ∀ g ∈ G, g ≠ 1 → |g| = 2 -/
lemma order_of_ntriv_of_4EleNoncycG_eq2 {G : Type _} [g4ele : Group4Ele G] -- [IsCyclic G]
    (noncyc : ∀ (g : G), ∃ (x : G), x ∉ Subgroup.zpowers g) : ∀ g : G, g ≠ 1 → orderOf g = 2 := by
  intro g gntriv
  have : orderOf g < 5 ∧ orderOf g ≥ 1:= by
    constructor
    · rw [Nat.lt_succ, ← g4ele.card_eq4]
      apply orderOf_le_card_univ
    · linarith [orderOf_pos g]
  rcases this with ⟨ub, lb⟩
  interval_cases og : orderOf g using lb, ub
  · rw [orderOf_eq_one_iff] at og
    simp; contradiction
  · rfl
  · have : orderOf g ∣ g4ele.card := by apply orderOf_dvd_card_univ
    rw [og, g4ele.card_eq4] at this
    simp at *
  · rw [← g4ele.card_eq4] at og
    have : IsCyclic G := isCyclic_of_orderOf_eq_card g og
    contrapose! noncyc
    apply this.exists_generator


/-- G : group, ∀ g ∈ G, |g| = 2 → g = g⁻¹ -/
lemma inv_eq_self_if_order_eq2 {G : Type _} (g : G) [Group4Ele G] (h : orderOf g = 2) : g = g⁻¹ := by
  have : g ^ 2 = 1 := orderOf_dvd_iff_pow_eq_one.1 (dvd_of_eq h)
  rw [sq, mul_eq_one_iff_eq_inv] at this
  exact this


/-- |G| = 4 → G : Abelian -/
theorem comm_of_4EleG {G : Type _} [g4ele : Group4Ele G] : ∀ a b : G, a * b = b * a := by
  intro a b
  let IsCyc := ∃ g, ∀ (x : G), x ∈ Subgroup.zpowers g
  cases em IsCyc
  · case inl h =>
    rcases h with ⟨g, hg⟩
    obtain ⟨ka, ha⟩ : ∃ k, g ^ k = a := Subgroup.mem_zpowers_iff.1 (hg a)
    obtain ⟨kb, hb⟩ : ∃ k, g ^ k = b := Subgroup.mem_zpowers_iff.1 (hg b)
    rw [← ha, ← hb]
    rw [← zpow_add g ka kb, ← zpow_add g kb, add_comm]
  · case inr h =>
    cases em (a = 1 ∨ b = 1 ∨ a * b = 1)
    · case inl h' =>
      rcases h' with eq1 | eq1 | eq1 <;>
      simp [eq1]
      rw [mul_eq_one_iff_eq_inv] at eq1
      rw [eq1, mul_right_inv]
    · case inr h' =>
      push_neg at h' h h
      rcases h' with ⟨ane1, bne1, abne1⟩
      let c := a * b
      have ceqab : c = a * b := rfl
      have oc2 : orderOf c = 2 := order_of_ntriv_of_4EleNoncycG_eq2 h c abne1
      have oa2 : orderOf a = 2 := order_of_ntriv_of_4EleNoncycG_eq2 h a ane1
      have ob2 : orderOf b = 2 := order_of_ntriv_of_4EleNoncycG_eq2 h b bne1
      have hc : c = c⁻¹ := inv_eq_self_if_order_eq2 c oc2
      have ha : a = a⁻¹ := inv_eq_self_if_order_eq2 a oa2
      have hb : b = b⁻¹ := inv_eq_self_if_order_eq2 b ob2
      rw [ceqab] at hc
      rw [hc]
      symm
      apply mul_eq_one_iff_eq_inv.1
      nth_rw 1 [ha, hb]
      rw [← mul_assoc, mul_assoc _ a⁻¹, mul_left_inv, mul_one, mul_left_inv]



theorem comm_of_4EleG' {G : Type _} [g4ele : Group4Ele G] : ∀ a b : G, a * b = b * a := by
  intro a b
  cases em (IsCyclic G)
  · case inl h =>
    have : CommGroup G := IsCyclic.commGroup
    convert this.mul_comm a b <;>
    sorry -- !!!!!!!!!!!!!
  case inr h =>
  cases em (a = 1 ∨ b = 1 ∨ a * b = 1)
  · case inl h' =>
    rcases h' with eq1 | eq1 | eq1 <;>
    simp [eq1]
    rw [mul_eq_one_iff_eq_inv] at eq1
    rw [eq1, mul_right_inv]
  case inr h' =>
  push_neg at h'
  rcases h' with ⟨ane1, bne1, abne1⟩
  let c := a * b
  have ceqab : c = a * b := rfl
  have oc2 : orderOf c = 2 := by
    convert order_of_ntriv_of_4EleNoncycG_eq2 _ c abne1
    contrapose! h
    rcases h with ⟨g, hg⟩
    use g
  have oa2 : orderOf a = 2 := by
    convert order_of_ntriv_of_4EleNoncycG_eq2 _ a ane1
    contrapose! h
    rcases h with ⟨g, hg⟩
    use g
  have ob2 : orderOf b = 2 := by
    convert order_of_ntriv_of_4EleNoncycG_eq2 _ b bne1
    contrapose! h
    rcases h with ⟨g, hg⟩
    use g
  have : c = c⁻¹ := inv_eq_self_if_order_eq2 c oc2
  rw [ceqab] at this
  nth_rw 2 [inv_eq_self_if_order_eq2 a oa2, inv_eq_self_if_order_eq2 b ob2]
  rw [this]
  -- rw [mul_inv]
  sorry


/-- the ready-made version -/
theorem comm_of_4EleG₂ {G : Type _} [Group G] [Fintype G] (h : Fintype.card G = 4) :
    ∀ a b : G, a * b = b * a := by
  have : 4 = 2 ^ 2 := by simp
  rw [this] at h
  apply IsPGroup.commutative_of_card_eq_prime_sq h
