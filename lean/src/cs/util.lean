import tactic.basic
import tactic.omega
import tactic.linarith
import tactic.apply_fun
import data.option.basic


namespace sym 

lemma bool.tt_eq_true {b : bool} : 
(b = tt) ↔ b := by { simp only [iff_self], }

lemma nat.lt2_implies_01 {j : ℕ} : j < 2 → (j = 0 ∨ j = 1) := by omega 
lemma nat.le_and_ne_is_lt {i j : ℕ} : i ≠ j → i ≤ j → i < j := by { intros h1 hs, omega,  }
lemma nat.lt_sub_pos {j n : ℕ} : j < n → 0 < n - j := by { omega, }

lemma nat.min_of_lt {k n : ℕ} : k < n → min k n = k := 
begin 
  intro h, 
  simp only [min, not_le, ite_eq_left_iff], 
  intro h', 
  linarith,
end 

lemma list.map_bound {α1 α2 β} 
{l1 : list α1} {l2 : list α2} {f1 : α1 → β} {f2 : α2 → β} {i : ℕ} : 
l1.map f1 = l2.map f2 → i < l1.length → i < l2.length := 
begin 
    intro h,
    apply_fun list.length at h,
    simp only [list.length_map] at h, 
    cc,
end 

lemma list.forall_mem_iff_forall_nth_le {α} {xs : list α} {p : α → Prop} :
(∀ (x : α), x ∈ xs → p x) ↔ 
(∀ (i : ℕ) (hi : i < xs.length), p (xs.nth_le i hi)) := 
begin
  constructor; intro h,
  { intros i hi,
    specialize h (xs.nth_le i hi) (list.nth_le_mem xs i hi),
    exact h, },
  { intros x hx,
    simp only [list.mem_iff_nth_le] at hx,
    cases hx with n hn, cases hn with hn hmem, 
    specialize h n hn,
    rewrite ←hmem,
    exact h, } 
end

lemma list.filter_length_ge_one {α} {xs : list α} {x : α} {p : α → Prop} [decidable_pred p] : 
x ∈ xs → p x → 1 ≤ (xs.filter p).length  := 
begin
  intros h1 h2,
  have h3 : x ∈ (xs.filter p) := by { simp only [h1, h2, list.mem_filter, and_self], },
  have h4 : 0 < (xs.filter p).length := (list.length_pos_of_mem h3),
  linarith, 
end
 

lemma list.filter_length_gt_one_aux {α} {xs : list α} {i j : ℕ} {p : α → Prop} [decidable_pred p] 
(hi : i < xs.length) (hj : j < xs.length) : 
i < j → p (xs.nth_le i hi) → p (xs.nth_le j hj) → 
(xs.filter p).length > 1 := 
begin
  intros hn hpi hpj,
  rcases (list.nth_le_mem xs i hi) with hi_mem,
  rcases (list.nth_le_mem xs j hj) with hj_mem,
  rcases (list.take_append_drop j xs) with hxs',
  rewrite [←hxs', list.filter_append],
  simp only [list.length_append, gt_iff_lt],

  have hi' : i < (list.take j xs ++ list.drop j xs).length := by { simp only [list.take_append_drop], exact hi, },
  have hti : i < (list.take j xs).length := by { simp only [hn, hi, lt_min_iff, list.length_take, and_self], },
  rcases (list.nth_le_append hi' hti) with hl,
  simp only [list.take_append_drop] at hl,
  rcases (list.nth_le_mem (list.take j xs) i hti) with hlm,
  rewrite ←hl at hlm,

  have hj' : j < (list.take j xs ++ list.drop j xs).length := by { simp only [list.take_append_drop], exact hj, },
  have htj : (list.take j xs).length ≤ j := by { simp only [list.length_take, min_le_iff], apply or.inl, refl, },
  rcases (list.nth_le_append_right htj hj') with hr,
  simp only [list.length_take, list.take_append_drop] at hr,
  have hd : j - min j xs.length < (list.drop j xs).length := by {
    rewrite nat.min_of_lt hj, 
    simp only [list.length_drop, nat.sub_self],
    apply nat.lt_sub_pos hj, },
  rcases (list.nth_le_mem (list.drop j xs) (j - min j xs.length) hd) with hrm,
  rewrite ←hr at hrm,

  rcases (list.filter_length_ge_one hlm hpi) with ht, 
  rcases (list.filter_length_ge_one hrm hpj) with hd, 

  linarith, 
end 

lemma list.filter_length_gt_one {α} {xs : list α} {i j : ℕ} {p : α → Prop} [decidable_pred p] 
(hi : i < xs.length) (hj : j < xs.length) : 
i ≠ j → p (xs.nth_le i hi) → p (xs.nth_le j hj) → 
(xs.filter p).length > 1 := 
begin
  intros hn hpi hpj,
  cases classical.em (i < j),
  { apply list.filter_length_gt_one_aux hi hj h hpi hpj, }, 
  { simp only [not_lt] at h,
    replace h : j < i := nat.le_and_ne_is_lt (by {cc}) h,
    apply list.filter_length_gt_one_aux hj hi h hpj hpi, } 
end 

lemma list.filter_map_length_eq {α β} {xs : list α} {f : α → β} {p : β → Prop} [decidable_pred p] :
(list.filter p (list.map f xs)).length = (list.filter (λ x, p (f x)) xs).length   := 
by { simp only [list.map_filter, list.length_map], }

lemma list.nth_le_eq_idx {α} (xs : list α) {i j : ℕ} : 
(i = j) → ∀ (hi : i < xs.length) (hj : j < xs.length), xs.nth_le i hi = xs.nth_le j hj := 
begin
  intros h hi hm,
  congr,
  exact h, 
end 

end sym
