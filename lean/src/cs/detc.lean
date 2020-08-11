import tactic.finish
import tactic.basic
import data.list.basic
import .lang

namespace lang

-- Concrete semantics is determinstic. 
lemma evalC_det 
{D O : Type} 
{op : O → list (val D O) → result D O}
{x : exp D O} 
{e : env D O} 
{r1 r2 : result D O} 
(h1 : evalC op x e r1) 
(h2 : evalC op x e r2) : 
r1 = r2 := 
begin
  induction h1 generalizing r2,
  any_goals { -- bool, datum, lam, var, error, abort
    cases h2, solve1 { simp only [eq_self_iff_true, and_self, err, abt], } }, 
  case lang.evalC.app {
    cases h2,
    congr,
    apply list.ext_le, 
    { cc, },
    { intros i hi1 hi2, 
      specialize h1_h2 i (by {cc}) hi1,
      specialize h2_h2 i (by {cc}) hi2,
      specialize h1_ih i (by {cc,}) hi1 h2_h2,
      simp only at h1_ih, 
      exact h1_ih,}},
  case lang.evalC.call {
    cases h2,
    { specialize h1_ih_h1 h2_h1,
      simp only at h1_ih_h1,
      specialize h1_ih_h2 h2_h2,
      simp only at h1_ih_h2,
      apply h1_ih_h3,
      simp [h1_ih_h1, h1_ih_h2, h2_h3],},
    { specialize h1_ih_h1 h2_h1,
      simp only at h1_ih_h1,
      rewrite ←h1_ih_h1 at h2_h3,
      simp [val.is_clos] at h2_h3,
      contradiction, }},
  case lang.evalC.call_halt {
    cases h2,
    { specialize h1_ih_h1 h2_h1,
      simp only at h1_ih_h1, 
      simp [h1_ih_h1] at h1_h3,
      contradiction, }, 
    { simp, }},
  case lang.evalC.let0 {
    cases h2,
    { specialize h1_ih_h1 h2_h1,
      simp only at h1_ih_h1, 
      rewrite ←h1_ih_h1 at h2_h2,
      apply h1_ih_h2 h2_h2, }, 
    { specialize h1_ih_h1 h2_h1,
      simp only at h1_ih_h1,
      contradiction, }},
  case lang.evalC.let0_halt {
    cases h2,
    { specialize h1_ih h2_h1, 
      simp only at h1_ih, 
      contradiction,}, 
    { apply h1_ih h2_h1,}},
  all_goals { -- if0_true, if0_false
    cases h2,
    any_goals { apply h1_ih_hr h2_hr, }, 
    { specialize h1_ih_hc h2_hc, 
      simp only at h1_ih_hc,
      rewrite [h1_ih_hc] at h1_hv,
      finish,} }, 
end 

end lang 