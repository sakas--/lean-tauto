/- TODO : Add comments and clean up the code.
-/

open expr tactic list nat


namespace tactic

/- transforms the current goal Γ ⊢ A to into two subgoals Γ ⊢ B → A and Γ ⊢ A. -/
-- I'm not sure if this is the right way to implement it
meta def cut (e: expr) : tactic unit :=
do {goal ← target,
    f ← mk_fresh_name,
    x ← mk_fresh_name,
    h ← mk_fresh_name,
    let fty := (pi h binder_info.default e goal) in
    apply (lam f binder_info.default  fty (lam x binder_info.default e (app (mk_var 1) (mk_var 0))))}
end tactic

open tactic

namespace tauto

/- utils -/
private meta def is_true (e : expr) : bool :=
is_constant_of e ``true

private meta def is_not' : expr → bool
| (app f a)     := if is_constant_of f ``not then tt else ff
| (pi n bi a b) := if is_false b then tt else ff
| e             := ff


private meta def is_genuine_not : expr → bool
| (app f a)  := if is_constant_of f ``not then tt else ff
| e          := ff

private meta def is_and (e : expr) : bool :=
is_app_of e ``and

private meta def is_or (e : expr) : bool :=
is_app_of e ``or

private meta def is_iff (e : expr) : bool :=
is_app_of e ``iff

private meta def option_arrow (e : expr) : option (expr × expr × expr) :=
match e with
| (pi n bi a b) := if bnot (has_var b) then some (e, a, b) else none
| e             := none
end

private meta def option_arrow_arrow (e : expr) : option (expr × expr × expr × expr × expr) :=
do
  (_, ab, c) ← option_arrow e,
  (_, a, b)  ← option_arrow ab,
  return (e, ab, a, b, c)

private meta def option_app : expr → option (expr × expr)
| (app a b) := some (a, b)
|  _        := none

private meta def option_binary_connective_of (n : name) (e : expr) : option (expr × expr) :=
do
  (e₁, b) ← option_app e,
  (e₂, a) ← option_app e₁,
  match e₂ with
  | (const n₁ _) := if n = n₁ then some (a, b) else none
  | _            := none
  end

private meta def option_and : expr → option (expr × expr) :=
option_binary_connective_of `and

private meta def option_or : expr → option (expr × expr) :=
option_binary_connective_of `or

private meta def option_iff : expr → option (expr × expr) :=
option_binary_connective_of `iff

/- utility tactics -/

/- uses LCF-style AND_THEN tactic during repeat  -/
private meta def repeat_seq_at_most : nat → tactic unit → tactic unit
| 0        t := skip
| (succ n) t := (seq t (repeat_seq_at_most n t)) <|> skip

private meta def repeat_seq : tactic unit → tactic unit :=
repeat_seq_at_most 100000


/- converts f : A -> B , e : A,  Γ |- P to f : A → B, f e : B, Γ |- P -/
private meta def apply_to (f : expr) (e : expr) : tactic unit :=
do
  fty ← infer_type f,
  ety ← infer_type e,
   match option_arrow fty with
   | none              := failed
   | (some (_, a , b)) :=
     do
       unify a ety,
       fe ← mk_fresh_name,
       assert fe b,
       exact (app f e)
   end

private meta def not_dep_intros_core : unit → tactic (list expr)
| u :=
   do goal ← target,
      if is_arrow goal
      then do  H ← intro1, Hs ← not_dep_intros_core u, return (H :: Hs)
      else match is_not goal with
           | none := return []
           | some a := do H ← intro1, Hs ← not_dep_intros_core u, return (H :: Hs)
           end

private meta def not_dep_intros : tactic (list expr) :=
not_dep_intros_core ()

private meta def not_dep_intros' : tactic unit :=
do
  es ← not_dep_intros,
  match es with
  | [] := failed
  | _  := skip
  end

private meta def find_imp_imp : list expr  → tactic (expr × expr × expr × expr × expr)
| []        := failed
| (e :: es) :=
  do
    ty ← infer_type e,
    match option_arrow_arrow ty with
    | none                    := find_imp_imp es
    | (some (_, ab, a, b, c)) := return (e, ab, a, b, c)
    end

namespace tauto
namespace tauto_rules

/- some logically equivalent rules that are used by the simplifier -/

variables {A B C : Prop}

protected lemma true_imp_iff : (true → A) ↔ A :=
begin
apply iff.intro,
  {intro h, apply h, trivial},
  {intros h₁ h₂, apply h₁}
end

protected lemma and_imp_iff : A ∧ B → C ↔ A → B → C :=
begin
apply iff.intro,
  {intros h ha hb, apply h, split, exact ha, exact hb},
  {intros h₁ h₂, cases h₂ with ha hb, exact (h₁ ha hb)}
end

protected lemma or_imp_iff : A ∨ B → C ↔ (A → C) ∧ (B → C) :=
begin
apply iff.intro,
  {intro h, split,
    {intro ha, apply h, left, exact ha},
    {intro hb, apply h, right, exact hb}},
  {intro h, cases h with hac hbc,
   intro h₁, cases h₁ with ha hb,
    {apply hac, exact ha},
    {apply hbc, exact hb}}
end

protected lemma iff_imp_iff : (A ↔ B) → C ↔ (A → B) ∧ (B → A) →  C :=
begin
apply iff.intro,
  {intros h h₁, apply h, apply iff.intro, exact (and.left h₁), exact (and.right h₁)},
  {intros h h₁, apply h, cases h₁ with h₂ h₃, exact (and.intro h₂ h₃)}
end

end tauto_rules
end tauto

/- simplifier -/

/- TODO: Currently type parameters are explicitly passed when to_expr is used.
         This is to ensure that no metavariables are introduced.
         I think there is a better work around (e.g. using the elaborator).
-/

/- converts A ∧ B → C, Γ ⊢ P to A → B → C, Γ ⊢ P -/
private meta def flatten_and_imp (e : expr) : tactic unit :=
do
  ty ← infer_type e,
  match option_arrow ty with
  | none              := failed
  | (some (_, ab, c)) :=
    match option_and ab with
    | none        := failed
    | some (a, b) :=
      do
        f ← to_expr `(iff.mp (@tauto.tauto_rules.and_imp_iff %%a %%b %%c)),
        apply_to f e,
        clear e
    end
  end

/- converts A ∨ B → C, Γ ⊢ P to (A → C) ∧ (B → C), Γ ⊢ P -/
private meta def flatten_or_imp (e : expr) : tactic unit :=
do
  ty ← infer_type e,
  match option_arrow ty with
  | none             := failed
  | (some (_, ab, c)) :=
    match option_or ab with
    | none          := failed
    | (some (a, b)) :=
      do
        f ← to_expr `(iff.mp (@tauto.tauto_rules.or_imp_iff %%a %%b %%c)),
        apply_to f e,
        clear e
    end
  end

private meta def flatten_not_imp (e : expr) : tactic unit :=
do
  ty ← infer_type e,
  match option_arrow ty with
  | none             := failed
  | (some (_, a, _)) :=
    if is_genuine_not a
    then
      dunfold_at [``not] e
    else
    failed
end

private meta def flatten_iff_imp (e : expr) : tactic unit :=
do
  ty ← infer_type e,
  match option_arrow ty with
  | none              := failed
  | (some (_, ab, c)) :=
    match option_iff ab with
    | none          := failed
    | (some (a, b)) :=
      do
        f ← to_expr `(iff.mp (@tauto.tauto_rules.iff_imp_iff %%a %%b %%c)),
        apply_to f e,
        clear e
    end
  end

/- converts ¬ A to A → false -/
private meta def reduce_not (e : expr) : tactic unit :=
do
  ty ← infer_type e,
  if is_genuine_not ty
  then
    dunfold_at [``not] e
  else
    failed

/- converts  A -> B , A,  Γ |- P to B, Γ |- P -/
private meta def apply_at_hyp (e : expr) (l : list expr) : tactic unit :=
do ty ← infer_type e,
   match option_arrow ty with
   | none             := failed
   | (some (_, a, _)) :=
     do
       ea ← find_same_type a l,
       apply_to e ea,
       clear e
   end

/- converts true → A, Γ ⊢ P to A, Γ ⊢ P -/
private meta def flatten_true_imp (e : expr) : tactic unit :=
do ty ← infer_type e,
   match option_arrow ty with
   | none             := failed
   | (some (_, a, b)) :=
     if is_true a
     then
     do
       f ← to_expr `(iff.mp (@tauto.tauto_rules.true_imp_iff %%b)),
       apply_to f e,
       clear e
     else failed
   end

private meta def simplify_hyp : list expr →  tactic unit
| []      := failed
| (e::es) :=
  do
    cases e
    <|> reduce_not e
    <|> local_context >>= apply_at_hyp e
    <|> flatten_true_imp e
    <|> flatten_not_imp e
    <|> flatten_and_imp e
    <|> flatten_or_imp e
    <|> flatten_iff_imp e
    <|> simplify_hyp es


private meta def simplify_goal : tactic unit :=
split <|> interactive.apply `(iff.intro) <|> failed

meta def simplify : tactic unit :=
do
  not_dep_intros >> skip,
  repeat_seq(
      (do
         ctx ← local_context,
         simplify_hyp ctx
         <|>  simplify_goal
         <|>  not_dep_intros'))


/- main procedures -/

private meta def apply_axiom : tactic unit :=
triv <|> contradiction <|> assumption

private meta def tauto_core : unit → tactic unit
| u :=
  do
    seq simplify
      (apply_axiom
      <|>
      do
        {ctx ← local_context,
        (e, ab, a, b, c) ← find_imp_imp ctx,
        cut c,
        focus [
              do {h ← intro1, clear e, tauto_core ()},
              do {cut ab, exact e, 
                  x ← mk_fresh_name, y ← mk_fresh_name, z ← mk_fresh_name,
                  h ← mk_fresh_name,
                  -- assert : b -> c
                  assert h (pi z binder_info.default b c),
                  -- exact (λ y : b, e (λ x : a, y)) : b -> c
                  exact (lam y binder_info.default b (app e (lam x binder_info.default a (mk_var 1)))), 
                  h1 ← intro1, clear e, tauto_core ()}]}
      <|>
      do
        {goal ← target,
         if is_arrow goal
         then
           do h ← intro1, tauto_core ()
         else if is_or goal then
           (left  >> tauto_core ()) <|>  (right >> tauto_core ())
         else fail "tauto failed"})

meta def tauto : tactic unit :=
tauto_core ()

end tauto

