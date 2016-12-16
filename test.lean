/- TODO : add some test from ILTP library
-/

import .tauto

open tauto

section test
variables {A B C D E : Prop}

example : true :=
by tauto >> tactic.trace "test1 succeeded"

example : A → A :=
by tauto >> tactic.trace "test2 succeeded"

example : A ∧ B → B ∧ A :=
by tauto >> tactic.trace "test3 succeeded"

example : A ∧ B ↔ B ∧ A :=
by tauto >> tactic.trace "test4 succeeded"

example : A ∨ B → B ∨ A :=
by tauto >> tactic.trace "test5 succeeded"

example : A ∨ B ↔ B ∨ A :=
by tauto >> tactic.trace "test6 succeeded"

example : (A → B) → A → B :=
by tauto >> tactic.trace "test7 succeeded"

example : (A ↔ B) → A → B :=
by tauto >> tactic.trace "test8 succeeded"

example : (true → A) ↔ A :=
by tauto >> tactic.trace "test9 succeeded"

example : (((A →  B) →  A) → A) → (B → A) → (((A → B) → B) → A) :=
by tauto >> tactic.trace "test10 succeeded"

example : (A → B) ∨ (A → C) →  A → B ∨ C :=
by tauto >> tactic.trace "test11 succeeded"

example : A ∧ B ∨ C ∧ D → (A ∨ C) ∧ (B ∨ C) :=
by tauto >> tactic.trace "test12 succeeded"

example : A → A → A → A → A → A → A → A → A → A :=
by tauto >> tactic.trace "test13 succeeded"

example : ¬ A → ¬ A :=
by tauto >> tactic.trace "test14 succeeded"

example : (¬ A ∧ ¬ B) ↔ ¬ (A ∨ B) :=
by tauto >> tactic.trace "test15 succeeded"

example : ¬ A ∨ ¬ B → ¬ (A ∧ B) :=
by tauto >> tactic.trace "test16 succeeded"

example : ¬ ¬ (¬ (A ∧ B) → ¬ A ∨ ¬ B)  :=
by tauto  >> tactic.trace "test17 succeeded"

example : ¬ ¬ (A ∨ ¬ A) :=
by tauto >> tactic.trace "test18 succeeded"

example : (A → ¬ ¬ B) → ¬ ¬ (A → B) :=
by tauto >> tactic.trace "test19 succeeded"

example : ¬ ¬ A ↔ ¬ ¬ ¬ ¬ A :=
by tauto >> tactic.trace "test20 succeeded"

example : (¬ ¬  A →  A) → (¬ B → A) → (B → A) → A :=
by tauto >> tactic.trace "test21 succeeded"

example : ¬ ¬ ((A ∧ B → C) ↔ ((A → C) ∨ (B → C))) :=
by tauto >> tactic.trace "test22 succeeded"

example : (A ↔ B) ∧ (B ↔ C) ∧ (C ↔ D) ∧ (D ↔ E) → (E ↔ A) :=
by tauto >> tactic.trace "test23 succeeded"

example : A → ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ A :=
by tauto >> tactic.trace "test24 succeeded"

example : (A → ¬ ¬ B) ∧ ¬ (A → B) ∧ (B → ¬ ¬ C) ∧ ¬ (B → C) → A :=
by tauto >> tactic.trace "test25 succeeded"

example : A ∨ B ∨ C → (A ∨ B ∨ C → D) → D :=
by tauto >> tactic.trace "test26 succeeded"

example : ¬ ¬ (((A → B) → A) → A) :=
by tauto >> tactic.trace "test27 succeeded"

end test
