/-
Copyright (c) 2022 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/

import tactic -- imports all the Lean tactics

/-!

# Logic in Lean, example sheet 2 : `true` and `false`

We learn about the `true` and `false` propositions.

## Tactics you will need

To solve the levels on this sheet you will need to know all previous
tactics, plus the following two new ones. Check out their explanations
in the course book. Or just try them out and hover over them to see
if you can understand what's going on.

* `triv`
* `exfalso`

-/

-- Throughout this sheet, `P`, `Q` and `R` will denote propositions.

variables (P Q R : Prop)

example : true :=
begin
  triv,
end

example : true → true :=
begin
  intro h,
  triv,
end

example : false → true :=
begin
  intro h,
  triv,
end

example : false → false :=
begin
  triv,
end

example : (true → false) → false :=
begin
  intro h,
  apply h,
  triv,
end

example : false → P :=
begin
  triv,
end

example : true → false → true → false → true → false :=
begin
  intros h_0 h_1,
  triv,
end

example : P → ((P → false) → false) :=
begin
  intro h,
  intro h_1,
  triv,
end

example : (P → false) → P → Q :=
begin
  intro h,
  intro h_1,
  triv,
end

example : (true → false) → P :=
begin
  intro h,
  exfalso,
  apply h,
  triv,
end