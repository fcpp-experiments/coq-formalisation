From AC Require Import syntax.
Require Import String.
Require Import Bool.
Require Import Coqlib.
Require Import Maps.
Require Import Coq.Strings.BinaryString.

Set Implicit Arguments.

(* Have: *)
Definition sensor_state := PMap.t nvalue.

Definition getSens (n:string) (s:sensor_state) : nvalue := PMap.get (to_pos n) s.

(* END *)
Definition base (s:string) := default l_fail.

Definition contains (s:string) (old:sensor_state): bool := 
match (PMap.get (to_pos s) old) with 
| default l_fail => false
| _ => true
end.

Definition add (s:string) (v:nvalue) (old:sensor_state): sensor_state := PMap.set (to_pos s) v old.
