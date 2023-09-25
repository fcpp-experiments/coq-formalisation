From AC Require Import syntax.
From AC Require Import nvalues.
Require Import String.
Require Import Bool.
Require Import Coqlib.
Require Import Maps.

Set Implicit Arguments.

(* Have: *)
Definition sensor_state := PMap.t nvalue.

Definition getSens (n:string) (s:sensor_state) := PMap.get (string_to_pos n) s.


(* END *)
Definition base: sensor_state := PMap.init (nv (PMap.init l_fail)).

(*Definition contains (s:string) (old:sensor_state): bool := 
match (PMap.get (string_to_pos s) old) with 
| nv (_,t) => PTree.empty t
end.
 *)

Definition add (s:string) (v:nvalue) (old:sensor_state): sensor_state := PMap.set (string_to_pos s) v old.
