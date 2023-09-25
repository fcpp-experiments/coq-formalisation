Require Import PeanoNat.
From AC Require Import syntax.
From AC Require Import nvalues.
From AC Require Import value_tree.
Require Import String.
Require Import List.
Import ListNotations.

Definition x : string := "x".
Definition y : string := "y".
Definition fun0: string := "fun0". 
Definition fun1: string := "fun1".

Compute (nvalues.get 0 <{[0>>'6][>'5]}>).
Fact pos_works: (nvalues.get 1 <{[0>>'6][>'5]}> = 5).
Proof.
  compute; reflexivity.
Qed.
Compute (nvalues.get 2 <{[0>>'6][2>>'7][>'5]}>).
Compute (nvalues.getDefault <{[0>>'6][2>>'7][>'5]}>).

Definition l_sum (x:literal) (y:literal) : literal := match x,y with | l_const x, l_const y => l_const (x+y) | _ , _ => l_fail end.
Compute(pointWise l_sum <{[1>>'2][3>>'5][5>>'7][7>>'3][>'1]}> <{[2 >>'2][4>>'5][6>>'7][7>>'3][>'2]}>).
(*
Compute(pointWise l_sum (device  1 2(device  3 5(device  5 7(device  7 3(default  1))))) (device  2 2(device  4 5(device  6 7(device  7 3 (default  2)))))).
*)
Compute (extend <{[1>>'2][5>>'4][7>>'6][>'8]}>
           <{[0>>'1][1>>'3][3>>'5][4>>'7][5>>'9][6>>'11][8>>'13][>'6]}>).

(*
Compute (extend (device  1 2(device  3 5(device  5 7(device  7 3(default  1))))) (device  2 2 (device  4 5(device  6 7(device  7 3 (default  2)))))).

Compute (extend (device  2 2(device  4 5(device  6 7(device  7 3(default  2)))))  (device  1 2(device  3 5(device  5 7(device  7 3 (default  1)))))).

Compute (folding 4 (rev (devices (vt_el 4 (empty nil) (vt_el 5 (empty nil) vt_end)))) <{[ > fun fun0[x:Nat] {fun fun0[y:Nat] {mult x y} }]}>  <{[4 >> 2][5 >> 6][> 7]}> <{[>6]}> ).
*)
