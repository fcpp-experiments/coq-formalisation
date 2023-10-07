Require Import PeanoNat.
From AC Require Import syntax.
Require Import List.
Require Import Maps.
Require Import Ascii.
Require Import BinPosDef.
Require Import String.
Require Import Pnat.

Local Definition bool_cons_pos (b : bool) (p : positive) : positive :=
  if b then p~1 else p~0.
Local Definition ascii_cons_pos (c : ascii) (p : positive) : positive :=
  match c with
  | Ascii b0 b1 b2 b3 b4 b5 b6 b7 =>
     bool_cons_pos b0 ( bool_cons_pos b1 ( bool_cons_pos b2 (
       bool_cons_pos b3 ( bool_cons_pos b4 ( bool_cons_pos b5 (
       bool_cons_pos b6 ( bool_cons_pos b7 p)))))))
  end.
Fixpoint string_to_pos (s : string) : positive :=
  match s with
  | EmptyString => 1
  | String c s => ascii_cons_pos c (string_to_pos s)
  end.

(*get single device value*)
Fixpoint get (pos:ident) (n:nvalue): literal :=
match n with
| nv m => PMap.get (Pos.of_nat (pos+1)) m
end.

Fixpoint getDefault (n:nvalue): literal :=
match n with
| nv (x, _) => x
end.


Fixpoint pointWise (op:literal -> literal -> literal) (w0:nvalue) {struct w0}: nvalue -> nvalue:=
  fix pointWise1 (w1:nvalue) {struct w1}: nvalue :=
    match w0,w1 with
    | nv (e1,t1), nv (e2,t2) => nv (op e1 e2, PTree.combine
                                                (fun x y => match x,y with
                                                            | None, None => None
                                                            | None, Some z => Some (op e1 z)
                                                            | Some z, None => Some (op z e2)
                                                            | Some zx, Some zy => Some (op zx zy)
                                                            end)
                                                t1 t2)
    end.

Fixpoint extend (w0:nvalue) {struct w0}: nvalue -> nvalue:=
  fix extend1 (w1:nvalue) {struct w1}: nvalue :=
    match w0,w1 with
    | nv (e1,t1), nv (e2,t2) => nv (e1 (*!*), PTree.combine
                                                (fun x y => match x,y with
                                                            | None, None => None
                                                            | None, Some z => Some z
                                                            | Some z, None => Some z
                                                            | Some zx, Some zy => Some zx
                                                            end)
                                                t1 t2)
    end.


Fixpoint folding (delta:ident) (devs:list nat) (w1:nvalue) (w2:nvalue) (w3:nvalue) : exp :=
match devs with 
| cons id l => if (delta =? id) then (folding id l w1 w2 w3) else exp_app (exp_app w1 (nvalues.get id w2)) (folding delta l w1 w2 w3)
| nil => (get delta w3)
end.

