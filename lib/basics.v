Require Import String.
Require Import Bool.
Require Import List.
Require Import Maps.
From AC Require Import syntax.
From AC Require Import nvalues.
Require Import Coq.Program.Basics.
Require Import Recdef.

(*Not recursive on nvalues*)
Reserved Notation "'/' x ':=' s '/' t" (in custom acnotation at level 20, x constr).
Fixpoint subst (x : string) (s : exp) (t : exp) : exp :=
  match t with
  | exp_var y =>
      if String.eqb x y then s else t
  | <{fun n [y:T] {t1}}> =>
      if ((String.eqb x y) || (String.eqb x n)) then t else <{fun n [y:T] {/x:=s/ t1}}>
  | <{t1 t2}> =>
      <{(/x:=s/ t1) (/x:=s/ t2)}>
  | <{val n = t1 ; t2}> =>
      if (String.eqb x n) then t else <{val n = (/x:=s/ t1) (*Dentro n non si può sostituire ?*) ; (/x:=s/ t2)}>
  | l_builtin b => l_builtin b
  | l_sensor s => l_sensor s
  | l_true => l_true
  | l_false => l_false
  | l_const n => l_const n
  | l_fail => l_fail
  | exp_nvalue w => <{w}>
end
where "'/' x ':=' s '/' t" := (subst x s t) (in custom acnotation).

Require Import Psatz.
Remark helper: forall t, 0 < exp_measure t.
Proof.
  induction t; compute; intuition.
  destruct n.  destruct m. lia.
Qed.

(*Recursive on nvalues*)
Fixpoint bounded (e:exp) (l_bounded:list string)  {struct e}: Prop :=
let fix l_b (l : literal) := 
        match l with
        | l_builtin b => True
        | l_sensor s => True
        | l_fail => True
        | l_true => True
        | l_false => True
        | l_const n => True
        end
in
match e with 
  | exp_var y =>
    In y l_bounded
  | <{t1 t2}> =>
    (bounded t1 l_bounded) /\ (bounded t2 l_bounded)
  | <{val n = t1 ; t2}> =>
    (bounded t1 l_bounded) /\ (bounded t2 (cons n l_bounded))
  | <{fun n [y:T] {t1}}> =>
    bounded t1 (cons y l_bounded)
  | exp_nvalue w =>
       match w with
         (* TODO: use ∘, requires scope? *)
       | nv (l, t) => let xs := (map snd (PTree.elements t)) in l_b l /\ forall x, In x xs -> l_b x
       end
  | exp_literal l => l_b l
end.

(*
Inductive w_values : nvalue -> Prop :=
| w_default : forall l, bounded (exp_literal l) nil-> w_values (default l)
| w_device : forall n l wl, bounded (exp_literal l) nil -> w_values wl -> w_values (device n l wl).
*)

Definition value (l:literal) : Prop := bounded (exp_literal l) nil.

Definition w_value (w:nvalue):= bounded (exp_nvalue w) nil.

Inductive is_fun: exp -> Prop :=
  | func : forall n x T2 t1, 
      is_fun <{fun n [x:T2] {t1}}>.





