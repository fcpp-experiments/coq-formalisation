From AC Require Import syntax.
From AC Require Import basics.
From AC Require Import sensor_state.
From AC Require Import value_tree.
From AC Require Import nvalues.
From AC Require Import big_step_semantics.
Require Import Bool.
Require Import String.
Require Import List.
Require Import PeanoNat.


(*Inductive definition of type event*)
Inductive event := e : nat -> nat -> event.

(*A list of events*)
Definition E_net := list event.

(*Event equality function*)
Definition equalsEv (e0:event) (e1:event) := 
match (e0,e1) with (e id0 n0,e id1 n1) => (id0 =? id1) && (n0 =? n1) end.

(*Relation between events (message) defined as an inductive type*)
Inductive relation := forward : event -> event -> relation.

(*Equality of relations*)
Definition equalsR (r0:relation) (r1:relation) := match (r0,r1) with 
| (forward e0_in e0_out,forward e1_in e1_out) => if ((equalsEv e0_in e1_in) && (equalsEv e0_out e1_out)) then true else false end.

(*A list of relations*)
Definition R_net := list relation.

(*Function that checks if a list of relation contains a certain relation*)
Fixpoint containsR (rel:relation) (rl:R_net) : bool :=
match rl with 
|cons r_el next => if (equalsR r_el rel) then true else (containsR rel next)
|nil => false 
end. 

(*A d_net is a function that maps a event to a device*)
Definition d_net := event -> ident.
(*The returned value if a searched event doesn't exists*)
Definition base_d (e:event) := 0.
(*Add a event to a d_net, with respective device id*)
Definition add_d (new_e:event) (new_d:ident) (old:d_net): d_net :=(fun e => if (equalsEv e new_e) then new_d else (old e)).

(*A s_net is a function that maps a event to a sensor_state*)
Definition s_net := event -> sensor_state.
(*The returned value if a searched event doesn't exists*)
Definition base_s (e:event) := base.
(*Add a event to a s_net, with respective sensor_state*)
Definition add_s (new_e:event) (new_s:sensor_state) (old:s_net): s_net :=(fun e => if (equalsEv e new_e) then new_s else (old e)).


(*The augmented event structure, like defined in the papers*)
Inductive AES := aes : E_net -> R_net -> d_net -> s_net -> AES.

(*Space time values, a function that maps each event to a resulting nvalue*)
Definition STV := event -> nvalue.
Definition base_STV (e:event) := default l_fail.
Definition add_STV (new_e:event) (new_w:nvalue) (old:STV): STV := (fun e => if (equalsEv e new_e) then new_w else (old e)).

(*A vt_net is a function that maps a event to a value_tree*)
Definition vt_net := event -> value_tree.
Definition base_vt (e:event) := empty nil.
Definition add_vt (new_e:event) (new_vt:value_tree) (old:vt_net): vt_net :=(fun e => if (equalsEv e new_e) then new_vt else (old e)).

(*A function that return the source events of a event*)
Fixpoint before_event (b_e:event) (b_E:E_net) (b_R:R_net) (b_vts:vt_net) (b_d:d_net): value_tree_env :=
match b_E with 
| cons e_el next => if (containsR (forward e_el b_e) b_R) then vt_el (b_d e_el) (b_vts e_el) (before_event b_e next b_R b_vts b_d) 
else (before_event b_e next b_R b_vts b_d)
| nil => vt_end
end.


(*Function that check if a event is sourced by another event in a list*)
Fixpoint isSourcedBy (ev:event) (evList:E_net) (is_R:R_net) : bool :=
match evList with 
| cons evS next => if (containsR (forward evS ev) is_R) then true else isSourcedBy ev next is_R
| nil => false
end.


(*Only source event extractor*)
Fixpoint returnNotSourced (rts_rec_E:E_net) (rts_all_E:E_net) (rts_R:R_net) : option event :=
match rts_rec_E with 
| cons (ev) next => if (isSourcedBy ev rts_all_E rts_R) then returnNotSourced next rts_all_E rts_R else Some ev
| nil => None
end.



Fixpoint removeEv (ev:event) (evList:E_net) :=
match evList with 
| cons evL next => if (equalsEv evL ev) then (removeEv ev next) else cons evL (removeEv ev next)
| nil => nil
end.



(*Alternative net evaluation concept*)
Inductive net_conf_in: Type := netI : AES -> E_net -> vt_net -> exp -> net_conf_in.

Reserved Notation "t '|=>' t'" (at level 40).
Inductive net_val: net_conf_in -> STV -> Prop :=

| E_NET_0 : forall (e_main:exp) (n_E:E_net) (n_R:R_net) (n_d:d_net) (n_s:s_net) (vt_collected:vt_net) (n_stv:STV) ,

netI (aes n_E n_R n_d n_s) (nil) vt_collected e_main |=> n_stv

| E_NET_R : forall (e_main:exp) (n_E:E_net) (n_R:R_net) (n_d:d_net) (n_s:s_net) (vt_collected:vt_net) (n_stv:STV) 
(vt:value_tree) (free_ev:event) (ev_notExplored:E_net),

Some free_ev = returnNotSourced ev_notExplored ev_notExplored n_R ->

<[ n_d free_ev | n_s free_ev | (before_event free_ev n_E n_R vt_collected n_d)  | e_main ]> ==> <[ n_stv free_ev |  vt ]> ->

netI (aes n_E n_R n_d n_s) (removeEv free_ev ev_notExplored) (add_vt free_ev vt vt_collected) e_main |=> n_stv ->

netI (aes n_E n_R n_d n_s) ev_notExplored vt_collected e_main |=> n_stv

where "t '|=>' t'" := (net_val t t').



(*
Inductive net_conf_in: Type := netI : AES -> exp -> net_conf_in.
Inductive net_conf_out: Type := netO : STV -> vt_net -> net_conf_out.


Reserved Notation "t '|=>' t'" (at level 40).
Inductive net_val: net_conf_in -> net_conf_out -> Prop :=

| E_NET_0 : forall (e_main:exp) (n_R:R_net) (n_d:d_net) (n_s:s_net) (n_stv:STV) (vts:vt_net),

netI (aes (nil) n_R n_d n_s) e_main |=> netO n_stv vts


| E_NET_R : forall (e_main:exp) (ev:event) (next:E_net) (n_R:R_net) (n_d:d_net) (n_s:s_net) (n_stv:STV) (vt:value_tree)
(vts:vt_net),

<[ n_d ev | n_s ev |(before_event ev (cons ev next)  n_R vts n_d)  | e_main ]> ==> <[ n_stv ev |  vt ]> 

-> (vts ev)=vt 

-> netI (aes next n_R n_d n_s) e_main |=> netO n_stv vts

-> netI (aes (cons ev next) n_R n_d n_s) e_main |=> netO n_stv vts

where "t '|=>' t'" := (net_val t t').
*)












