(** Borrowed from Pierce's "Software Foundations" *)

Require Import Arith Arith.EqNat.
Require Import Lia.

(* note: every id converts number into name *) 
Inductive id : Type :=
  Id : nat -> id.
             
(* note: precedence level + assoc/no assoc  *)
Reserved Notation "m i<= n" (at level 70, no associativity).
Reserved Notation "m i>  n" (at level 70, no associativity).
Reserved Notation "m i<  n" (at level 70, no associativity).

(* note: less or equal on idents. result -- proposition *)
(* "where" block binds syntax sugar "i<=" with function above *)
Inductive le_id : id -> id -> Prop :=
  le_conv : forall n m, n <= m -> (Id n) i<= (Id m)
where "n i<= m" := (le_id n m).   

(* note: less than on idents *)
Inductive lt_id : id -> id -> Prop :=
  lt_conv : forall n m, n < m -> (Id n) i< (Id m)
where "n i< m" := (lt_id n m).   

(* note: greater than on idents *)
Inductive gt_id : id -> id -> Prop :=
  gt_conv : forall n m, n > m -> (Id n) i> (Id m)
where "n i> m" := (gt_id n m).   

(* note: Ltac (tactic language) --  *)
(* goal is the statement that we want to proof *)
Ltac prove_with th :=
  intros; (* reads vars and hypotheses from theorem's conditions, puts them into context *)
  repeat (match goal with H: id |- _ => destruct H end); (* convert vars into numbers *)
  match goal with n: nat, m: nat |- _ => set (th n m) end; (* applies theorem to two number args *)
  repeat match goal with H: _ + {_} |- _ => inversion_clear H end; (* breaks sum ("or"?) into two parts *)
  try match goal with H: {_} + {_} |- _ => inversion_clear H end;
  repeat
    match goal with
    (* if hypothesis is that n<m and the goal is {Id ?n i< Id ?m}, then *)
      H: ?n <  ?m |-  _                + {Id ?n i< Id ?m}  => right
    | H: ?n <  ?m |-  _                + {_}               => left
    | H: ?n >  ?m |-  _                + {Id ?n i> Id ?m}  => right
    | H: ?n >  ?m |-  _                + {_}               => left
    | H: ?n <  ?m |- {_}               + {Id ?n i< Id ?m}  => right
    | H: ?n <  ?m |- {Id ?n i< Id ?m}  + {_}               => left
    | H: ?n >  ?m |- {_}               + {Id ?n i> Id ?m}  => right
    | H: ?n >  ?m |- {Id ?n i> Id ?m}  + {_}               => left
    | H: ?n =  ?m |-  _                + {Id ?n =  Id ?m}  => right
    | H: ?n =  ?m |-  _                + {_}               => left
    | H: ?n =  ?m |- {_}               + {Id ?n =  Id ?m}  => right
    | H: ?n =  ?m |- {Id ?n =  Id ?m}  + {_}               => left
    | H: ?n <> ?m |-  _                + {Id ?n <> Id ?m}  => right
    | H: ?n <> ?m |-  _                + {_}               => left
    | H: ?n <> ?m |- {_}               + {Id ?n <> Id ?m}  => right
    | H: ?n <> ?m |- {Id ?n <> Id ?m}  + {_}               => left

    | H: ?n <= ?m |-  _                + {Id ?n i<= Id ?m} => right
    | H: ?n <= ?m |-  _                + {_}               => left
    | H: ?n <= ?m |- {_}               + {Id ?n i<= Id ?m} => right
    | H: ?n <= ?m |- {Id ?n i<= Id ?m} + {_}               => left
    end;
    (* constructor => evaluates operators based on "where" blocks where they were bound *)
    (* assumption -- trivia, congruence -- can prove equality, including id = id *)
  try (constructor; assumption); congruence.

Lemma lt_eq_lt_id_dec: forall (id1 id2 : id), {id1 i< id2} + {id1 = id2} + {id2 i< id1}.
Proof. prove_with lt_eq_lt_dec. Qed.
  
Lemma gt_eq_gt_id_dec: forall (id1 id2 : id), {id1 i> id2} + {id1 = id2} + {id2 i> id1}.
Proof. prove_with gt_eq_gt_dec. Qed.

Lemma le_gt_id_dec : forall id1 id2 : id, {id1 i<= id2} + {id1 i> id2}.
Proof. prove_with le_gt_dec. Qed.

(* numbers either equal or not, returns one case (?) *)
Lemma id_eq_dec : forall id1 id2 : id, {id1 = id2} + {id1 <> id2}.
Proof. prove_with eq_nat_dec. Qed.

(* (if id=id then p else q) = p *)
Lemma eq_id : forall (T:Type) x (p q:T), (if id_eq_dec x x then p else q) = p.
Proof. 
  intros.
  destruct (id_eq_dec x x).
  - reflexivity. (* fst goal ({x=x}) will be closed well via reflexivity *)
  - contradiction. (* snd goal ({x<>x}) will be closed with contradiction  *)
Qed.

(* x!=y => (if x=y then p else q) = q *)
Lemma neq_id : forall (T:Type) x y (p q:T), x <> y -> (if id_eq_dec x y then p else q) = q.
Proof.
  intros. (* now in context: x, y: id; T: Type; p, q: T, x<>y: H (hypothesis) *)
  destruct (id_eq_dec x y).
  (* try to put either {x=y} or {x<>y} into context.
  if {x=y} is chosen, then "if" goes into fst branch => goal is {p=q}.
  we have hypothesis {x<>y} aka x=y -> False => context is contradictive now.
  the contradiction tactic finds it and closes the goal
  if {x<>y} is chosen, then "if" goes into snd branch => goal is {q=q}
  the reflexivity tactic closes that goal with eq_refl object
   *)
  - contradiction.
  - reflexivity.
Qed.

(* if id1>id2 then id2>id1 is false *)
Lemma lt_gt_id_false : forall id1 id2 : id,
    id1 i> id2 -> id2 i> id1 -> False.
Proof.
  intros [a] [b] H_gt H_lt.
  inversion H_gt.
  inversion H_lt.
  lia. (* can see contradictions in linear expressions inside context *)
Qed.

(* if id2 >= id1 then id2<id1 is false *)
Lemma le_gt_id_false : forall id1 id2 : id,
    id2 i<= id1 -> id2 i> id1 -> False.
Proof.
  intros [a] [b] H_le H_gt.
  inversion H_le.
  inversion H_gt.
  lia.
Qed.

(* helper for next lemma *)
Lemma le_id_nat : forall n m, Id n i<= Id m -> n <= m.
Proof.
  intros n m H.
  inversion H.
  assumption.
Qed.

(* if id1<=id2 then (id1=id2 or id1<id2) *)
Lemma le_lt_eq_id_dec : forall id1 id2 : id, 
    id1 i<= id2 -> {id1 = id2} + {id2 i> id1}.
Proof.
  intros [n] [m] H_le.
  destruct (eq_nat_dec n m) as [H_eq | H_neq].
  - left. subst. reflexivity.
  - right. apply gt_conv.
    pose proof (le_id_nat n m H_le) as H_nm.
    lia.
Qed.

Lemma neq_lt_gt_id_dec : forall id1 id2 : id,
    id1 <> id2 -> {id1 i> id2} + {id2 i> id1}.
Proof. 
  intros id1 id2 H_neq.
  destruct (le_gt_id_dec id1 id2) as [H_le | H_gt].
  - (* id1 i<= id2 *)
    destruct (le_lt_eq_id_dec id1 id2 H_le) as [H_eq | H_gt2].
    + contradiction.
    + right. exact H_gt2.
  - (* id1 i> id2 *)
    left. exact H_gt.
Qed.
    
Lemma eq_gt_id_false : forall id1 id2 : id,
    id1 = id2 -> id1 i> id2 -> False.
Proof. 
  intros id1 id2 H_eq H_gt.
  destruct H_gt as [n m H_gt_nat].
  injection H_eq as H_eq_nat.
  lia.
Qed.
