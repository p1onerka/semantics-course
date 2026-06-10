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

(* if id1<=id2 then (id1=id2 or id1<id2) *)
Lemma le_lt_eq_id_dec : forall id1 id2 : id, 
    id1 i<= id2 -> {id1 = id2} + {id2 i> id1}.
Proof.
  (*intros [a] [b] H_a_le_b.
  destruct (gt_eq_gt_dec a b) as [[H_a_gt_b | H_eq] | H_a_lt_b].
  - (* anything can be proven from the False *)
    destruct H_a_le_b
    inversion H_a_le_b as [a' b' Hle].
    subst.
    lia.
  - left.
    destruct H_eq.
    exact H_eq.
  - right.
    exact H_a_lt_b.*)


  (*inversion H_le as [a' b' H]; subst. (* because hypothesis was built from constructor *)
  destruct (Nat.eq_dec a b) as [H_eq | H_neq].
  - left.
    subst.
    reflexivity.
  - right.
    constructor.
    lia.*)
admit. Admitted.

Lemma neq_lt_gt_id_dec : forall id1 id2 : id,
    id1 <> id2 -> {id1 i> id2} + {id2 i> id1}.
Proof. admit. Admitted.
    
Lemma eq_gt_id_false : forall id1 id2 : id,
    id1 = id2 -> id1 i> id2 -> False.
Proof. admit. Admitted.
