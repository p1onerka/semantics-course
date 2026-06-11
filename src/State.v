(** Based on Benjamin Pierce's "Software Foundations" *)

Require Import List.
Import ListNotations.
Require Import Lia.
Require Export Arith Arith.EqNat.
Require Export Id.

Section S.

  (* Set means that type is arbitrary *)
  Variable A : Set.
  
  (* list of pairs: id with type A *)
  Definition state := list (id * A). 

  Reserved Notation "st / x => y" (at level 0).

  Inductive st_binds : state -> id -> A -> Prop := 
  (* if (id, x) is in the head pair, return x *)
    st_binds_hd : forall st id x, ((id, x) :: st) / id => x
  (* if fst pair isnt id, then exclude it from st and try again *)
  | st_binds_tl : forall st id x id' x', id <> id' -> st / id => x -> ((id', x')::st) / id => x
  where "st / x => y" := (st_binds st x y).

  (* put new pair inro list (it will override (shadow?) old value, if exists, because st_binds takes first pair) *)
  Definition update (st : state) (id : id) (a : A) : state := (id, a) :: st.

  Notation "st [ x '<-' y ]" := (update st x y) (at level 0).
  
  (* Functional version of binding-in-a-state relation *)
  (* like st_binds, finds the value of given id in given state *)
  Fixpoint st_eval (st : state) (x : id) : option A :=
    match st with
    | (x', a) :: st' =>
        if id_eq_dec x' x then Some a else st_eval st' x
    | [] => None
    end.
 
  (* State a prove a lemma which claims that st_eval and
     st_binds are actually define the same relation.
  *)
  (* TODO: Lemma st_binds_eval_eq : forall st x a, st / x => a <-> st_eval st x = Some a.
  Proof.
    split.
    - (* => *)

    - (* <= *)
  Qed.*)

  (* if state binds x to both n and m, then n=m *)
  Lemma state_deterministic' (st : state) (x : id) (n m : option A)
    (SN : st_eval st x = n)
    (SM : st_eval st x = m) :
    n = m.
  Proof using Type.
    subst n. subst m. reflexivity.
  Qed.
  
  (* same for st_binds *)
  Lemma state_deterministic (st : state) (x : id) (n m : A)   
    (SN : st / x => n)
    (SM : st / x => m) :
    n = m. 
  Proof using Type.
    induction SN;
    inversion SM;
    subst;
    auto; (* half of cases: hd/hd and tl/tl, will succeed, other half will cause a conrtadiction *)
    contradiction.
  Qed.
  
  (* update works *)
  Lemma update_eq (st : state) (x : id) (n : A) :
    st [x <- n] / x => n.
  Proof.
    unfold update. (* places actual function into expression *)
    constructor.
  Qed.

  (* updating one value doesnt change the other *)
  Lemma update_neq (st : state) (x2 x1 : id) (n m : A)
        (NEQ : x2 <> x1) : st / x1 => m <-> st [x2 <- n] / x1 => m.
  Proof.
    unfold update.
    split.
    - (* => *)
      intros H.
      apply st_binds_tl with (id':=x2) (x':=n); auto.
    - (* <= *)
      intros H; inversion H; subst; [contradiction | assumption].
  Qed.
  
  (* shadowing of one var doesnt affect other. TODO: check if could be more elegant *)
  Lemma update_shadow (st : state) (x1 x2 : id) (n1 n2 m : A) :
    st[x2 <- n1][x2 <- n2] / x1 => m <-> st[x2 <- n2] / x1 => m.
  Proof.
    destruct (id_eq_dec x1 x2) as [H_eq | H_neq].
    - (* x1=x2 *)
      subst. split; intro H.
      + assert (m = n2).
        { eapply state_deterministic.
          - exact H.
          - apply update_eq.
        }
        subst. apply update_eq.
      + assert (m = n2).
        { eapply state_deterministic.
          - exact H.
          - apply update_eq.
        }
        subst. apply update_eq.
    - (* x1!=x2 *)
      split; intro H.
      + apply update_neq in H; auto.
        apply update_neq in H; auto.
        apply update_neq; auto.
      + apply update_neq in H; auto.
        apply update_neq; auto.
        apply update_neq; auto.
  Qed.
  
  (* update with same value doesnt affect other pairs *)
  Lemma update_same (st : state) (x1 x2 : id) (n1 m : A)
        (SN : st / x1 => n1)
        (SM : st / x2 => m) :
    st [x1 <- n1] / x2 => m.
  Proof.
    destruct (id_eq_dec x1 x2) as [H_Eq | H_NotEq].
    - subst.
      assert (m = n1).
      { eapply state_deterministic; eauto. }
      subst.
      apply update_eq.
    - apply update_neq.
      + exact H_NotEq.
      + exact SM.
    (*intros.
    unfold update.
    induction SN.
    induction SM.
    assert (m = n1) by (eapply state_deterministic; eauto).
    subst.
    apply update_eq.*)
  Qed.
  
  (* the order of updates doesnt affect other pairs. TODO: more elegant? *)
  Lemma update_permute (st : state) (x1 x2 x3 : id) (n1 n2 m : A)
        (NEQ : x2 <> x1)
        (SM : st [x2 <- n1][x1 <- n2] / x3 => m) :
    st [x1 <- n2][x2 <- n1] / x3 => m.
  Proof. 
      destruct (id_eq_dec x3 x1) as [H_eq | H_neq].
  - (* x1=x3 => n2=m *)
    subst. assert (m = n2).
    {
      eapply state_deterministic.
      - exact SM.
      - apply update_eq.
    }
    subst. apply update_neq.
    + exact NEQ.
    + apply update_eq.
  - (* x1!=x3 => (x2=x3 => m=n1) | (m!=n1) *)
    destruct (id_eq_dec x3 x2) as [H_eq_inner | H_neq_inner].
    + subst. assert (m = n1).
      {
        eapply state_deterministic.
        - exact SM.
        - apply update_neq.
          * congruence.
          * apply update_eq.
      }
      subst. apply update_eq.
    + apply update_neq in SM; auto.
      apply update_neq in SM; auto.
      apply update_neq; auto.
      apply update_neq; auto.
  Qed.

  (* not true. TODO: proof *)
  Lemma state_extensional_equivalence (st st' : state) (H: forall x z, st / x => z <-> st' / x => z) : st = st'.
  Proof. Abort.

  Definition state_equivalence (st st' : state) := forall x a, st / x => a <-> st' / x => a.

  Notation "st1 ~~ st2" := (state_equivalence st1 st2) (at level 0).

  Lemma st_equiv_refl (st: state) : st ~~ st.
  Proof.
    unfold state_equivalence.
    intros x a.
    split; intro H; exact H.
  Qed.

  Lemma st_equiv_symm (st st': state) (H: st ~~ st') : st' ~~ st.
  Proof.
    unfold state_equivalence.
    intros x a.
    split; intro H'; apply H; exact H'.
  Qed.

  Lemma st_equiv_trans (st st' st'': state) (H1: st ~~ st') (H2: st' ~~ st'') : st ~~ st''.
  Proof.
    unfold state_equivalence.
    intros x a.
    split; intro H.
    - apply H2. apply H1. exact H.
    - apply H1. apply H2. exact H.
  Qed.

  Lemma equal_states_equive (st st' : state) (HE: st = st') : st ~~ st'.
  Proof.
    unfold state_equivalence.
    intros x a. (*Show.*)
    rewrite HE. (*Show.*)
    split; intro H; exact H.
  Qed.
  
End S.
