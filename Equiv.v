Require Import Coq.Program.Equality.
Require Import List ZArith.
Require Import Arith.
Require Import Psatz.
Require Import Lia.
Import ListNotations.
Open Scope nat_scope.
Close Scope Z_scope.
Require Import String.
Open Scope string_scope.
Require Import While Tactics.
Require Import WhileSmallStep WhileBigStep.

Print star.
Print step.

Lemma star_seq:
  forall s1 env1 env2,
  star s1 env1 Skip env2
  -> forall s2 s3 env3,
  star s2 env2 s3 env3
  -> star (Seq s1 s2) env1 s3 env3.
Proof.
  intros s1 env1 env2 Hstar.
  dependent induction Hstar; simpl; intros.
  - eapply star_step.
    + eapply step_seq_skip.
    + apply H.
  - eapply star_step.
    + eapply step_seq. apply H.
    + apply IHHstar. reflexivity. apply H0.
Qed. 



Theorem bigstep_star:
  forall i env env', bigstep env i env' -> star i env Skip env'.
Proof.
  intros i env env' Hbigstep. induction Hbigstep.
  - apply star_refl.
  - eapply star_step.
    + apply step_assign.
    + apply star_refl.
  - eapply star_seq.
    + apply IHHbigstep1.
    + apply IHHbigstep2.
  - eapply star_step.
    + apply step_if_true. apply H.
    + apply IHHbigstep.
  - eapply star_step.
    + apply step_if_false. apply H.
    + apply IHHbigstep.
  - eapply star_step.
    + apply step_while_true. apply H.
    + eapply star_seq.
      * apply IHHbigstep1.
      * apply IHHbigstep2.
  - eapply star_step.
    + apply step_while_false. apply H.
    + apply star_refl.
Qed.

Print bigstep.

Lemma step_bigstep:
  forall i env i' env',
    step i env i' env' ->
    forall env'',
      bigstep env' i' env'' ->
      bigstep env i env''.
Proof.
  intros i env i' env' Hstep. induction Hstep; intros.
  - inversion H. eapply bigstep_assign.
  - eapply bigstep_if_true.
    + apply H.
    + apply H0.
  - eapply bigstep_if_false.
    + apply H.
    + apply H0.
  - inversion H0. subst. eapply bigstep_while_true.
    + apply H.
    + apply H4.
    + apply H6.
  - inversion H0. subst. eapply bigstep_while_false. apply H.
  - inversion H. subst. eapply bigstep_seq.
    + apply IHHstep. apply H3.
    + apply H5.
  - econstructor. 
    + econstructor.
    + apply H.
Qed.
Theorem star_bigstep:
  forall i env env', star i env Skip env' -> bigstep env i env'.
Proof.
  intros i env env' Hstar. dependent induction Hstar.
  - econstructor.
  - eapply step_bigstep.
    + apply H.
    + apply IHHstar. auto.
Qed.
  



