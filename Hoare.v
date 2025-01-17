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
Require Import While Tactics WhileBigStep.

(** * 6 - Logique de Hoare  *)

Definition pred := state -> Prop.

Definition valid_hoare_triple (P: pred) (s: stmt) (Q: pred) : Prop :=
  forall env1 env2, P env1 -> bigstep env1 s env2 -> Q env2.

(** ** Question 6.1  *)

Theorem hoare_skip: forall P, valid_hoare_triple P Skip P.
Proof.
  intros. unfold valid_hoare_triple. intros. inversion H0. subst. auto.
Qed.

(** ** Question 6.2  *)

(* Règle [SÉQUENCE] dans le sujet *)
Theorem hoare_seq:
  forall P Q R s1 s2,
  valid_hoare_triple P s1 Q
  -> valid_hoare_triple Q s2 R
  -> valid_hoare_triple P (Seq s1 s2) R.
Proof.
  intros. unfold valid_hoare_triple. intros. inversion H2; subst.
  eapply H0.
  - eapply H. eassumption. apply H6.
  - assumption.
Qed.
  

(* Règle [CONDITION]. *)
Theorem hoare_if:
  forall P Q c s1 s2,
  valid_hoare_triple (fun env => P env /\ eval_condP env c)  s1 Q
  -> valid_hoare_triple (fun env => P env /\ ~ eval_condP env c) s2 Q
  -> valid_hoare_triple P (If c s1 s2) Q.
Proof.
  intros. unfold valid_hoare_triple. intros. inversion H2; subst.
  - eapply H.
    + split.
      * apply H1.
      * apply H8.
    + assumption.
  - eapply H0.
    + split.
      * apply H1.
      * apply H8.
    + assumption.
Qed.

(* Règle [AFFECTATION]. On utilise [update_env] pour décrire l'effet de P[x <- E]. *)
Theorem hoare_assign:
  forall (P:pred) x e,
  valid_hoare_triple
    (fun env => P (update_state env x (eval_expr env e))) (Assign x e) P.
Proof.
  intros. unfold valid_hoare_triple. intros. inversion H0; subst.
  unfold update_state. simpl. assumption.
Qed.


(* Règle [STRENGTHEN]. *)
Theorem hoare_strengthen_pre:
  forall (P P' Q : pred) s,
  valid_hoare_triple P s Q
  -> (forall env, P' env -> P env)
  -> valid_hoare_triple P' s Q.
Proof.
  intros. unfold valid_hoare_triple. intros. eapply H.
  - apply H0. eassumption.
  - assumption.
Qed.
  

(* Règle [WEAKEN]. *)
Theorem hoare_weaken_post:
  forall (P Q Q' : pred) s,
  valid_hoare_triple P s Q
  -> (forall env, Q env -> Q' env)
  -> valid_hoare_triple P s Q'.
Proof.
  intros. unfold valid_hoare_triple. intros. eapply H0. eapply H.
  - eassumption.
  - assumption.
Qed.

(* Règle [WHILE]. *)
Theorem hoare_while:
  forall P c s I,
   valid_hoare_triple (fun env => P env /\ eval_condP env c) s P
   -> valid_hoare_triple
        P (While c I s) (fun env => P env /\ ~ eval_condP env c).
Proof.
  intros.
  remember (While c I s) as w.
  unfold valid_hoare_triple. intros.
  induction H1.
  - discriminate.
  - discriminate.
  - discriminate.
  - discriminate.
  - discriminate.
  - inversion Heqw. subst. apply IHbigstep2.
    * assumption.
    * unfold valid_hoare_triple in H. eapply H.
      + split.
        ** eassumption.
        ** assumption.
      + assumption.
  - split.
    * assumption.
    * inversion Heqw. subst. assumption.
Qed.
 

(** ** Question 6.7  *)
Lemma hoare_while':
  forall (P Q : pred ) c s I,
  valid_hoare_triple (fun env => I env /\ eval_condP env c) s I
  -> (forall env, P env -> I env)
  -> (forall env, I env /\ ~eval_condP env c -> Q env)
  -> valid_hoare_triple P (While c I s) Q.
Proof.
  intros. eapply hoare_weaken_post.
  - eapply hoare_strengthen_pre.
    + eapply hoare_while. eassumption.
    + intros. apply H0. assumption.
  - intros. apply H1. assumption.
Qed.


Open Scope Z_scope.

Definition factorielle n :=
  Seq
    (Assign "res" (Const 1))
    (While
      (Lt (Const 0) (Var "n"))
      (fun env => env "res" * Zfact (env "n") = Zfact n)
      (Seq
        (Assign "res" (Mul (Var "res") (Var "n")))
        (Assign "n" (Sub (Var "n") (Const 1)))
      )
    ).

(* Cette preuve devrait passer *)

Lemma fact_correct_first_try:
  forall n, n >= 0 ->
            valid_hoare_triple (fun env => env "n" = n) (factorielle n) (fun env => env "res" = Zfact n).
Proof.
  intros n NPOS. unfold factorielle.
  eapply hoare_strengthen_pre.
  apply hoare_seq with (Q:= fun env => env "res" = 1 /\ env "n" = n). eapply hoare_assign.
  apply hoare_while'.
  - eapply hoare_strengthen_pre. eapply hoare_seq. eapply hoare_assign.
    apply hoare_assign.
    unfold update_state; simpl. intros.
    destruct H. rewrite <- H.
    rewrite <- Z.mul_assoc. f_equal.
    rewrite (Zfact_pos (env "n")). 2: lia. auto.
  - simpl. intros env [A B]; rewrite A, B. lia.
  - simpl. intros env [A B].
    rewrite <- A.
    rewrite Zfact_neg. 2: lia. lia.
  - unfold update_state; simpl. auto.
Qed.

(* Elle est passée !*)

Fixpoint vars_affected (s: stmt) : list var :=
  match s with
  | Skip => []
  | Assign v e => [v]
  | Seq s1 s2 => vars_affected s1 ++ vars_affected s2
  | If c s1 s2 => vars_affected s1 ++ vars_affected s2
  | While c _ s => vars_affected s
  end.

Fixpoint wp (s: stmt) (Q: pred) : pred :=
  match s with
  | Skip         => Q
  | Assign v e   => fun env => Q (update_state env v (eval_expr env e))
  | Seq s1 s2    => wp s1 (wp s2 Q)
  | If c s1 s2   =>
    fun env =>
      (eval_condP env c -> wp s1 Q env) /\ (~ eval_condP env c -> wp s2 Q env)
  | While c II s =>
    fun env =>
      II env
      /\ let vv := vars_affected s in
         forall env',
         (forall x, ~ In x vv -> env x = env' x)
         -> (eval_condP env' c -> II env' -> wp s II env')
            /\ (~ eval_condP env' c -> II env' -> Q env')
  end.

Lemma bigstep_vars_affected:
  forall env1 s env2,
  bigstep env1 s env2
  -> forall x, ~ In x (vars_affected s)
  -> env1 x = env2 x.
Proof.
  intros.
  induction H.
  - reflexivity.
  - simpl in H0. unfold update_state. destruct (var_eq x x0).
    + subst. exfalso. apply H0. left. reflexivity.
    + reflexivity.
  - eapply eq_trans.
    + apply IHbigstep1. intros Habs. apply H0. simpl. apply in_or_app. left. assumption.
    + apply IHbigstep2. intros Habs. apply H0. simpl. apply in_or_app. right. assumption.
  - apply IHbigstep. intros Habs. apply H0. simpl. apply in_or_app. left. assumption.
  - apply IHbigstep. intros Habs. apply H0. simpl. apply in_or_app. right. assumption.
  - eapply eq_trans.
    + apply IHbigstep1. simpl in H0. eassumption.
    + apply IHbigstep2. simpl in H0. eassumption.
  - reflexivity.
Qed.

Lemma auto_hoare_while:
  forall
    c (I: pred) s (Q: pred) (IHs : valid_hoare_triple (wp s I) s I) env1 env2
    (Itrue: I env1)
    (CondTrue:
      forall env' : var -> val,
      (forall x : var, ~ In x (vars_affected s) -> env1 x = env' x)
      -> eval_condP env' c -> I env' -> wp s I env'
    )
   (CondFalse:
     forall env' : var -> val,
     (forall x : var, ~ In x (vars_affected s) -> env1 x = env' x)
     -> ~ eval_condP env' c -> I env' -> Q env'
   )
   (Heval : bigstep env1 (While c I s) env2),
    Q env2.
Proof.
  intros c I s Q IHs env1 env2 Itrue CondTrue CondFalse Heval.
  dependent induction Heval. 
    - clear IHHeval1. eapply IHHeval2 with (s:=s) (I:=I) (c:=c); auto.
      + eapply IHs.
        * apply (CondTrue env); auto.
        * auto.
      + intros. apply CondTrue.
        * intros. eapply eq_trans. 
          ** eapply bigstep_vars_affected; eauto.
          ** apply H0. apply H3.
        * auto.
        * auto.
      + intros. apply CondFalse.
        * intros. eapply eq_trans. 
          ** eapply bigstep_vars_affected; eauto.
          ** apply H0. apply H3.
        * auto.
        * auto.
    - eapply CondFalse.
      + intros. reflexivity.
      + auto.
      + auto.
Qed.


Theorem auto_hoare: forall s Q, valid_hoare_triple (wp s Q) s Q.
Proof.
  intros.
  dependent induction s.
  - apply hoare_skip.
  - apply hoare_assign.
  - eapply hoare_seq.
    + apply IHs1.
    + apply IHs2.
  - simpl. unfold valid_hoare_triple. intros. destruct H. inversion H0; subst.
    + eapply IHs1.
      * apply H. assumption.
      * assumption.
    + eapply IHs2.
      * apply H1. assumption.
      * assumption.
  - simpl. unfold valid_hoare_triple. intros. destruct H. eapply auto_hoare_while.
    + apply IHs.
    + apply H.
    + intros.
      apply H1 in H3.
      * assumption.
      * apply H2.
      * assumption.
    + apply H1.
    + assumption.
Qed.

Lemma auto_hoare':
  forall (P: pred) s Q,
  (forall env, P env -> wp s Q env)
  -> valid_hoare_triple P s Q.
Proof.
  intros. eapply hoare_strengthen_pre.
  - apply auto_hoare.
  - assumption.
Qed.

