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
Require Import WhileBigStep.
Require Import Lia.

Fixpoint exec_prog (fuel: nat) (env: state) (i: stmt) : option state :=
  match fuel with
  | O => None
  | S fuel' =>
    match i with
    | Skip => Some env
    | Assign x e => Some (update_state env x ( eval_expr env e))
    | Seq s1 s2 =>
      match exec_prog fuel' env s1 with
      | Some env' => exec_prog fuel' env' s2
      | None => None
      end 
    | If c s1 s2 => 
      if eval_cond env c
      then exec_prog fuel' env s1
      else exec_prog fuel' env s2
    | While c I1 s => 
      if eval_cond env c
      then match exec_prog fuel' env s with
           | Some env' => exec_prog fuel' env' (While c I1 s)
           | None => None
          end
      else Some env
    end
  end.

(* On définit un programme qui calcule la somme des entiers de 1 à 10. *)

Definition p1 :=
  Seq
    (Assign "x" (Const 10%Z))
    (Seq
      (Assign "sum" (Const 0%Z))
      (While
        (Not (Eq (Var "x") (Const 0%Z)))
        (fun _ => True)
        (Seq
          (Assign "sum" (Add (Var "sum") (Var "x")))
          (Assign "x" (Sub (Var "x") (Const 1%Z)))
        )
      )
    ).

(* Le calcul suivant devrait retourner [Some 55]. *)
Compute
  option_map (fun env => env "sum")
  (exec_prog 30 (fun _ => 0%Z) p1).

Theorem exec_prog_bigstep:
  forall fuel s i s', exec_prog fuel s i = Some s' -> bigstep s i s'.
Proof.
  induction fuel; intros s i s' Hexec.
  - discriminate.
  - destruct i.
    + inversion Hexec. apply bigstep_skip.
    + inversion Hexec. apply bigstep_assign.
    + inversion Hexec. destruct (exec_prog fuel s i1) eqn:Hexec1.
      * apply bigstep_seq with (env':=s0).
        -- apply IHfuel. apply Hexec1.
        -- apply IHfuel. apply H0.
      * discriminate.
    + destruct (eval_cond s c) eqn:Hcond.
      * inversion Hexec. apply bigstep_if_true.
        -- rewrite eval_cond_true. apply Hcond.
        -- apply IHfuel. rewrite Hcond in H0. apply H0.
      * inversion Hexec. apply bigstep_if_false.
        -- rewrite eval_cond_false. apply Hcond.
        -- apply IHfuel. rewrite Hcond in H0. apply H0.
    + destruct (eval_cond s c) eqn:Hcond.
      * destruct (exec_prog fuel s i) eqn:Hexec1.
        -- inversion Hexec. rewrite Hcond in H0. apply bigstep_while_true with (env':=s0).
          ++ rewrite eval_cond_true. apply Hcond.
          ++ apply IHfuel. apply Hexec1.
          ++ apply IHfuel. rewrite Hexec1 in H0. apply H0.
        -- inversion Hexec. rewrite Hcond in H0. rewrite Hexec1 in H0. discriminate.
      * inversion Hexec. rewrite Hcond in H0. inversion H0. apply bigstep_while_false.
        rewrite eval_cond_false. rewrite <- H1. apply Hcond.
Qed.



Lemma exec_prog_more_fuel:
  forall f s i s',
  exec_prog f s i = Some s'
  -> forall f', f' >= f
  -> exec_prog f' s i = Some s'.
Proof.
  intros f. induction f; intros.
  - discriminate.
  - destruct f'.
    + lia.
    + destruct i.
      * inversion H. reflexivity.
      * inversion H. reflexivity.
      * simpl. simpl in H. destruct (exec_prog f s i1) eqn:Hexec1.
        -- apply IHf with (f':=f') in Hexec1.
            ++ rewrite Hexec1. apply IHf with (f':=f') in H.
                ** apply H.
                ** lia.
            ++ lia.
        -- discriminate.
      * simpl. simpl in H. destruct (eval_cond s c) eqn:Hcond.
        -- apply IHf with (f':=f') in H.
            ++ rewrite H. reflexivity.
            ++ lia.
        -- apply IHf with (f':=f') in H. 
            ++ rewrite H. reflexivity.
            ++ lia.
      * simpl. simpl in H. destruct (eval_cond s c) eqn:Hcond.
        -- destruct (exec_prog f s i) eqn:Hexec1.
            ++ apply IHf with (f':=f') in Hexec1.
                ** rewrite Hexec1. apply IHf with (f':=f') in H.
                    --- apply H.
                    --- lia.
                ** lia.
            ++ discriminate.
        -- apply H.
Qed.

Theorem bigstep_exec_prog:
  forall s i s',
  bigstep s i s'
  -> exists fuel, exec_prog fuel s i = Some s'.
Proof.
  intros s i s' Hbigstep.
  induction Hbigstep.
  - exists 1. reflexivity.
  - exists 1. reflexivity.
  - destruct IHHbigstep1 as [fuel1 H1].
    destruct IHHbigstep2 as [fuel2 H2].
    exists (S (max fuel1 fuel2)). simpl. rewrite exec_prog_more_fuel with (f:=fuel1) (s':=env').
    + rewrite exec_prog_more_fuel with (f:=fuel2) (s':=env'').
      * reflexivity.
      * apply H2.
      * lia.
    + apply H1.
    + lia.
  - destruct IHHbigstep as [fuel1 H1].
    exists (S fuel1). simpl. rewrite H1. apply eval_cond_true in H. rewrite H. reflexivity.
  - destruct IHHbigstep as [fuel1 H1].
    exists (S fuel1). simpl. rewrite H1. apply eval_cond_false in H. rewrite H. reflexivity.
  - destruct IHHbigstep1 as [fuel1 H1].
    destruct IHHbigstep2 as [fuel2 H2].
    exists (S (max fuel1 fuel2)). simpl. apply eval_cond_true in H. rewrite H.
    + destruct (exec_prog fuel1 env s) eqn:Hexec1.
      * rewrite exec_prog_more_fuel with (f:=fuel1) (s':=env').
        -- rewrite exec_prog_more_fuel with (f:=fuel2) (s':=env'').
            ++ reflexivity.
            ++ apply H2.
            ++ lia.
        -- rewrite <- H1. apply Hexec1.
        -- lia.
      * discriminate.
  - exists 1. simpl. apply eval_cond_false in H. rewrite H. reflexivity.
Qed.

     

