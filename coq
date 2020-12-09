

Coercion anum : nat >-> AExp.
Coercion avar : Var >->AExp.

Notation "A +' B" := (aplus A B) (at level 50, left associativity).
Notation "A -' B" := (aminus A B) (at level 50, left associativity).
Notation "A *' B" := (amul A B) (at level 40, left associativity).
Notation "A /' B" := (adiv A B) (at level 40, left associativity).
Notation "A %' B" := (amod A B) (at level 40, left associativity).

Definition Env := Var -> nat.

Definition env1 : Env :=
  fun x =>
    if (Var_eq_dec x n)
    then 10
    else 0.

Definition update (env : Env)
           (x : Var) (v : nat) : Env :=
  fun y =>
    if (Var_eq_dec y x)
    then v
    else (env y).

Fixpoint eval (a : AExp) (env : Env) : nat :=
  match a with
  | avar var => env var
  | anum nr => nr
  | aplus a1 a2 => (eval a1 env) + (eval a2 env)
  | amul a1 a2 => (eval a1 env) * (eval a2 env)
  | aminus a1 a2 => (eval a1 env) - (eval a2 env)
  | adiv a1 a2 =>  Nat.div (eval a1 env) (eval a2 env)
  | amod a1 a2 => Nat.modulo (eval a1 env) (eval a2 env)
  end.

(* 1 *)

Reserved Notation "A =[ S ]=> N" (at level 60).
(* Inductive aeval (a : AExp) (sigma : Env) (n : nat) : Prop := *)
(* | const : a = n -> a =[ sigma ]=> n *)
(* where "a =[ sigma ]=> n" := (aeval a sigma n). *)

Inductive aeval : AExp -> Env -> nat -> Prop :=
| const : forall n sigma, anum n =[ sigma ]=> n (* <n,sigma> => <n> *) 
| var : forall v sigma, avar v =[ sigma ]=> (sigma v) (* <v,sigma> => sigma(x) *)
| add : forall a1 a2 i1 i2 sigma n,
    a1 =[ sigma ]=> i1 ->
    a2 =[ sigma ]=> i2 ->
    n = i1 + i2 ->
    a1 +' a2 =[sigma]=> n
| times : forall a1 a2 i1 i2 sigma n,
    a1 =[ sigma ]=> i1 ->
    a2 =[ sigma ]=> i2 ->
    n = i1 * i2 ->
    a1 *' a2 =[sigma]=> n
| minus : forall a1 a2 i1 i2 sigma n,
    a1 =[ sigma ]=> i1 ->
    a2 =[ sigma ]=> i2 ->
    n = i1 - i2 ->
    a1 -' a2 =[sigma]=> n
| div : forall a1 a2 i1 i2 sigma n,
    a1 =[ sigma ]=> i1 ->
    a2 =[ sigma ]=> i2 ->
    n = Nat.div i1 i2 ->
    a1 /' a2 =[sigma]=> n
| modulo : forall a1 a2 i1 i2 sigma n,
    a1 =[ sigma ]=> i1 ->
    a2 =[ sigma ]=> i2 ->
    n = Nat.modulo i1 i2 ->
    a1 %' a2 =[sigma]=> n
where "a =[ sigma ]=> n" := (aeval a sigma n).

Require Import Omega.

Example ex_minus : 12 -' 2 =[ env1 ]=> 10.
Proof.
  eapply minus.
  - apply const.
  - apply const.
  - omega.
Qed.

Example ex_div : 6 /' 3 =[ env1 ]=> 2.
Proof.
  eapply div.
  - apply const.
  - apply const.
  - simpl. reflexivity.
Qed.

Example ex_modulo : 7 %' 5 =[ env1 ]=>2.
Proof.
  eapply modulo.
  - apply const.
  - apply const.
  - simpl. reflexivity.
Qed.

(* 2 *)

Lemma equiv :
  forall aexp sigma n,
    n = eval aexp sigma ->
    aexp =[ sigma ]=> n.
Proof.
  induction aexp; intros; simpl; subst.
  - apply var.
  - apply const.
  - eapply add; eauto.
  - eapply times; eauto.
  - eapply minus; eauto.
  - eapply div; eauto.
  - eapply modulo; eauto.
Qed.

(* 3 *)

Inductive BExp :=
| btrue : BExp
| bfalse : BExp
| bnot : BExp -> BExp
| band : BExp -> BExp -> BExp
| bor : BExp -> BExp -> BExp
| blessthan : AExp -> AExp -> BExp
| bmorethan : AExp -> AExp -> BExp
| blessequal : AExp -> AExp -> BExp
| bmoreequal : AExp -> AExp -> BExp.

Scheme Equality for BExp.

Notation " ! A" := (bnot A) (at level 70, no associativity).
Notation " A <' B" := (blessthan A B) (at level 70, no associativity).
Notation " A >' B" := (bmorethan A B) (at level 70, no associativity).
Notation " A <=' B" := (blessequal A B) (at level 70, no associativity).
Notation " A >=' B" := (bmoreequal A B) (at level 70, no associativity).
Notation "A 'and'' B" := (band A B) (at level 40, left associativity).
Notation "A 'or'' B" := (bor A B) (at level 40, left associativity).
Reserved Notation "B ={ S }=> B'" (at level 70).

Inductive beval : BExp -> Env -> bool -> Prop :=
| e_true : forall sigma, btrue ={ sigma }=> true
| e_false : forall sigma, bfalse ={ sigma }=> false
| e_lessthan : forall a1 a2 i1 i2 sigma b,
    a1 =[ sigma ]=> i1 ->
    a2 =[ sigma ]=> i2 ->
    b = Nat.leb i1 i2 ->
    a1 <=' a2 ={ sigma }=> b
| e_nottrue : forall b sigma,
    b ={ sigma }=> true ->
    (bnot b) ={ sigma }=> false
| e_notfalse : forall b sigma,
    b ={ sigma }=> false ->
    (bnot b) ={ sigma }=> true
| e_andtrue : forall b1 b2 sigma t,
    b1 ={ sigma }=> true ->
    b2 ={ sigma }=> t ->
    band b1 b2 ={ sigma }=> t
| e_andfalse : forall b1 b2 sigma,
    b1 ={ sigma }=> false ->
    band b1 b2 ={ sigma }=> false
where "B ={ S }=> B'" := (beval B S B').

Inductive Stmt :=
| assignment : Var -> AExp -> Stmt
| sequence : Stmt -> Stmt -> Stmt
| ifthenelse : BExp -> Stmt -> Stmt -> Stmt
| while : BExp -> Stmt -> Stmt.

Notation "X ::= A" := (assignment X A) (at level 50).
Notation "S1 ;; S2" := (sequence S1 S2) (at level 90).
Notation "'if'' B 'then'' S1 'else'' S2 'end''" := (ifthenelse B S1 S2) (at level 97).

Reserved Notation "S -{ Sigma }-> Sigma'" (at level 60).
Inductive eval0 : Stmt -> Env -> Env -> Prop :=
| e_assignment: forall a i x sigma sigma',
    a =[ sigma ]=> i ->
    sigma' = (update sigma x i) ->
    (x ::= a) -{ sigma }-> sigma'
| e_seq : forall s1 s2 sigma sigma1 sigma2,
    s1 -{ sigma }-> sigma1 ->
    s2 -{ sigma1 }-> sigma2 ->
    (s1 ;; s2) -{ sigma }-> sigma2
| e_iftrue : forall b s1 s2 sigma sigma1,
              b ={ sigma }=> true ->
              s1 -{ sigma }-> sigma1 ->
              (if' b then' s1 else' s2 end') -{ sigma }-> sigma1
| e_iffalse : forall b s1 s2 sigma sigma',
              b ={ sigma }=> false ->
              s2 -{ sigma }-> sigma' ->
              if' b then' s1 else' s2 end' -{ sigma }-> sigma'
| e_whilefalse : forall b s sigma,
    b ={ sigma }=> false ->
    while b s -{ sigma }-> sigma
| e_whiletrue : forall b s sigma sigma',
    b ={ sigma }=> true ->
    (s ;; while b s) -{ sigma }-> sigma' ->
    while b s -{ sigma }-> sigma'
where "s -{ sigma }-> sigma'" := (eval0 s sigma sigma').

Hint Constructors eval0.
Hint Constructors beval.
Hint Constructors aeval.

Example ex_iffalse : exists sigma',  if' (n <=' x) then' (y ::= 7) else' (y ::= 10) end' -{ env1 }-> sigma'.
Proof.
  eexists.
  apply e_iffalse.
  - eapply e_lessthan.
    + apply var.
    + apply var.
    + simpl. reflexivity.
  - eapply e_assignment; eauto.
Qed.


Example ex_iftrue : exists sigma',  if' (x <=' n) then' (y ::= 7) else' (y ::= 10) end' -{ env1 }-> sigma'.
Proof.
  eexists.
  apply e_iftrue.
  - eapply e_lessthan.
    + apply var.
    + apply var.
    + simpl. reflexivity.
  - eapply e_assignment; eauto.
Qed.
