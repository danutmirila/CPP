(* Librarii pentru string-uri *)
Require Import Strings.String.
Local Open Scope string_scope.
Local Open Scope list_scope.
Scheme Equality for string.

Inductive ErrorUnsigned :=
  | error_unsigned : ErrorUnsigned
  | num : nat -> ErrorUnsigned.

Inductive ErrorBool :=
  | error_bool : ErrorBool
  | boolean : bool -> ErrorBool.

Inductive ErrorString :=
  | error_string : ErrorString
  | str : string -> ErrorString.

Coercion num: nat >-> ErrorUnsigned.
Coercion boolean: bool >-> ErrorBool.
Coercion str: string >-> ErrorString.

(* Expresii aritmetice *)
Inductive AExp :=
  | avar: string -> AExp
  | anum: ErrorUnsigned -> AExp
  | aplus: AExp -> AExp -> AExp
  | aminus: AExp -> AExp -> AExp
  | amul: AExp -> AExp -> AExp
  | adiv: AExp -> AExp -> AExp
  | amod: AExp -> AExp -> AExp.

Coercion anum: ErrorUnsigned >-> AExp.
Coercion avar: string >-> AExp.

Notation "A +' B" := (aplus A B) (at level 50, left associativity).
Notation "A -' B" := (aminus A B) (at level 50, left associativity).
Notation "A *' B" := (amul A B) (at level 40, left associativity).
Notation "A /' B" := (adiv A B) (at level 40, left associativity).
Notation "A %' B" := (amod A B) (at level 40, left associativity).

Check ("x" +' "y").
Check ("x" -' "y").
Check ("x" *' "y").
Check ("x" /' "y").
Check ("x" %' "y").

(* Expresii booleene *)
Inductive BExp :=
  | berror : ErrorBool -> BExp
  | bvar: string -> BExp
  | beq : AExp -> AExp -> BExp
  | blt : AExp -> AExp -> BExp
  | bgt : AExp -> AExp -> BExp
  | bleq : AExp -> AExp -> BExp
  | bgeq : AExp -> AExp -> BExp
  | bnot : BExp -> BExp
  | band : BExp -> BExp -> BExp
  | bor : BExp -> BExp -> BExp.

Coercion berror : ErrorBool >-> BExp.
Coercion bvar: string >-> BExp.

Notation "!' A" := (bnot A) (at level 70, no associativity).
Notation "A ==' B" := (beq A B) (at level 70, no associativity).
Notation "A <' B" := (blt A B) (at level 70, no associativity).
Notation "A >' B" := (bgt A B) (at level 70, no associativity).
Notation "A <=' B" := (bleq A B) (at level 70, no associativity).
Notation "A >=' B" := (bgeq A B) (at level 70, no associativity).
Notation "A '&&'' B" := (band A B) (at level 40, left associativity).
Notation "A '||'' B" := (bor A B) (at level 40, left associativity).

Check (!' "x").
Check ("x" <' "y").
Check ("x" >' "y").
Check ("x" <=' "y").
Check ("x" >=' "y").
Check ("x" &&' "y").
Check ("x" ||' "y").

(* Expresii cu string-uri *)
Inductive StrExp := (* operatii cu string-uri *)
  | sir_vid : StrExp
  | strings : ErrorString -> StrExp.

Coercion strings : ErrorString >-> StrExp.

Scheme Equality for StrExp.

Definition cmp (str1 str2 : StrExp) : BExp :=
  match str1, str2 with
  | sir_vid, sir_vid => true
  | sir1, sir2 => if(StrExp_beq sir1 sir2) then true
                  else false
  end.

Definition lungime (str : StrExp) : nat :=
  match str with
  | sir_vid => 0
  | strings s => match s with
                  | error_string => 0
                  | str s' => length s'
                 end
  end.

Definition concat (str1 str2 : StrExp) : StrExp :=
  match str1, str2 with
  | sir_vid, _ => str2
  | _, sir_vid => str1
  | strings s1, strings s2 => match s1, s2 with
                              | error_string, _ => error_string
                              | _, error_string => error_string
                              | str s1', str s2' => append s1' s2'
                              end
  end.

Notation " A +s B " := (concat A B) (at level 54).
Notation "'strcmp' ( A , B )" := (cmp A B) (at level 56).
Notation "'strlen' ( A )" := (lungime A) (at level 58).

Check ("abc" +s "abc").
Compute ("abc" +s "abc").
Check (strcmp ( "abc" , "abc" )).
Compute (strcmp ( "abc" , "abc" )).
Check (strlen ("abc")).
Compute (cmp "123" "13").
Compute (cmp "123" "123").
Compute (strlen ("123") + 3).

(* In Stmt se afla declararile pentru tipuri de date: unsigned, bool, string *)
Inductive Stmt :=
  | stmt_null : Stmt
  | unsigned_decl : string -> Stmt (* tipul unsigned *)
  | bool_decl : string -> Stmt (* tipul bool *)
  | string_decl : string -> Stmt (* tipul string *)
  | unsigned_assign : string -> AExp -> Stmt
  | bool_assign : string -> BExp -> Stmt
  | string_assign : string -> StrExp -> Stmt
  | sequence : Stmt -> Stmt -> Stmt
  | while : BExp -> Stmt -> Stmt
  | ifthenelse : BExp -> Stmt -> Stmt -> Stmt
  | ifthen : BExp -> Stmt -> Stmt
  | Struct : string -> Stmt -> Stmt (* struct-uri *)
  | funct_decl : string -> Stmt -> Stmt (* declarare functii *)
  | funct_call : string -> Stmt (* apelare functii *)
  | switch1 : AExp -> AExp -> Stmt -> AExp -> Stmt -> Stmt -> Stmt.

Notation "X :u= A" := (unsigned_assign X A)(at level 90).
Notation "X :b= A" := (bool_assign X A)(at level 90).
Notation "X :s= A" := (string_assign X A)(at level 90).
Notation "'unsigned' X" := (unsigned_decl X)(at level 90).
Notation "'Bool' X" := (bool_decl X )(at level 90).
Notation "'string'' X" := (string_decl X )(at level 90).
Notation "S1 ;; S2" := (sequence S1 S2) (at level 93, right associativity).
Notation "'if'' B 'then'' S1 'end''" := (ifthen B S1) (at level 97).
Notation "'if'' B 'then'' S1 'else'' S2 'end''" := (ifthenelse B S1 S2) (at level 97).
Notation "'while'' B 'sf' 'inceput' S 'sfarsit'" := (while B S) (at level 97).
Notation "'struct' X 'inceput' S 'sfarsit'" := (Struct X S) (at level 88, no associativity).
Notation " 'decl' X 'inceput' S 'sfarsit' " := (funct_decl X S) (at level 88, no associativity).
Notation " 'call' X 'endcall' " := (funct_call X) (at level 30, no associativity).
Notation " 'switch' A 'inceput' 'case' a1 'sf' s1 'sfarsit' 'case' a2 'sf' s2 'sfarsit' 'default' s3 'sfarsit' " := (switch1 A a1 s1 a2 s2 s3) (at level 97).

Check ( unsigned "x1").
Check ( unsigned "x1" ;;
        "x1" :u= 3).
Check ( Bool "b" ;;
        "b" :b= true ;;
        unsigned "x" ;;
        unsigned "y" ;;
        unsigned "d" ;;
        unsigned "i" ;;
        unsigned "sum" ;;
        "x" :u= 2 ;;
        "y" :u= 3 ;;
        "d" :u= 0 ;;
        "sum" :u= 0 ;;
        if' ( "x" <=' "y" ) then'
          "d" :u= ("y" -' "x")
        else'
          "d" :u= ("x" -' "y")
        end' ;;
        if' ( "x" <=' "y" ) then'
          "d" :u= ("y" -' "x")
        end' ;;
        "i" :u= 0 ;;
        while' "i" <=' "d" sf inceput
          "sum" :u= ("sum" +' 1)
        sfarsit).
Check ( decl "fun" inceput
        unsigned "s" ;;
        "s" :u= ("x" +' 2)
        sfarsit ).
Check ( struct "nume" inceput
          unsigned "x" ;;
          unsigned "y"
        sfarsit ).
Check ( call "fun" endcall ).
Check ( switch "x" +' "y" inceput
          case 7 sf "z" :u= 7 sfarsit
          case 10 sf "z" :u= 10 sfarsit
          default "z" :u= 0 sfarsit  ).


Inductive Result :=
  | err_undecl : Result
  | err_assign : Result
  | default : Result
  | res_unsigned : ErrorUnsigned -> Result
  | res_string : ErrorString -> Result
  | res_bool : ErrorBool -> Result
  | code : Stmt -> Result.

Coercion res_unsigned : ErrorUnsigned >-> Result.

Definition check_eq_over_types (t1 : Result)(t2 : Result) : bool :=
  match t1 with
  | err_undecl => match t2 with 
                   | err_undecl => true
                   | _ => false
                   end
  | err_assign => match t2 with 
                   | err_assign => true
                   | _ => false
                   end
  | default => match t2 with 
                   | default => true
                   | _ => false
                   end
  | res_unsigned x => match t2 with
                   | res_unsigned x  => true
                   | _ => false
                  end
  | res_string x => match t2 with
                   | res_string x => true
                   | _ => false
                   end
  | res_bool x => match t2 with 
                   | res_bool x => true
                   | _ => false
                   end
  | code x => match t2 with
                | code x => true
                | _ => false
              end
  end.

Definition Env := string -> Result.

Definition update (env : Env) (x : string) (v : Result) : Env :=
  fun y =>
    if (eqb y x)
    then
      if (check_eq_over_types err_undecl (env y))
      then v
      else
        if (andb (check_eq_over_types err_undecl (env y)) (negb (check_eq_over_types default v)))
        then err_undecl
        else
          if (andb (check_eq_over_types err_undecl (env y)) (check_eq_over_types default v))
          then default
          else
            if (orb (check_eq_over_types default (env y)) (check_eq_over_types v (env y)))
            then v
            else err_assign
    else (env y).

Notation "S [ V 'up' X ]" := (update S X V) (at level 0).

Definition env0 : Env := fun n => err_undecl.
Definition env1 : Env := 
  fun n => 
    if (string_beq n "x" )
    then res_unsigned 2
    else if (string_beq n "n")
         then res_unsigned 3
         else if (string_beq n "z")
              then res_unsigned 4
              else if (string_beq n "f")
                   then code (unsigned "ab")
                   else err_undecl.

Compute (env0 "x").
Compute (env1 "x").
Compute (env1 "f").

Compute (update (update env0 "x" (default)) "x" 1) "x".

(* Semantica expresii aritmetice *)
Definition plus_ErrorUnsigned (n1 n2 : ErrorUnsigned) : ErrorUnsigned :=
  match n1, n2 with
    | error_unsigned, _ => error_unsigned
    | _, error_unsigned => error_unsigned
    | num v1, num v2 => num (v1 + v2)
    end.

Definition minus_ErrorUnsigned (n1 n2 : ErrorUnsigned) : ErrorUnsigned :=
  match n1, n2 with
    | error_unsigned, _ => error_unsigned
    | _, error_unsigned => error_unsigned
    | num n1, num n2 => if Nat.ltb n1 n2
                        then error_unsigned
                        else num (n1 - n2)
    end.

Definition mul_ErrorUnsigned (n1 n2 : ErrorUnsigned) : ErrorUnsigned :=
  match n1, n2 with
    | error_unsigned, _ => error_unsigned
    | _, error_unsigned => error_unsigned
    | num v1, num v2 => num (v1 * v2)
    end.

Definition div_ErrorUnsigned (n1 n2 : ErrorUnsigned) : ErrorUnsigned :=
  match n1, n2 with
    |error_unsigned, _ => error_unsigned
    | _, error_unsigned => error_unsigned
    | _, num 0 => error_unsigned
    | num v1, num v2 => num (Nat.div v1 v2)
    end.

Definition mod_ErrorUnsigned (n1 n2 : ErrorUnsigned) : ErrorUnsigned :=
  match n1, n2 with
    | error_unsigned, _ => error_unsigned
    | _, error_unsigned => error_unsigned
    | _, num 0 => error_unsigned
    | num v1, num v2 => num (v1 - v2 * (Nat.div v1 v2))
    end.

Fixpoint aeval_fun (a : AExp) (sigma : Env) : ErrorUnsigned :=
  match a with
  | anum n => match n with
              | error_unsigned => error_unsigned
              | num n' => n'
              end
  | avar v => match (sigma v) with
              | res_unsigned y => match y with
                                  | error_unsigned => error_unsigned
                                  | num y' => y'
                                  end
              | _ => error_unsigned
              end
  | a1 +' a2 => plus_ErrorUnsigned (aeval_fun a1 sigma) (aeval_fun a2 sigma)
  | a1 -' a2 => minus_ErrorUnsigned (aeval_fun a1 sigma) (aeval_fun a2 sigma)
  | a1 *' a2 => mul_ErrorUnsigned (aeval_fun a1 sigma) (aeval_fun a2 sigma)
  | a1 /' a2 => div_ErrorUnsigned (aeval_fun a1 sigma) (aeval_fun a2 sigma)
  | a1 %' a2 => mod_ErrorUnsigned (aeval_fun a1 sigma) (aeval_fun a2 sigma)
  end.

Compute aeval_fun (3 +' 3 *' 3) env0.
Compute aeval_fun (3 +' "x") env1.

(* Semantica Big-Step pentru expresii aritmetice *)
Reserved Notation "A =[ S ]=> U" (at level 30).

Inductive aeval : AExp -> Env -> ErrorUnsigned -> Prop :=
| const : forall n sigma , anum n =[ sigma ]=> n (* <n,sigma> => <n> *) 
| var : forall v sigma ,avar v =[ sigma ]=> match (sigma v) with
                                            | res_unsigned y => match y with
                                                                | error_unsigned => error_unsigned
                                                                | num y' => y'
                                                                end
                                            | _ => error_unsigned
                                            end
| plus : forall a1 a2 i1 i2 sigma n,
    a1 =[ sigma ]=> i1 ->
    a2 =[ sigma ]=> i2 ->
    n = (plus_ErrorUnsigned i1 i2) ->
    (a1 +' a2) =[ sigma ]=> n
| minus: forall a1 a2 i1 i2 sigma n,
    a1 =[ sigma ]=> i1 ->
    a2 =[ sigma ]=> i2 ->
    n = (minus_ErrorUnsigned i1 i2) ->
    (a1 -' a2) =[ sigma ]=> n
| mul : forall a1 a2 i1 i2 sigma n,
    a1 =[ sigma ]=> i1 ->
    a2 =[ sigma ]=> i2 ->
    n = (mul_ErrorUnsigned i1 i2) ->
    (a1 *' a2) =[ sigma ]=> n
| div : forall a1 a2 i1 i2 sigma n,
    a1 =[ sigma ]=> i1 ->
    a2 =[ sigma ]=> i2 ->
    n = (div_ErrorUnsigned i1 i2) ->
    (a1 /' a2) =[ sigma ]=> n
| modulo : forall a1 a2 i1 i2 sigma n,
    a1 =[ sigma ]=> i1 ->
    a2 =[ sigma ]=> i2 ->
    n = (mod_ErrorUnsigned i1 i2) ->
    (a1 %' a2) =[sigma]=> n
where "a =[ sigma ]=> n" := (aeval a sigma n).

(* Exemple pentru expresiile aritmetice *)
Require Import Omega.

Example ex_plus : (12 +' "x") =[ env1 ]=> 14.
Proof.
  eapply plus.
  - apply const.
  - apply var.
  - simpl. reflexivity.
Qed.

Example ex_minus : (12 -' "x") =[ env1 ]=> 10.
Proof.
  eapply minus.
  - apply const.
  - apply var.
  - simpl. reflexivity.
Qed.

Example ex_minus_error : (12 -' 13) =[ env1 ]=> error_unsigned.
Proof.
  eapply minus.
  - apply const.
  - apply const.
  - simpl. reflexivity.
Qed.

Example ex_mul : (6 *' "x") =[ env1 ]=> 12.
Proof.
  eapply mul.
  - apply const.
  - apply var.
  - simpl. reflexivity.
Qed.

Example ex_div : (6 /' "x") =[ env1 ]=> 3.
Proof.
  eapply div.
  - apply const.
  - apply var.
  - simpl. reflexivity.
Qed.

Example ex_div_error : (6 /' 0) =[ env1 ]=> error_unsigned.
Proof.
  eapply div.
  - apply const.
  - apply const.
  - simpl. reflexivity.
Qed.

Example ex_modulo : (7 %' 5) =[ env1 ]=>2.
Proof.
  eapply modulo.
  - apply const.
  - apply const.
  - simpl. reflexivity.
Qed.

(* Semantica expresii booleene *)
Definition beq_ErrorBool (n1 n2 : ErrorUnsigned) : ErrorBool :=
  match n1, n2 with
    | error_unsigned, _ => error_bool
    | _, error_unsigned => error_bool
    | num v1, num v2 => Nat.eqb v1 v2
    end.

Definition blt_ErrorBool (n1 n2 : ErrorUnsigned) : ErrorBool :=
  match n1, n2 with
    | error_unsigned, _ => error_bool
    | _, error_unsigned => error_bool
    | num v1, num v2 => Nat.ltb v1 v2
    end.

Definition bleq_ErrorBool (n1 n2 : ErrorUnsigned) : ErrorBool :=
  match n1, n2 with
    | error_unsigned, _ => error_bool
    | _, error_unsigned => error_bool
    | num v1, num v2 => Nat.leb v1 v2
    end.

Definition bgt_ErrorBool (n1 n2 : ErrorUnsigned) : ErrorBool :=
  match n1, n2 with
    | error_unsigned, _ => error_bool
    | _, error_unsigned => error_bool
    | num v1, num v2 => negb (Nat.leb v1 v2)
    end.

Definition bgeq_ErrorBool (n1 n2 : ErrorUnsigned) : ErrorBool :=
  match n1, n2 with
    | error_unsigned, _ => error_bool
    | _, error_unsigned => error_bool
    | num v1, num v2 => negb (Nat.ltb v1 v2)
    end.

Definition not_ErrorBool (n : ErrorBool) : ErrorBool :=
  match n with
    | error_bool => error_bool
    | boolean v => negb v
    end.

Definition and_ErrorBool (n1 n2 : ErrorBool) : ErrorBool :=
  match n1, n2 with
    | error_bool, _ => error_bool
    | _, error_bool => error_bool
    | boolean v1, boolean v2 => boolean (andb v1 v2)
    end.

Definition or_ErrorBool (n1 n2 : ErrorBool) : ErrorBool :=
  match n1, n2 with
    | error_bool, _ => error_bool
    | _, error_bool => error_bool
    | boolean v1, boolean v2 => boolean (orb v1 v2)
    end.

Compute (beq_ErrorBool 1 1).
Compute (blt_ErrorBool 1 5).
Compute (bleq_ErrorBool 2 2).
Compute (bgt_ErrorBool 2 2).
Compute (bgeq_ErrorBool 2 2).
Compute and_ErrorBool (not_ErrorBool (blt_ErrorBool 2 5)) true.
Compute or_ErrorBool (not_ErrorBool (blt_ErrorBool 2 5)) true.

Fixpoint beval_fun (b : BExp) (sigma : Env) : ErrorBool :=
  match b with
  | berror x => match x with
                | error_bool => error_bool
                | boolean x' => x'
                end
  | bvar v => match (sigma v) with
              | res_bool y => match y with
                                  | error_bool => error_bool
                                  | boolean y' => y'
                                  end
              | _ => error_bool
              end
  | beq a1 a2 => (beq_ErrorBool (aeval_fun a1 sigma) (aeval_fun a2 sigma))
  | blt a1 a2 => (blt_ErrorBool (aeval_fun a1 sigma) (aeval_fun a2 sigma))
  | bleq a1 a2 => (bleq_ErrorBool (aeval_fun a1 sigma) (aeval_fun a2 sigma))
  | bgt a1 a2 => (bgt_ErrorBool (aeval_fun a1 sigma) (aeval_fun a2 sigma))
  | bgeq a1 a2 => (bgeq_ErrorBool (aeval_fun a1 sigma) (aeval_fun a2 sigma))
  | bnot b => (not_ErrorBool (beval_fun b sigma))
  | band b1 b2 => (and_ErrorBool (beval_fun b1 sigma) (beval_fun b2 sigma))
  | bor b1 b2 => (or_ErrorBool (beval_fun b1 sigma) (beval_fun b2 sigma))
  end.

Compute (beval_fun true env0).
Compute (beval_fun (true &&' false) env0).
Compute (beval_fun ((1 <=' 10) &&' (!' (("x" +' 1) <=' 2))) env1 ).
Compute (beval_fun ((1 >=' 10) ||' (!' (("x" +' 1) <=' 2))) env1 ).

(* Semantica Big-Step pentru expresii aritmetice *)
Reserved Notation "B ={ S }=> B'" (at level 20).

Inductive beval : BExp -> Env -> ErrorBool -> Prop :=
| b_error: forall x sigma, berror x ={ sigma }=> match x with
                                      | error_bool => error_bool
                                      | boolean x' => x'
                                      end
| b_var : forall v sigma, bvar v  ={ sigma }=>  match (sigma v) with
                                                | res_bool y => match y with
                                                                | error_bool => error_bool
                                                                | boolean y' => y'
                                                                end
                                                | _ => error_bool
                                                end
| b_eq : forall a1 a2 i1 i2 sigma b,
    a1 =[ sigma ]=> i1 ->
    a2 =[ sigma ]=> i2 ->
    b = (beq_ErrorBool i1 i2) ->
    (a1 ==' a2) ={ sigma }=> b
| b_lt : forall a1 a2 i1 i2 sigma b,
    a1 =[ sigma ]=> i1 ->
    a2 =[ sigma ]=> i2 ->
    b = (blt_ErrorBool i1 i2) ->
    (a1 <' a2) ={ sigma }=> b
| b_leq : forall a1 a2 i1 i2 sigma b,
    a1 =[ sigma ]=> i1 ->
    a2 =[ sigma ]=> i2 ->
    b = (bleq_ErrorBool i1 i2) ->
    (a1 <=' a2) ={ sigma }=> b
| b_gt : forall a1 a2 i1 i2 sigma b,
    a1 =[ sigma ]=> i1 ->
    a2 =[ sigma ]=> i2 ->
    b = (bgt_ErrorBool i1 i2) ->
    (a1 >' a2) ={ sigma }=> b
| b_geq : forall a1 a2 i1 i2 sigma b,
    a1 =[ sigma ]=> i1 ->
    a2 =[ sigma ]=> i2 ->
    b = (bgeq_ErrorBool i1 i2) ->
    (a1 >=' a2) ={ sigma }=> b
| b_not : forall a1 i1 sigma b,
    a1 ={ sigma }=> i1 ->
    b = (not_ErrorBool i1) ->
    (!' a1) ={ sigma }=> b
| b_and : forall a1 a2 i1 i2 sigma b,
    a1 ={ sigma }=> i1 ->
    a2 ={ sigma }=> i2 ->
    b = (and_ErrorBool i1 i2) ->
    (a1 &&' a2) ={ sigma }=>  b
| b_or : forall a1 a2 i1 i2 sigma b,
    a1 ={ sigma }=> i1 ->
    a2 ={ sigma }=> i2 ->
    b = (or_ErrorBool i1 i2) ->
    (a1 ||' a2) ={ sigma }=>  b 
where "B ={ S }=> B'" := (beval B S B').

(* Exemple pentru expresii booleene *)
Example ex1 : (("x" *' 3) <=' 2) ={ env1 }=> false.
Proof.
  eapply b_leq.
  - eapply mul.
    * apply var.
    * apply const.
    * simpl. reflexivity.
  - apply const.
  - simpl. reflexivity.
Qed.

Example ex2 : (("x" *' 3) >=' 2) ={ env1 }=> true.
Proof.
  eapply b_geq.
  - eapply mul.
    * apply var.
    * apply const.
    * simpl. reflexivity.
  - apply const.
  - simpl. reflexivity.
Qed.

Example ex3 : (!' (("x" *' 3) >=' 2)) ={ env1 }=> false.
Proof.
  eapply b_not.
    - eapply b_geq.
      -- eapply mul.
        * apply var.
        * apply const.
        * simpl. reflexivity.
      -- apply const.
      -- simpl. reflexivity.
    - simpl. reflexivity.
Qed.

Example ex4 : (((("x" *' 3) >=' 2) &&' true) ||' (("x" +' 3) <' 2)) ={ env1 }=> true.
Proof.
  eapply b_or.
  - eapply b_and.
    -- eapply b_geq.
      --- eapply mul.
          ---- apply var.
          ---- apply const.
          ---- simpl. reflexivity.
      --- apply const.
      --- simpl. reflexivity.
    -- apply b_error.
    -- simpl. reflexivity.
  - eapply b_lt.
    -- eapply plus.
      --- apply var.
      --- apply const.
      --- simpl. reflexivity.
    -- apply const.
    -- simpl. reflexivity.
  - simpl. reflexivity.
Qed.

Example ex5 : (((("x" *' 3) >=' 2) &&' true) ||' (("y" +' 3) <' 2)) ={ env1 }=> error_bool. (* "y" nu este declarat in env1, deci o sa fie returnat error_bool *)
Proof.
  eapply b_or.
  - eapply b_and.
    -- eapply b_geq.
      --- eapply mul.
          ---- apply var.
          ---- apply const.
          ---- simpl. reflexivity.
      --- apply const.
      --- simpl. reflexivity.
    -- apply b_error.
    -- simpl. reflexivity.
  - eapply b_lt.
    -- eapply plus.
      --- apply var.
      --- apply const.
      --- simpl. reflexivity.
    -- apply const.
    -- simpl. reflexivity.
  - simpl. reflexivity.
Qed.

Compute (beval_fun (!' (1 ==' 1)) env0).

Reserved Notation "S -{ Sigma }-> Sigma'" (at level 60).
Inductive eval : Stmt -> Env -> Env -> Prop :=
| e_decl_unsigned : forall sigma sigma' x,
    sigma' = (update sigma x (default)) ->
    (unsigned x) -{ sigma }-> sigma'
| e_assignment_unsigned: forall a i x sigma sigma',
    a =[ sigma ]=> i ->
    sigma' = (update sigma x (res_unsigned i)) ->
    (x :u= a) -{ sigma }-> sigma'
| e_decl_bool : forall sigma sigma' x,
    sigma' = (update sigma x (default)) ->
    (Bool x) -{ sigma }-> sigma'
| e_assignment_bool: forall a i x sigma sigma',
    a ={ sigma }=> i ->
    sigma' = (update sigma x (res_bool i)) ->
    (x :b= a) -{ sigma }-> sigma'
(*| e_decl_string : forall sigma sigma' x,
    sigma' = (update sigma x (default)) ->
    (string' x) -{ sigma }-> sigma'
| e_assignment_string: forall a i x sigma sigma',
    a =[ sigma ]=> i ->
    sigma' = (update sigma x (res_string i)) ->
    (x :s= a) -{ sigma }-> sigma'*)
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
| e_struct : forall X s1 s2 sigma sigma',
    (s1 ;; s2) -{ sigma }-> sigma' ->
    (Struct X (s1 ;; s2)) -{ sigma }-> sigma'
| e_funct_decl : forall sigma sigma' nume s,
    sigma' = update sigma nume (code s) ->
    (funct_decl nume s) -{ sigma }-> sigma'
| e_funct_call : forall s X sigma sigma',
    s = match (sigma X) with
        | code y => y
        | _ => stmt_null
        end ->
    s -{ sigma }-> sigma' ->
    (funct_call X) -{ sigma }-> sigma'
  | e_switch_case1 : forall A a sigma sigma' a1 s1 a2 s2 s3,
    A =[ sigma ]=> a ->
    (a ==' a1) ={ sigma }=> true ->
    s1 -{ sigma }-> sigma' ->
    (switch1 A a1 s1 a2 s2 s3) -{ sigma }-> sigma'
  | e_switch_case2 : forall A a sigma sigma' a1 s1 a2 s2 s3,
    A =[ sigma ]=> a ->
    (a ==' a2) ={ sigma }=> true ->
    s2 -{ sigma }-> sigma' ->
    (switch1 A a1 s1 a2 s2 s3) -{ sigma }-> sigma'
  | e_switch_default : forall A a sigma sigma' a1 s1 a2 s2 s3,
    A =[ sigma ]=> a ->
    (a ==' a1) ={ sigma }=> false ->
    (a ==' a2) ={ sigma }=> false ->
    s3 -{ sigma }-> sigma' ->
    (switch1 A a1 s1 a2 s2 s3) -{ sigma }-> sigma'
where "s -{ sigma }-> sigma'" := (eval s sigma sigma').

Example ex_bool : exists sigma',
  (Bool "b" ;;
  "b" :b= true) -{ env0 }-> sigma'.
Proof.
  eexists.
  eapply e_seq.
  - eapply e_decl_bool. reflexivity.
  - eapply e_assignment_bool.
    -- apply b_error.
    -- reflexivity.
Qed.

Example ex_iftrue : exists sigma',  if' ("x" <=' "n") then' ("z" :u= 7) else' ("z" :u= 10) end' -{ env1 }-> sigma'.
Proof.
  eexists.
  apply e_iftrue.
  - eapply b_leq.
    -- apply var.
    -- apply var.
    -- simpl. reflexivity.
  - eapply e_assignment_unsigned; eauto.
    -- apply const.
Qed.

Example ex_iffalse : exists sigma',  if' ("x" >=' "n") then' ("z" :u= 7) else' ("z" :u= 10) end' -{ env1 }-> sigma'.
Proof.
  eexists.
  apply e_iffalse.
  - eapply b_geq.
    -- apply var.
    -- apply var.
    -- simpl. reflexivity.
  - eapply e_assignment_unsigned; eauto.
    -- apply const.
Qed.

Example ex_decl_assign_while : exists sigma',
  (unsigned "sum" ;;
  "sum" :u= 0 ;;
  while' "x" <' "n" sf inceput
    "sum" :u= "sum" +' 1 ;;
    "x" :u= "x" +' 1
  sfarsit) -{ env1 }-> sigma'.
Proof.
  eexists.
  eapply e_seq.
  - eapply e_decl_unsigned. reflexivity.
  - eapply e_seq.
    -- eapply e_assignment_unsigned. 
       apply const. reflexivity.
    -- eapply e_whiletrue.
      --- eapply b_lt.
        ---- apply var.
        ---- apply var.
        ---- simpl. reflexivity.
      --- eapply e_seq.
        ---- eapply e_seq.
          ----- eapply e_assignment_unsigned.
            ------ eapply plus. apply var. apply const. simpl. reflexivity.
            ------ reflexivity.
          ----- eapply e_assignment_unsigned.
            ------ eapply plus. apply var. apply const. simpl. reflexivity.
            ------ reflexivity.
        ---- eapply e_whilefalse.
            ------ eapply b_lt. apply var. apply var. simpl. reflexivity.
Qed.

Example ex_struct : exists sigma',
  (struct "coordonate" inceput
    unsigned "x" ;;
    unsigned "y" 
  sfarsit) -{ env0 }-> sigma'.
Proof.
  eexists.
  eapply e_struct.
  - eapply e_seq.
    -- apply e_decl_unsigned. reflexivity.
    -- apply e_decl_unsigned. reflexivity.
Qed.

Example ex_funct_decl : exists sigma',
  (decl "f" inceput 
    unsigned "a" ;;
    "a" :u= 10
  sfarsit ;;
  call "f" endcall) -{ env0 }-> sigma'.
Proof.
  eexists.
  eapply e_seq.
    - apply e_funct_decl. reflexivity.
    - eapply e_funct_call.
      -- simpl. reflexivity.
      -- eapply e_seq.
        --- apply e_decl_unsigned. reflexivity.
        --- eapply e_assignment_unsigned.
            ---- apply const.
            ---- reflexivity.
Qed.

Example ex_switch_case1 : exists sigma',
  (unsigned "x" ;;
  "x" :u= 3 ;;
  switch "x" +' 1 inceput
          case 4 sf "x" :u= 7 sfarsit
          case 5 sf "x" :u= 10 sfarsit
          default "x" :u= 0 sfarsit) -{ env0 }-> sigma'.
Proof.
  eexists.
  eapply e_seq.
  - apply e_decl_unsigned. reflexivity.
  - eapply e_seq.
    -- eapply e_assignment_unsigned.
      --- apply const.
      --- reflexivity.
    -- eapply e_switch_case1.
      --- eapply plus.
        ---- apply var.
        ---- apply const.
        ---- simpl. reflexivity.
      --- eapply b_eq.
        ---- apply const.
        ---- apply const.
        ---- simpl. reflexivity.
      --- eapply e_assignment_unsigned.
        ---- apply const.
        ---- reflexivity.
Qed.

Example ex_switch_case2 : exists sigma',
  (unsigned "x" ;;
  "x" :u= 3 ;;
  switch "x" +' 2 inceput
          case 4 sf "x" :u= 7 sfarsit
          case 5 sf "x" :u= 10 sfarsit
          default "x" :u= 0 sfarsit) -{ env0 }-> sigma'.
Proof.
  eexists.
  eapply e_seq.
  - apply e_decl_unsigned. reflexivity.
  - eapply e_seq.
    -- eapply e_assignment_unsigned.
      --- apply const.
      --- reflexivity.
    -- eapply e_switch_case2.
      --- eapply plus.
        ---- apply var.
        ---- apply const.
        ---- simpl. reflexivity.
      --- eapply b_eq.
        ---- apply const.
        ---- apply const.
        ---- simpl. reflexivity.
      --- eapply e_assignment_unsigned.
        ---- apply const.
        ---- reflexivity.
Qed.

Example ex_switch_default : exists sigma',
  (unsigned "x" ;;
  "x" :u= 3 ;;
  switch "x" +' 3 inceput
          case 4 sf "x" :u= 7 sfarsit
          case 5 sf "x" :u= 10 sfarsit
          default "x" :u= 0 sfarsit) -{ env0 }-> sigma'.
Proof.
  eexists.
  eapply e_seq.
  - apply e_decl_unsigned. reflexivity.
  - eapply e_seq.
    -- eapply e_assignment_unsigned.
      --- apply const.
      --- reflexivity.
    -- eapply e_switch_default.
      --- eapply plus.
        ---- apply var.
        ---- apply const.
        ---- simpl. reflexivity.
      --- eapply b_eq.
        ---- apply const.
        ---- apply const.
        ---- simpl. reflexivity.
      --- eapply b_eq.
        ---- apply const.
        ---- apply const.
        ---- simpl. reflexivity.
      --- eapply e_assignment_unsigned.
        ---- apply const.
        ---- reflexivity.
Qed.
