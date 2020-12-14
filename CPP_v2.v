(* Librarii pentru string-uri *)
Require Import Strings.String.
Local Open Scope string_scope.
Local Open Scope list_scope.
Scheme Equality for string.

(* Librarii pentru int *)
Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition Var := string -> nat.

Inductive ErrorUnsigned :=
  | error_unsigned : ErrorUnsigned
  | num : nat -> ErrorUnsigned.

Inductive ErrorInt :=
  | error_int : ErrorInt
  | integer : Z -> ErrorInt.

Inductive ErrorBool :=
  | error_bool : ErrorBool
  | boolean : bool -> ErrorBool.

Inductive ErrorString :=
  | error_string : ErrorString
  | str : string -> ErrorString.

Coercion num: nat >-> ErrorUnsigned.
Coercion integer: Z >-> ErrorInt.
Coercion boolean: bool >-> ErrorBool.
Coercion str: string >-> ErrorString.

(* Expresii aritmetice *)
Inductive AExp :=
  | avar: ErrorString -> AExp
  | anum: ErrorUnsigned -> AExp
  | aint: ErrorInt -> AExp
  | aplus: AExp -> AExp -> AExp
  | aminus: AExp -> AExp -> AExp
  | amul: AExp -> AExp -> AExp
  | adiv: AExp -> AExp -> AExp
  | amod: AExp -> AExp -> AExp.

Coercion anum: ErrorUnsigned >-> AExp.
Coercion aint: ErrorInt >-> AExp.
Coercion avar: ErrorString >-> AExp.

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
  | berror
  | btrue
  | bfalse
  | bvar: string -> BExp
  | blt : AExp -> AExp -> BExp
  | bgt : AExp -> AExp -> BExp
  | bleq : AExp -> AExp -> BExp
  | bgeq : AExp -> AExp -> BExp
  | bnot : BExp -> BExp
  | band : BExp -> BExp -> BExp
  | bor : BExp -> BExp -> BExp.

Coercion bvar: string >-> BExp.

Notation "!' A" := (bnot A) (at level 70, no associativity).
Notation "A <' B" := (blt A B) (at level 70, no associativity).
Notation "A >' B" := (bgt A B) (at level 70, no associativity).
Notation "A <=' B" := (bleq A B) (at level 70, no associativity).
Notation "A >=' B" := (bgeq A B) (at level 70, no associativity).
Notation "A '&&'' B" := (band A B) (at level 40, left associativity).
Notation "A '||'' B" := (bor A B) (at level 40, left associativity).

Check btrue.
Check bfalse.
Check (!' "x").
Check ("x" <' "y").
Check ("x" >' "y").
Check ("x" <=' "y").
Check ("x" >=' "y").
Check ("x" &&' "y").
Check ("x" ||' "y").

(* Expresii cu string-uri *)
Inductive StrExp := (* operatii cu string-uri *)
  | String : ErrorString -> StrExp
  | concat : ErrorString -> ErrorString -> StrExp
  | cmp : ErrorString -> ErrorString -> StrExp
  | length : ErrorString -> StrExp.

Coercion String: ErrorString >-> StrExp.

Notation " A +s B " := (concat A B) (at level 54).
Notation "'strcmp' ( A , B )" := (cmp A B) (at level 56).
Notation "'strlen' ( A )" := (length A) (at level 58).

Check ("abc" +s "abc").
Check (strcmp ( "abc" , "abc" )).
Check (strlen ( "abc" )).

(* Librarii pentru liste *)
Require Import Coq.Lists.List.
Import ListNotations.
Scheme Equality for list.

Print Coq.Lists.List.

(* In Stmt se afla declararile pentru tipuri de date: unsigned, bool, int, string *)
Inductive Stmt :=
  | unsigned_decl : string -> Stmt (* tipul unsigned *)
  | bool_decl : string -> Stmt (* tipul bool *)
  | int_decl : string -> Stmt (* tipul int *)
  | string_decl : string -> Stmt (* tipul string *)
  | unsigned_assign : string -> AExp -> Stmt
  | int_assign : string -> AExp -> Stmt
  | bool_assign : string -> BExp -> Stmt
  | string_assign : string -> AExp -> Stmt
  | sequence : Stmt -> Stmt -> Stmt
  | while : BExp -> Stmt -> Stmt
  | ifthenelse : BExp -> Stmt -> Stmt -> Stmt
  | ifthen : BExp -> Stmt -> Stmt
  | Struct : string -> Stmt -> Stmt (* struct-uri *)
  | funct_decl : string -> Stmt -> Stmt -> Stmt (* declarare functii *)
  | funct_call : string -> list Z -> Stmt (* apelare functii *)
  | switch1 : AExp -> list Case -> Stmt
  with Case :=
  | case1 : AExp -> Stmt -> Case
  | default1 : Stmt -> Case.

Notation "X :u= A" := (unsigned_assign X A)(at level 90).
Notation "X :i= A" := (int_assign X A)(at level 90).
Notation "X :b= A" := (bool_assign X A)(at level 90).
Notation "X :s= A" := (string_assign X A)(at level 90).
Notation "'unsigned' X" := (unsigned_decl X)(at level 90).
Notation "'int' X" := (int_decl X )(at level 90).
Notation "'Bool' X" := (bool_decl X )(at level 90).
Notation "'string'' X" := (int_decl X )(at level 90).
Notation "S1 ;; S2" := (sequence S1 S2) (at level 93, right associativity).
Notation "'if'' B 'then'' S1 'end''" := (ifthen B S1) (at level 97).
Notation "'if'' B 'then'' S1 'else'' S2 'end''" := (ifthenelse B S1 S2) (at level 97).
Notation "'while'' ( B ) { S }" := (while B S) (at level 97).
Notation "'for'' ( A ? B ? C ) { S } 'end''" := (A ;; while B ( S ;; C )) (at level 97).
Notation "'struct' X 'inceput' S 'sfarsit'" := (Struct X S) (at level 88, no associativity).
Notation " 'decl' X 'inceput' S1 'sfarsit' { S2 } " := (funct_decl X S1 S2) (at level 88, no associativity).
Notation " 'call' X 'inceput' L 'sfarsit' " := (funct_call X L) (at level 30, no associativity).
Notation " 'switch' A 'sf' L 'sfarsit' " := (switch1 A L) (at level 97).
Notation " 'case'  A 'sf' S 'sf' " := (case1 A S) (at level 99).
Notation " 'default'' S 'sf' " := (default1 S) (at level 99).

Check ( int "x1").
Check ( unsigned "x1" ;;
        "x1" :u= 3).
Check ( Bool "b" ;;
        "b" :b= btrue ;;
        int "x" ;;
        int "y" ;;
        unsigned "d" ;;
        int "i" ;;
        int "sum" ;;
        "x" :i= 2 ;;
        "y" :i= 3 ;;
        "d" :u= 0 ;;
        "sum" :i= 0 ;;
        if' ( "x" <=' "y" ) then'
          "d" :u= ("y" -' "x")
        else'
          "d" :u= ("x" -' "y")
        end' ;;
        if' ( "x" <=' "y" ) then'
          "d" :u= ("y" -' "x")
        end' ;;
        for' ( ("i" :i= 0) ? ("i" <=' "d") ? ("i" :i= "i" +'1)) {
            "sum" :i= ("sum" +' 1)
        } end' ;;
        "i" :i= 0 ;;
        while' ( "i" <=' "d" ) {
          "sum" :i= ("sum" +' 1)
        }).
Check ( decl "fun" inceput int "x" sfarsit {
        int "s" ;;
        "s" :i= ("x" +' 2)
        } ).
Check ( struct "nume" inceput
          int "x" ;;
          int "y"
        sfarsit ).
Check ( call "fun" inceput [2;3]  sfarsit ).
Check ( switch "x" +' "y" sf [
          case  7 sf "z" :i= 7 sf ;
          case 10 sf "z" :i= 10 sf ;
          default' "z" :i= 0 sf ] sfarsit  ).


Inductive Result :=
  | err_undecl : Result
  | err_assign : Result
  | default : Result
  | res_unsigned : ErrorUnsigned -> Result
  | res_int : ErrorInt -> Result
  | res_string : ErrorString -> Result
  | res_bool : ErrorBool -> Result.

Scheme Equality for Result.

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
  | res_int x => match t2 with
                   | res_int x  => true
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
  end.
