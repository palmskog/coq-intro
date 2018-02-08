Require Import List.
Import ListNotations.
  
Fixpoint alternate (l1 l2 : list nat) : list nat :=
match l1 with
| [] => l2
| h1 :: t1 =>
  match l2 with
  | [] => h1 :: t1
  | h2 :: t2 => h1 :: h2 :: alternate t1 t2
  end
end.

Eval compute in alternate [1] [2].
Eval compute in alternate [1; 3; 5] [2; 4; 6].

Inductive alt : list nat -> list nat -> list nat -> Prop :=
| alt_nil :
    forall l, alt [] l l
| alt_step :
    forall a l t1 t2,
    alt l t1 t2 ->
    alt (a :: t1) l (a :: t2).

Lemma alt_one : alt [] [1] [1].
Proof.
apply alt_nil.
Qed.

Lemma alt_123456 : alt [1; 3; 5] [2; 4; 6] [1; 2; 3; 4; 5; 6].
Proof.
apply alt_step.
apply alt_step.
apply alt_step.
apply alt_step.
apply alt_step.
apply alt_step.
apply alt_nil.
Qed.

Print list_ind.

Lemma alt_alternate : 
  forall l1 l2 l3, alt l1 l2 l3 -> alternate l1 l2 = l3.
Proof.
induction l1; intros.
- inversion H.
  subst.
  simpl.
  reflexivity.
- destruct l2; simpl.
  * inversion H.
    inversion H4.
    reflexivity.
  * inversion H.
    inversion H4.
    subst.
    apply IHl1 in H9.
    rewrite H9.
    reflexivity.
Qed.

Lemma alternate_alt :
  forall l1 l2 l3, alternate l1 l2 = l3 -> alt l1 l2 l3.
Proof.
induction l1; simpl; intros.
- rewrite H. apply alt_nil.
- destruct l2; subst; apply alt_step; try apply alt_nil.
  apply alt_step. apply IHl1. reflexivity.
Qed.

Extraction Language Ocaml.

Require Import ExtrOcamlBasic.
Require Import ExtrOcamlNatInt.

Extraction "alternate.ml" alternate.

(*
Fixpoint alternate' (l1 l2 : list nat) : list nat :=
match l1 with
| [] => l2
| h1 :: t1 => h1 :: alternate' l2 t1
end.
*)

Require Program.Wf.
Require Import Sorting.Permutation.

Program Fixpoint alternate' (l1 l2 : list nat) 
 { measure (length (l1 ++ l2)) } : { l | alt l1 l2 l } :=
match l1 with
| [] => l2
| h1 :: t1 => h1 :: alternate' l2 t1
end.

Next Obligation.
Proof.
apply alt_nil.
Defined.

Next Obligation.
Proof.
simpl.
assert (H_l: length (l2 ++ t1) = length (t1 ++ l2)).
  apply Permutation_length.
  apply Permutation_app_swap.
rewrite H_l.
auto with arith.
Defined.

Next Obligation.
case alternate'.
intros.
simpl.
apply alt_step.
assumption.
Defined.

Eval compute in proj1_sig (alternate' [1] [2]).

