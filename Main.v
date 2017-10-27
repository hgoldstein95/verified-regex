Require Import DecEq.
Require Import EnsembleLemmas.
Require Import List Ensembles Equality NPeano Arith Bool.
Import ListNotations.

Section Regex.
  Context {T : Type}.
  Context (dec_eq_ : DecEq T).

  Definition str := list T.

  Inductive re : Type :=
  | Phi : re
  | Char : T -> re
  | Alt : re -> re -> re
  | Con : re -> re -> re
  | Star : re -> re.
  Notation ε := (Star Phi).

  Fixpoint contains_empty (r : re) : bool :=
    match r with
    | Phi => false
    | Char _ => false
    | Alt r1 r2 => contains_empty r1 || contains_empty r2
    | Con r1 r2 => contains_empty r1 && contains_empty r2
    | Star _ => true
    end.

  Fixpoint deriv (c : T) (r : re) : re :=
    match r with
    | Phi => Phi
    | Char c' =>
      match dec_eq c c' with
      | left _ => Star Phi
      | right _ => Phi
      end
    | Alt r1 r2 => Alt (deriv c r1) (deriv c r2)
    | Con r1 r2 =>
      if contains_empty r1 then
        Alt (Con (deriv c r1) r2) (deriv c r2)
      else
        Con (deriv c r1) r2
    | Star r => Con (deriv c r) (Star r)
    end.

  Fixpoint deriv_str (s : str) (r : re) : re :=
    match s with
    | [] => r
    | c :: s' => deriv_str s' (deriv c r)
    end.

  Definition re_match (r : re) (s : str) := contains_empty (deriv_str s r).

  Inductive denote : re -> Ensemble str -> Prop :=
  | Denote_phi : denote Phi (Empty_set str)
  | Denote_char : forall c,
      denote (Char c) (Singleton str [c])
  | Denote_alt : forall r s l m,
      denote r l ->
      denote s m ->
      denote (Alt r s) (Union str l m)
  | Denote_con : forall r s l m,
      denote r l ->
      denote s m ->
      denote (Con r s) (SetConcat l m)
  | Denote_star : forall r l,
      denote r l ->
      denote (Star r) (SetStar l).

  Hint Constructors denote.

  Ltac invert H := inversion H ; subst ; clear H ; auto.

  Theorem match_in_denote :
    forall r s l, re_match r s = true -> denote r l -> In str l s.
  Proof.
    intros r s l Hmatch Hden.
    induction Hden ;
      induction s ;
      unfold re_match in * ;
      simpl in * ;
      try discriminate.
    - apply IHs in Hmatch. contradict Hmatch.
    - remember (dec_eq a c) as Hdec.
      destruct Hdec ; subst ; clear HeqHdec.
  Abort.

  Lemma unique_denote :
    forall r, exists l, denote r l /\ forall l', denote r l' -> l' = l.
  Proof.
    Ltac dest_IH :=
      repeat match goal with
             | [ H : exists _ : _, _ |- _ ] => destruct H
             | [ H : _ /\ _ |- _ ] => destruct H
             end.
    Ltac lcrush :=
      split ; auto ; intros l' H' ; invert H' ;
      repeat match goal with
             | [ H1 : forall _ : _, denote ?r _ -> _ = _,
                   H2 : denote ?r _ |- _ ] => apply H1 in H2
             end ;
      subst ;
      auto.
    dependent induction r ; dest_IH  ;
      [ exists (Empty_set str) |
               exists (Singleton str [t]) |
               exists (Union str x0 x) |
               exists (SetConcat x0 x) |
               exists (SetStar x) ] ;
      lcrush.
  Qed.

  Theorem in_denote_match : forall r l,
      denote r l -> (forall s, In str l s -> re_match r s = true).
  Abort.
End Regex.