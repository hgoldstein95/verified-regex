Require Import EnsembleLemmas CpdtTactics Str.
Require Import List Ensembles Equality NPeano Arith Bool MSets.
Import ListNotations.

Inductive re : Type :=
| Phi : re
| Char : Str.char -> re
| Alt : re -> re -> re
| Con : re -> re -> re
| Star : re -> re.
Notation ε := (Star Phi).

Fixpoint nullify (r : re) : re :=
  match r with
  | Phi => Phi
  | Char _ => Phi
  | Alt r1 r2 => Alt (nullify r1) (nullify r2)
  | Con r1 r2 => Con (nullify r1) (nullify r2)
  | Star r => Star Phi
  end.

Fixpoint deriv (c : Str.char) (r : re) : re :=
  match r with
  | Phi => Phi
  | Char c' =>
    match Str.dec_eq_char c c' with
    | left _ => Star Phi
    | right _ => Phi
    end
  | Alt r1 r2 => Alt (deriv c r1) (deriv c r2)
  | Con r1 r2 => Alt (Con (deriv c r1) r2) (Con (nullify r1) (deriv c r2))
  | Star r => Con (deriv c r) (Star r)
  end.

Fixpoint deriv_str (s : Str.t) (r : re) : re :=
  match s with
  | [] => r
  | c :: s' => deriv_str s' (deriv c r)
  end.

Fixpoint contains_empty (r : re) : bool :=
  match r with
  | Phi => false
  | Char _ => false
  | Alt r1 r2 => contains_empty r1 || contains_empty r2
  | Con r1 r2 => contains_empty r1 && contains_empty r2
  | Star _ => true
  end.

Definition re_match (r : re) (s : Str.t) :=
  contains_empty (deriv_str s r).

Inductive denote : re -> Ensemble Str.t -> Prop :=
| Denote_phi : denote Phi (Empty_set Str.t)
| Denote_char : forall c,
    denote (Char c) (Singleton Str.t [c])
| Denote_alt : forall r s l m,
    denote r l ->
    denote s m ->
    denote (Alt r s) (Union Str.t l m)
| Denote_con : forall r s l m,
    denote r l ->
    denote s m ->
    denote (Con r s) (SetConcat l m)
| Denote_star : forall r l,
    denote r l ->
    denote (Star r) (SetStar l).

Hint Constructors denote.

Reserved Notation "A == B" (at level 50).
Inductive cong : re -> re -> Prop :=
| Cong_alt_associative : forall r s t,
    Alt r (Alt s t) == Alt (Alt r s) t
| Cong_alt_commutative : forall r s,
    Alt r s == Alt s r
| Cong_alt_zero : forall r, Alt r Phi == r
| Cong_alt_idempotent : forall r, Alt r r == r
| Cong_con_associative : forall r s t,
    Con r (Con s t) == Con (Con r s) t
| Cong_one_con : forall r, Con (Star Phi) r == r
| Cong_con_one : forall r, Con r (Star Phi) == r
| Cong_con_distribute_left : forall r s t,
    Con r (Alt s t) == Alt (Con r s) (Con r t)
| Cong_con_distribute_right : forall r s t,
    Con (Alt r s) t == Alt (Con r t) (Con s t)
| Cong_zero_con : forall r, Con Phi r == Phi
| Cong_con_zero : forall r, Con r Phi == Phi
| Cong_unroll_left : forall r,
    Alt (Star Phi) (Con r (Star r)) == Star r
| Cong_unroll_right : forall r,
    Alt (Star Phi) (Con (Star r) r) == Star r
| Cong_least_fixpoint_left : forall r s t,
    Alt (Con (Alt s r) t) t == t ->
    Alt (Con (Star r) s) t == t
| Cong_least_fixpoint_right : forall r s t,
    Alt (Con (Alt r s) t) s == s ->
    Alt (Con r (Star t)) s == s
| Cong_refl : forall r, r == r
| Cong_sym : forall r s, r == s -> s == r
| Cong_trans : forall r s t,
    r == s ->
    s == t ->
    r == t
| Cong_alt_cong : forall r s t u,
    r == s ->
    t == u ->
    Alt r t == Alt s u
| Cong_con_cong : forall r s t u,
    r == s ->
    t == u ->
    Con r t == Con s u
| Cong_star_cong : forall r s,
    r == s ->
    Star r == Star s
where "A == B" := (cong A B).

Hint Constructors cong.

Add Parametric Relation : re cong
    reflexivity proved by Cong_refl
    symmetry proved by Cong_sym
    transitivity proved by Cong_trans
      as cong_relation.

Add Parametric Morphism : Alt with signature
    cong ++> cong ++> cong as Alt_cong_mor.
  intros.
  apply Cong_alt_cong ; auto.
Qed.

Add Parametric Morphism : Con with signature
    cong ++> cong ++> cong as Con_cong_mor.
  intros.
  apply Cong_con_cong ; auto.
Qed.

Add Parametric Morphism : Star with signature
    cong ++> cong as Star_cong_mor.
  apply Cong_star_cong.
Qed.

Lemma nullify_phi_or_empty :
  forall r, nullify r == Phi \/ nullify r == Star Phi.
Proof.
  Ltac split_app :=
    repeat
      match goal with
      | [ H : _ \/ _ |- _ ] => destruct H
      end ;
    repeat
      match goal with
      | [ H : nullify _ == _ |- _ ] => try rewrite H ; clear H
      end ;
    auto.
  induction r ; simpl ; auto ; split_app. right.
  transitivity (Alt (Star Phi) Phi) ; auto.
Qed.

Lemma denote_unique :
  forall r l m, denote r l -> denote r m -> l = m.
Proof.
  intros r l m Hl Hm.
  dependent induction r ; inversion Hl ; inversion Hm ; subst ; auto.
  - pose proof (IHr1 l0 l1 H1 H6).
    pose proof (IHr2 m0 m1 H3 H8).
    subst.
    auto.
  - pose proof (IHr1 l0 l1 H1 H6).
    pose proof (IHr2 m0 m1 H3 H8).
    subst.
    auto.
  - pose proof (IHr l0 l1 H0 H3).
    subst.
    auto.
Qed.

Theorem cong_sound :
  forall r s lr ls, r == s -> denote r lr -> denote s ls -> lr = ls.
Proof.
  Ltac invert H := inversion H ; subst ;  clear H.
  Ltac unify_denote :=
    repeat
      match goal with
      | [ H1 : denote ?r ?l, H2 : denote ?r ?m |- _ ] =>
        pose proof (denote_unique r l m H1 H2) ; subst ; clear H2
      end.
  Ltac invert_re :=
    repeat
      match goal with
      | [ H : denote (Alt _ _) _ |- _ ] => invert H
      | [ H : denote (Con _ _) _ |- _ ] => invert H
      | [ H : denote Phi _ |- _ ] => invert H
      | [ H : denote (Star _) _ |- _ ] => invert H
      end.
  intros.
  induction H ; invert_re ; unify_denote.
  - union_crush.
  - union_crush.
  - union_crush.
  - union_crush.
  - apply set_concat_assoc.
  - apply set_concat_neut_l.
  - apply set_concat_neut_r.
Abort.
