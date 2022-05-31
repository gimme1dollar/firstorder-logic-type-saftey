(*
  CSE-433 Logic in Computer Science, POSTECH (gimme1dollar@postech.ac.kr, gla@postech.ac.kr)
    --- Type safety of the simply typed lambda-calculus
 *)

(*
  For this assignment, you may use any tactic and library functions.
  Here are excerpts from the sample solution, which you might find helpful in learning new Coq tactics. 

    - eapply 
    eapply IHk with (e':={y::~>Y**A}e2); auto. 

    - firstorder 
    induction e; simpl; try case_var; simpl; firstorder.

    - congruence 
    case_var; inversion H; subst; exists (n :: emptyset); split; auto; simpl; case_var; try congruence; auto.

    - forwards (from LibTactics.v, similar to pose) 
    forwards Ha : (IHe _ _ _ _ H2).
    forwards Ha : (IHe1 _ _ _ _ H3); destruct Ha as [Sa [? ?]].

    - f_equal 
    simpl in H; f_equal; firstorder.

    - destruct with ? 
    destruct Ha as [x [A0 [e0 ?]]].

    - v62 (library)  
    induction e; intros; simpl; try case_var; simple; eauto using list_always_incl_emptyset with v62.
  
    - assert ... by. 
    assert (k1 < S (max k1 k2)) by auto with arith.
    assert (size_e e2 <= size_e e1 + size_e e2) by auto with arith.

    - The following sequence of tactics creates a fresh parameter not found in [(X, C)::~>e']e) ++ (X :: emptyset). 
    set (L := param ([(X, C)::~>e']e) ++ (X :: emptyset)).
    destruct (pick_fresh L) as [Y Hfresh].
    unfold L in Hfresh.
 *)

(*
  Type safety of simply typed lambda-calculus 
 *)

 Set Implicit Arguments.

 Require Import List.
 Require Import Arith.
 Require Import Max. 
 Require Import LibTactics.    (* See LibTactics.v *)  
 Require Import LibNat.        (* See LibNat.v. You may use any lemmas in LibNat.v. *) 
 
 (** generating fresh nats *)
 
 Section Exist_fresh.
   Fixpoint MAX (L : list nat) : nat :=
     match L with
     | nil        => O
     | cons hd tl => max hd (MAX tl)
     end.
   
   Lemma ex_fresh_var_1 : forall x L,
     In x L -> (x <= MAX L).
   Proof.
   induction L; intros.
     inversion H; simpl.
     destruct (max_dec a (MAX L)); destruct H; simpl.
         subst; rewrite e; apply le_refl.
         eapply le_trans; [ apply IHL; trivial | apply le_max_r].
         subst; apply le_max_l.
         eapply le_trans; [apply IHL; trivial | apply le_max_r].
   Qed.
       
   Lemma ex_fresh_var_2 : forall x L,
     MAX L < x -> ~ In x L.
   Proof.
   induction L; intuition; simpl.
     inversion H0; simpl; subst.
       eelim (le_not_lt). eapply ex_fresh_var_1. apply H0. trivial.
     apply IHL. apply le_lt_trans with (m := (MAX (a :: L))). simpl; apply le_max_r. assumption.
     inversion H0; subst.
       eelim le_not_lt. eapply ex_fresh_var_1. apply H0. trivial.
       trivial.
   Qed.
 
   Lemma pick_fresh : forall (L : list nat),
     exists (n : nat), ~ In n L.
   Proof.
   induction L; intros.
     exists O; auto.
     exists (S (MAX (a :: L))); intuition.
     elim ex_fresh_var_2 with (x := (S (MAX (a :: L)))) (L := (a :: L)).
       apply lt_n_Sn.
       trivial.
   Qed.
 (* Now you can use 
       destruct (pick_fresh L) as [Y Hfresh].
    to generate a fresh natural number Y not found in the set L. *)  
 End Exist_fresh.
 
 (** 
   Definitions and rules 
  *)
 
 (** types *)
 Inductive typ : Set :=
   | typ_top   : typ                     (* dummy base type *)
   | typ_arrow : typ -> typ -> typ.      (* function type *) 
 Notation " A --> B " := (typ_arrow A B) (at level 65).
 
 (** variables and parameters *) 
 Notation var := nat.     (* variables *)
 Notation par := nat.     (* parameters *)  
 
 (** terms *) 
 Inductive tm : Set := 
 | tm_var : var -> tm                  (* variables *)
 | tm_par : par -> typ -> tm           (* parameters annotated with a type *)
 | tm_abs : var -> typ -> tm -> tm     (* lambda abstraction *)
 | tm_app : tm -> tm -> tm.            (* lambda application *) 
 (* parameter X annotated with type A *)
 Notation " X ** A " := (tm_par X A) (at level 65).   
 
 (* equality *) 
 
 Lemma typ_dec : forall A B : typ, {A = B} + {A <> B}.
 Proof.
   decide equality; apply eq_nat_dec.
 Qed.
 
 Lemma par_dec : forall (X Y : (par * typ)), {X = Y} + {X <> Y}.
 Proof.
   decide equality; [apply typ_dec | apply eq_nat_dec ].
 Qed.
 
 Notation "p ==== q" := (par_dec p q) (at level 70).
 (* Now you can use 'if p ==== q then ... else ...', 'destruct (p ==== q)', etc
    where you compare two parameters annotated with types. 
    Remember that you can compare two var's, or two par's, using 'x == y'. *)
 
 (** list of parameters in a given term e. *)
 Fixpoint param (e:tm) : list par :=
   match e with
   | tm_var x     => nil
   | tm_par X A   => X :: nil
   | tm_abs x A t => param (t)
   | tm_app t1 t2 => param (t1) ++ param(t2)
   end.
 
 (** substitution of e' for x in e0 *) 
 Fixpoint lsubst (x : var) (e' : tm) (e0 : tm) {struct e0} : tm :=
   (* Here you can use 'if x == y then ... else'. *)
   match e0 with
   | tm_var x' =>
       if x' == x 
       then e'
       else tm_var x'
   | tm_par x' A => 
       tm_par x' A
   | tm_abs x' A t =>
       if x' == x
       then tm_abs x' A t
       else tm_abs x' A (lsubst x e' t)
   | tm_app t1 t2 =>
       tm_app (lsubst x e' t1) (lsubst x e' t2)
   end.
 Notation "{ x ::~> e0 } e " := (lsubst x e0 e) (at level 67).
 
 (** substitution of e' for (X ** A) in e0 *)
 Fixpoint fsubst (X : par) (A:typ) (e' e0: tm) {struct e0} : tm :=
   match e0 with
   | tm_var x' => 
       tm_var x'
   | tm_par x' A' =>
       if x' == X
       then e'
       else tm_par x' A'
   | tm_abs x' A' t =>
       tm_abs x' A' (fsubst X A e' t)
   | tm_app t1 t2 =>
       tm_app (fsubst X A e' t1) (fsubst X A e' t2)
   end.
 Notation "[ ( X , A ) ::~> e ] e0 " := (fsubst X A e e0) (at level 67).
 
 (** size of term e0 *) 
 Fixpoint size_e (e0 : tm) : nat :=
   match e0 with
   | tm_var _     => 0
   | tm_par _ _   => 0
   | tm_abs _ _ t => size_e(t) + 1
   | tm_app t1 t2 => size_e(t1) + size_e(t2) + 1
   end.
 
 (** values.
     'value t' means that term t is a value *)
 Inductive value : tm -> Prop :=
   | VA : forall (x: var) (A: typ) (t: tm), value (tm_abs x A t).
 
 (** one-step reduction.
     'red t1 t2' means that term t1 reduces to term t2. *)
 Inductive red : tm -> tm -> Prop :=
   | RF : forall (t1 t2 t1': tm), red t1 t1' -> red (tm_app t1 t2) (tm_app t1' t2)
   | RA : forall (t1 t2 t2': tm), value t1 -> red t2 t2' -> red (tm_app t1 t2) (tm_app t1 t2')
   | RP : forall (t':tm) (x: var) (A: typ) (t: tm), value t' -> red (tm_app (tm_abs x A t) t') ({x::~>t'}t).
 
 (** locally closed terms.
     'lclosed S t' means that S is the list of temporarily unbound variables in term t. *) 
 Inductive lclosed : list var -> tm -> Prop := 
   (* You might find 'remove eq_nat_dec' useful. *)    
   | LVA : forall (x : var), lclosed (x::nil) (tm_var x)
   | LPA : forall (x : par) (A: typ), lclosed (nil) (tm_par x A)
   | LAB : forall (x: var) (A: typ) (t: tm) (s: list var), 
           lclosed s t -> lclosed (remove eq_nat_dec x s) (tm_abs x A t)
   | LAP : forall (t1: tm) (s1: list var) (t2: tm) (s2: list var),
           lclosed s1 t1 -> lclosed s2 t2 -> lclosed (s1 ++ s2) (tm_app t1 t2).
 
 (** typing relation.
     'typing t A' means that term t has type A. *)
 Inductive typing : tm -> typ -> Prop :=
   (* Hint: see typingLH below *)
   | TEP : forall (x: par) (A: typ), 
           typing (tm_par x A) A
   | TAB : forall (x: var) (A: typ) (B: typ) (t: tm) (X: par),
           ~ In X (param t)
           -> typing (lsubst x (tm_par X A) t) B 
           -> typing (tm_abs x A t) (A --> B)
   | TAP : forall (t1: tm) (A: typ) (t2: tm) (B: typ),
           typing t1 (A --> B) ->
           typing t2 A ->
           typing (tm_app t1 t2) B.
  
 Hint Constructors value.
 Hint Constructors red.
 Hint Constructors lclosed.
 Hint Constructors typing.
 
 (** tactic destructing equality cases *)
 Ltac case_var :=
   let ldestr X Y := destruct (X == Y); [try subst X | idtac] in
   let hdestr p q := destruct (p ==== q); [try subst p | idtac] in
   match goal with
   | |- context [?X == ?Y]      => ldestr X Y
   | H: context [?X == ?Y] |- _ => ldestr X Y
   | |- context [?p ==== ?q]      => hdestr p q
   | H: context [?p ==== ?q] |- _ => hdestr p q
   end.
 
 (** 
   Type safety 
  *)
 
 (** typing relation with sizes.
   We need typingLH because sometimes we need to perform induction on the size of typing judgments. 
  *)
 Inductive typingLH : nat -> tm -> typ -> Prop :=
 | typing_parLH : forall X A,
   typingLH O (tm_par X A) A
 | typing_absLH : forall x A B e X k,
   ~ In X (param e) 
   -> typingLH k (lsubst x (tm_par X A) e) B 
   -> typingLH (S k) (tm_abs x A e) (A --> B)
 | typing_appLH : forall e e' A B k1 k2,
   typingLH k1 e (A --> B) 
   -> typingLH k2 e' A 
   -> typingLH (S (max k1 k2)) (tm_app e e') B.
 
 Hint Constructors typingLH.


Ltac simplifyTac tac :=
let rec filter_list l :=
  match l with
    | emptyset => idtac
    | _ :: _ => idtac
    | _ => fail
  end
with filter_t t :=
  match t with
    | typ_top => idtac
    | typ_arrow _ _ => idtac
    | _ => fail
  end
with filter_e e :=
  match e with
    | tm_var _ => idtac
    | tm_par _ _ => idtac
    | tm_abs _ _ _ => idtac
    | tm_app _ _ => idtac
  end
with filter_param C :=
  match C with
    | param => idtac
    | _ => idtac
  end
with filter_lsubst S :=
  match S with
    | lsubst => idtac
    | _ => fail
  end
with filter_fsubst S :=
  match S with
    | fsubst => idtac
    | _ => fail
  end in
  match goal with
    | H: ?X = ?X |- _ => clear H; simplifyTac tac
    | H: ?X <> ?X |- _ => try congruence
    | H: context [?X == ?Y] |- _ =>
      destruct (X == Y); [ try subst X | idtac ]; simplifyTac tac
    | H: context [?X === ?Y] |- _ =>
      destruct (X === Y); [ try subst X | idtac ]; simplifyTac tac
    | |- context [?X == ?Y] =>
      destruct (X == Y); [ try subst X | idtac ]; simplifyTac tac
    | |- context [?X === ?Y] =>
      destruct (X === Y); [ try subst X | idtac ]; simplifyTac tac
    | H: context[ remove _ _ ?l ] |- _ =>
      filter_list l; simpl remove in H; simplifyTac tac
    | H : context[ ?C ?t ] |- _ =>
      filter_param C; filter_t t; simpl C in H; simplifyTac tac
    | H : context[ ?C ?e ] |- _ =>
      filter_param C; filter_e e; simpl C in H; simplifyTac tac
    | H : context[ lsubst _ _ ?t ] |- _ =>
      filter_t t; simpl lsubst in H; simplifyTac tac
    | H : context[ fsubst _ _ _ ?t ] |- _ =>
      filter_t t; simpl fsubst in H; simplifyTac tac
    | H : context[ ?S _ _ ?e ] |- _ =>
      filter_lsubst S; filter_e e; simpl S in H; simplifyTac tac
    | H : context[ ?S _ _ _ ?e ] |- _ =>
      filter_fsubst S; filter_e e; simpl S in H; simplifyTac tac
    | |- context[ remove _ _ ?l ] =>
      filter_list l; simpl remove; simplifyTac tac
    | |- context[ ?C ?t ] =>
      filter_param C; filter_t t; simpl C; simplifyTac tac
    | |- context[ ?C ?e ] =>
      filter_param C; filter_e e; simpl C; simplifyTac tac
    | |- context[ lsubst _ _ ?t ] =>
      filter_t t; simpl lsubst; simplifyTac tac
    | |- context[ fsubst _ _ _ ?t ] =>
      filter_t t; simpl fsubst; simplifyTac tac
    | |- context[ ?S _ _ ?e ] =>
      filter_lsubst S; filter_e e; simpl S; simplifyTac tac
    | |- context[ ?S _ _ _ ?e ] =>
      filter_fsubst S; filter_e e; simpl S; simplifyTac tac
    | _ => tac
  end.

Tactic Notation "Simplify" "by" tactic(tac) := simplifyTac tac.

 (* 
 
 Lemma typing_typingLH : forall e A,
   typing e A -> exists n : nat, typingLH n e A.
 
 Lemma size_nochange : forall x X A e,
   size_e ({x ::~> X**A}e) = size_e e.
 
 Lemma lclosed_var_split : forall e S0 x X A,
   lclosed S0 ({x ::~> X ** A}e) -> 
     (exists S, lclosed S e /\ remove eq_nat_dec x S = S0). 
 
 Lemma typing_subst_par_nochange : forall e e' X A,
   ~ In X (param e) -> [(X, A) ::~> e']e = e.
 
 Lemma subst_var_nochange : forall e S x e',
   lclosed S e ->
   ~ In x S ->
   {x ::~> e'}e = e.
 
 Lemma subst_var_var : forall e x X A y Y B,
   x <> y -> {y ::~> Y**B}({x ::~> X**A}e) = {x ::~> X**A}({y ::~> Y**B}e).
 
 Lemma subst_par_var : forall e e' x X A Y B,
   lclosed emptyset e' -> 
   X <> Y -> 
   [(Y, B) ::~> e']({x ::~> X**A}e) = {x ::~> X**A}([(Y, B) ::~> e']e).
  *) 

 Hint Resolve sym_eq list_remove_in : nochange.

 Lemma subst_seq_par_var : forall e e' x X A,
   ~ In X (param e) -> 
   [(X, A) ::~> e']({x ::~> X**A}e) = {x ::~> e'}e.
 Admitted.

  (*
 Lemma typing_lclosed : forall e A,
   typing e A -> lclosed emptyset e.
 
 Lemma param_sum : forall e e' x,
   incl (param ({x ::~> e'} e)) (param e ++ param e').
 
  *)
 
 (** renaming lemma 
   You want to first perform induction on k, as in:
     induction k.
     intros; elim (lt_n_O (l + size_e e)); auto.
   *)
 Lemma typingLH_rename_par : forall k e e' y Y Z A B l,
   l + size_e e < k
   -> typingLH l e' B 
   -> e' = ({y ::~> Y**A}e) 
   -> typingLH l ({y ::~> Z**A}e) B.
 Admitted.  
  
 Lemma typingLH_subst_par : forall m n e A e' X C, 
   n < m 
   -> typingLH n e A 
   -> typing e' C 
   -> typing ([(X, C) ::~> e']e) A.
 Admitted.
 
 (** substitution lemma *)
 Lemma typing_typingLH : forall t T,
   typing t T -> exists n, typingLH n t T.
 Proof.
  induction 1.
  exists 0; auto.
  inversion IHtyping as [k ?].
  exists (S k); eauto.
  inversion IHtyping1 as [k1 ?].
  inversion IHtyping2 as [k2 ?].
  exists (S (max k1 k2)); eauto.
 Qed.

 Lemma typing_subst_par : forall e A e' X C, 
   typing e A -> typing e' C -> typing ([(X, C) ::~> e']e) A.
 Proof.
  intros.
  destruct (typing_typingLH H) as [k ?]; eauto using typingLH_subst_par.
 Qed.

 Lemma typing_subst_var_par : forall x X A e e' B,
   ~ In X (param e) 
   -> typing ({x ::~> X**A}e) B
   -> typing e' A
   -> typing ({x ::~> e'}e) B.
 Proof.
  intros.
  rewrite <- subst_seq_par_var with (X := X) (A := A) by eauto.
  auto using typing_subst_par.
 Qed.

 (* 
 Lemma preservation_typ_aux : forall e C, 
   typing e C -> 
   forall e', red e e' -> typing e' C.
 
 Lemma preservation_fv_aux : forall e e',
   red e e' -> incl (param e') (param e).
  *)
 
 (** preservation theorem *)
 Lemma preservation_t : forall t T,
  typing t T ->
  forall u, red t u -> typing u T.
 Admitted.

 Lemma param_sum : forall t u x,
  incl (param ({x ::~> u} t)) (param t ++ param u).
 Admitted.

 Lemma preservation_fv : forall t u,
  red t u -> incl (param u) (param t).
 Admitted.

 Lemma preservation : forall e C, 
   typing e C -> 
   forall e', red e e' -> typing e' C /\ incl (param e') (param e).
 Proof.
  eauto using preservation_t, preservation_fv.
 Qed.

 
 (** canonical forms lemma *)
 Lemma canonical_form_abs : forall e A B,
   value e 
   -> typing e (A --> B)
   -> exists x A0 e0, e = tm_abs x A0 e0.
 Proof.
  induction 1; simpl; intros; eauto.
 Qed.
 
 (** progress theorem *)
 Lemma progress : forall e A,
   typing e A -> 
   param e = emptyset -> 
   value e \/ exists e', red e e'.
 Proof.
  induction 1; simpl; intro Hve; try congruence; auto.
  assert (param t1 = emptyset) by firstorder using app_eq_nil.
  assert (param t2 = emptyset) by firstorder using app_eq_nil.
  destruct (IHtyping1 H1).
    destruct (IHtyping2 H2).
      destruct (canonical_form_abs H3 H) as [a0 [T0 [t0 ?]]]; subst.
      right; eauto.
      destruct H4 as [t0 ?].
      right; exists (tm_app t1 t0); auto.
    destruct H3 as [t'' ?].
    right; exists (tm_app t'' t2); auto.
 Qed.
 