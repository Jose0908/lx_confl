(* begin hide *)
Require Import Arith Lia.

Require Export Metalib.Metatheory.
Require Export Metalib.LibDefaultSimp.
Require Export Metalib.LibLNgen. 
Require Import PeanoNat.

Lemma strong_induction: forall (P:nat->Prop), (forall n, (forall m, m < n -> P m) -> P n) -> (forall n, P n).
Proof.
  intros Q IH n.
  assert (H := nat_ind (fun n => (forall m : nat, m < n -> Q m))).
  apply IH. apply H.
  - intros m Hlt; inversion Hlt.
  - intros n' H' m Hlt. apply IH. intros m0 Hlt'. apply H'. apply Nat.lt_succ_r in Hlt.  apply Nat.lt_le_trans with m.
    + assumption.
    + lia.
Qed.

Lemma in_or_notin: forall x s, x `in` s \/ x `notin` s.
Proof.
  intros. pose proof notin_diff_1. specialize (H x s s).
  rewrite AtomSetProperties.diff_subset_equal in H.
  - apply or_comm. apply H. apply notin_empty_1.
  - reflexivity.
Qed.

Lemma diff_remove_2: forall x y s, x <> y -> x `notin` remove y s -> x `notin` s.
Proof.
  intros. default_simp.
Qed. 

Lemma aux_not_equal : forall (x:atom) (y:atom), x <> y -> y <> x.
Proof.
  intros. unfold not. intros. unfold not in H.
  assert (x = y).
  - subst. reflexivity.
  - contradiction.
Qed.

Lemma remove_singleton_empty: forall x, remove x (singleton x) [=] empty.
Proof.
  intros. rewrite AtomSetProperties.singleton_equal_add. rewrite AtomSetProperties.remove_add.
  - reflexivity.
  - apply notin_empty_1.
Qed.
  
Lemma remove_singleton: forall t1 t2, remove t1 (singleton t1) [=] remove t2 (singleton t2).
Proof.
  intros t1 t2. repeat rewrite remove_singleton_empty. reflexivity.
Qed.

Lemma notin_singleton_is_false: forall x, x `notin` (singleton x) -> False.
Proof.
  intros. intros. apply notin_singleton_1 in H. contradiction.
Qed.

Lemma double_remove: forall x s, remove x (remove x s) [=] remove x s.
Proof.
  intros. pose proof AtomSetProperties.remove_equal.
  assert (x `notin` remove x s). apply AtomSetImpl.remove_1. reflexivity.
  specialize (H (remove x s) x). apply H in H0. assumption.
Qed.

Lemma remove_symmetric: forall x y s, remove x (remove y s) [=] remove y (remove x s).
Proof.
  intros. split.
  - intros. case (a == x); intros; case (a == y); intros; subst. apply AtomSetImpl.remove_3 in H.
    + rewrite double_remove. assumption.
    + apply remove_iff in H. inversion H. contradiction.
    + apply remove_iff in H. inversion H. apply remove_iff in H0. inversion H0. contradiction.
    + pose proof H. apply AtomSetImpl.remove_3 in H. apply AtomSetImpl.remove_2.
      * apply aux_not_equal; assumption.
      * apply AtomSetImpl.remove_2.
        ** apply aux_not_equal; assumption.
        ** apply AtomSetImpl.remove_3 in H. assumption.
  - intros. case (a == x); intros; case (a == y); intros; subst.
    + apply AtomSetImpl.remove_3 in H. rewrite double_remove. assumption.
    + apply remove_iff in H. inversion H. apply remove_iff in H0. inversion H0. contradiction.
    + apply remove_iff in H. inversion H. contradiction.
    + pose proof H. apply AtomSetImpl.remove_3 in H. apply AtomSetImpl.remove_2.
      * apply aux_not_equal; assumption.
      * apply AtomSetImpl.remove_2.
        ** apply aux_not_equal; assumption.
        ** apply AtomSetImpl.remove_3 in H. assumption.
Qed.

Lemma remove_empty: forall x, remove x empty [=] empty.
Proof.
  intros. pose proof notin_empty. specialize (H x). apply AtomSetProperties.remove_equal in H. assumption.
Qed.

Lemma diff_remove: forall x y s, x <> y -> x `notin` s -> x `notin` remove y s.
Proof.
  intros. apply notin_remove_2. assumption.
Qed.

Definition vswap (x:atom) (y:atom) (z:atom) := if (z == x) then y else if (z == y) then x else z.

Lemma vswap_id: forall x y, vswap x x y = y.
Proof.
  intros. unfold vswap. case (y == x); intros; subst; reflexivity. 
Qed.

Lemma vswap_in: forall x y z, vswap x y z = x \/ vswap x y z = y \/  vswap x y z = z.
Proof.
  intros x y z. unfold vswap. default_simp.
Qed.

Lemma vswap_eq: forall x y z w, vswap x y z = vswap x y w <-> z = w.
Proof.
  intros x y z w; split.
  - unfold vswap. default_simp.
  - intro H; subst. reflexivity.
Qed.

Lemma vswap_neq: forall x y z, x <> z -> y <> z -> vswap x y z = z.
Proof.
  intros x y z H1 H2. unfold vswap. default_simp.
Qed.
(* end hide *)

(**

%\begin{equation}\label{es:grammar}
  t ::= x \mid \lambda_x.t \mid t\ t \mid \esub{t}{x}{u}
\end{equation}%
%\noindent% where $[x := u] t$ represents a term with an operator that will be evaluated with specific rules of a substitution calculus. The intended meaning of the explicit substitution is that it will simulate the metasubstitution. This formalization aims to be a generic framework applicable to any calculi with explicit substitutions using a named notation for variables. 

The following inductive definition corresponds to the grammar (%\ref{es:grammar}%), where the explicit substitution constructor, named [n_sub], has a special notation. Accordingly, [n_sexp] denotes the set of nominal $\lambda$-expressions equipped with an explicit substitution operator, which, for simplicity, we will refer to as just _terms_.

 *)

Inductive n_sexp : Set :=
| n_var (x:atom)
| n_abs (x:atom) (t:n_sexp)
| n_app (t1:n_sexp) (t2:n_sexp)
| n_sub (t1:n_sexp) (x:atom) (t2:n_sexp).

Notation "[ x := u ] t" := (n_sub t x u) (at level 60).

(**

The [Notation] statement allow us to write [([x := u] t)] instead of [(n_sub t x u)], which is closer to paper and pencil notation, as well as to the syntax of the grammar (%\ref{es:grammar}%).

The contributions of this work are as follows:
%\begin{enumerate}
 \item
 \item 
\end{enumerate}% 
*)
(* begin hide *)
Inductive pure : n_sexp -> Prop :=
 | pure_var : forall x, pure (n_var x)
 | pure_app : forall e1 e2, pure e1 -> pure e2 -> pure (n_app e1 e2) 
 | pure_abs : forall x e1, pure e1 -> pure (n_abs x e1).

Definition Rel (A: Type) := A -> A -> Prop.


Fixpoint size (t : n_sexp) : nat :=
  match t with
  | n_var x => 1
  | n_abs x t => 1 + size t
  | n_app t1 t2 => 1 + size t1 + size t2
  | n_sub t1 x t2 => 1 + size t1 + size t2
  end.

Lemma n_sexp_size: forall t, size t > 0.
Proof.
  induction t.
  - simpl. auto.
  - simpl. auto.
  - simpl. lia.
  - simpl. lia.
Qed.    

Lemma n_sexp_induction: forall P : n_sexp -> Prop, (forall x, P (n_var x)) ->
                                                     (forall t1 z, (forall t2, size t2 = size t1 -> P t2) -> P (n_abs z t1)) ->
                                                     (forall t1 t2, P t1 -> P t2 -> P (n_app t1 t2)) ->
                                                     (forall t1 t3 z, P t3 -> (forall t2, size t2 = size t1 -> P t2) -> P (n_sub t1 z t3)) -> (forall t, P t).
Proof.
  intros P Hvar Habs Happ Hsub t. remember (size t) as n. generalize dependent t. induction n using strong_induction. intro t; case t.
  - intros x Hsize. apply Hvar.
  - intros x t' Hsize. apply Habs. intros t'' Hsize'. apply H with (size t'').
    + rewrite Hsize'. rewrite Hsize. simpl. lia. 
    + reflexivity.
  - intros t1 t2 Hsize. simpl in Hsize. apply Happ.
    + apply H with ((size t1)).
      * rewrite Hsize. lia. 
      * reflexivity.
    + apply H with ((size t2)).
      * rewrite Hsize. lia.
      * reflexivity.
  - intros t1 x t2 Hsize. simpl in Hsize. apply Hsub.
    + apply H with (size t2).
      * rewrite Hsize. lia.
      * reflexivity.
    + intros t1' Hsize'. apply H with (size t1').
      * rewrite Hsize'. rewrite Hsize. lia. 
      * reflexivity.
Qed.

Lemma n_sexp_size_induction_P: forall P: n_sexp -> Prop,
  (forall x, (forall y, size y < size x -> P y) -> P x) -> forall z, P z.
Proof.
  intros P IH z. remember (size z) as n. generalize dependent z. induction n using strong_induction.
intro z. case z eqn:H'. 
  - intro H''. apply IH. intros y Hsize. simpl in Hsize. inversion Hsize; subst.
    + pose proof n_sexp_size as H2. specialize (H2 y). lia.
    + lia.
  - intro H''. apply IH. intros y Hsize. apply (H (size y)).
    + simpl in *. subst. assumption.
    + reflexivity.
  - intro H''. apply IH. intros y Hsize. apply (H (size y)).
    + simpl in *. subst. assumption.
    + reflexivity.
  - intro H''. apply IH. intros y Hsize. apply (H (size y)).
    + simpl in *. subst. assumption.
    + reflexivity.
Qed.

Lemma n_sexp_size_induction: forall P : n_sexp -> Prop, (forall x, P (n_var x)) ->
                                                     (forall t1 z, (forall t1', size t1' < size (n_abs z t1) -> P t1') -> P (n_abs z t1)) ->
                                                     (forall t1 t2, (forall t1', size t1' < size (n_app t1 t2) -> P t1') -> P (n_app t1 t2)) ->
                                                     (forall t1 t2 z, (forall t1', size t1' < size (n_sub t1 z t2) -> P t1') -> P (n_sub t1 z t2)) -> (forall t, P t).
Proof.
  intros P Hvar Habs Happ Hsub t. remember (size t) as n. generalize dependent t. induction n using strong_induction. intro t; case t.
  - intros x Hsize. apply Hvar.
  - intros x t' Hsize. apply Habs. intros t'' Hsize'. apply H with (size t'').
    + rewrite Hsize. simpl. auto.
    + reflexivity.
  - intros t1 t2 Hsize. apply Happ. intros t1' Hsize'. apply H with (size t1').
    + rewrite Hsize. assumption.
    + reflexivity.
  - intros t1 x t2 Hsize. simpl in *. apply Hsub. intros t1' Hsize'. apply H with (size t1').
    + rewrite Hsize. assumption.
    + reflexivity.
Qed.

Fixpoint fv_nom (t : n_sexp) : atoms :=
  match t with
  | n_var x => {{x}}
  | n_abs x t1 => remove x (fv_nom t1)
  | n_app t1 t2 => fv_nom t1 `union` fv_nom t2
  | n_sub t1 x t2 => (remove x (fv_nom t1)) `union` fv_nom t2
  end.

Lemma notin_abs: forall x y t, x <> y -> x `notin` fv_nom (n_abs y t) -> x `notin` fv_nom t.
Proof.
  intros x y t H. pose proof in_or_notin as H1. specialize (H1 x (fv_nom t)). destruct H1 as [H1 | H1].
    - intro H2. simpl in *. apply notin_remove_1 in H2. destruct H2.
      + subst. contradiction.
      + assumption.
    - intro H2. assumption.
Qed.

Fixpoint swap (x:atom) (y:atom) (t:n_sexp) : n_sexp :=
  match t with
  | n_var z     => n_var (vswap x y z)
  | n_abs z t1  => n_abs (vswap x y z) (swap x y t1)
  | n_app t1 t2 => n_app (swap x y t1) (swap x y t2)
  | n_sub t1 z t2 => n_sub (swap x y t1) (vswap x y z) (swap x y t2)
  end.

Lemma swap_id : forall t x, swap x x t = t.
Proof.
  induction t; simpl; unfold vswap; default_simp.
Qed.

Lemma swap_eq: forall x y z w, vswap x y z = vswap x y w -> z = w.
Proof.
  intros x y z w H. unfold vswap in H. destruct (z == x).
  - subst. destruct (w == x).
    + rewrite e. reflexivity.
    + destruct (w == y).
      * subst. contradiction.
      * subst. contradiction.
  - destruct (z == y).
    + subst. destruct (w == x).
      * subst. contradiction.
      * destruct (w == y).
        ** subst. reflexivity.
        ** subst. contradiction.
    + destruct (w == x).
      * subst. contradiction.
      * destruct (w == y).
        ** subst. contradiction.
        ** assumption.
Qed.  

Lemma swap_eq': forall x y z w, z = w -> swap x y z = swap x y w.
Proof.
  intros x y z w H. subst. reflexivity.
Qed.

Lemma swap_neq: forall x y z w, z <> w -> vswap x y z <> vswap x y w.
Proof.
  intros x y z w H1 H2. unfold vswap. destruct (z == x).
  - subst. apply swap_eq in H2. contradiction.
  - apply swap_eq in H2. contradiction.
Qed.

Lemma swap_size_eq : forall x y t, size (swap x y t) = size t.
Proof.
  induction t; simpl; auto.
Qed.

Lemma swap_symmetric : forall t x y, swap x y t = swap y x t.
Proof.
  induction t as [z | z t1 | t1 IHt1 t2 IHt2 | t1 IHt1 z t2 IHt2 ].
  - intros x y. simpl. unfold vswap. default_simp.
  - intros x y; simpl. unfold vswap. default_simp.
  - intros x y; simpl. rewrite IHt1. rewrite IHt2; reflexivity.
  - intros. simpl. unfold vswap. default_simp.
Qed.
      
Lemma swap_involutive : forall t x y, swap x y (swap x y t) = t.
Proof.
 induction t; intros; simpl; unfold vswap; default_simp.
Qed.

Lemma swap_inverse: forall x y t1 t2, t1 = swap x y t2 -> t2 = swap x y t1.
Proof.
  intros. rewrite H. rewrite swap_involutive. reflexivity.
Qed.

Lemma shuffle_swap : forall w y z t, w <> z -> y <> z -> (swap w y (swap y z t)) = (swap w z (swap w y t)).
Proof.
  induction t; intros; simpl; unfold vswap; default_simp.
Qed.

Lemma shuffle_swap' : forall w y n z, w <> z -> y <> z -> (swap w y (swap y z n)) = (swap z w (swap y w n)).
Proof.
  induction n; intros; simpl; unfold vswap; default_simp.
Qed.

Lemma vswap_equivariance : forall v x y z w, vswap x y (vswap z w v) = vswap (vswap x y z) (vswap x y w) (vswap x y v).
Proof.
  intros; unfold vswap; case(v == z); case (w == x); default_simp.
Qed.

Lemma swap_equivariance : forall t x y z w, swap x y (swap z w t) = swap (vswap x y z) (vswap x y w) (swap x y t).
Proof.
  induction t.
  - intros. unfold vswap. case (z == x0).
    + case (w == x0).
      * intros. rewrite swap_id. rewrite e; rewrite e0. rewrite swap_id. reflexivity.
      * intros. case (w == y).
        ** intros. rewrite swap_symmetric. rewrite e; rewrite e0. reflexivity.
        ** intros. unfold swap. unfold vswap. default_simp.
    + unfold swap. unfold vswap. intros. default_simp.
  - intros. simpl. rewrite IHt. unfold vswap. case (x == z).
    + case (w == x0); default_simp.
    + case (w == x0).
      * default_simp.
      * intros. case (x == w); intros; case (z == x0); default_simp.
  - intros. simpl. rewrite IHt1. rewrite IHt2. reflexivity.
  - intros. simpl. rewrite IHt1. rewrite IHt2. unfold vswap. default_simp.    
Qed.

Lemma pure_swap : forall x y t, pure t -> pure (swap x y t).
Proof.
  intros x y t H. induction H.
  - simpl. unfold vswap. case (x0 == x); case (x0 == y); intros; subst; apply pure_var.
  - simpl. apply pure_app; assumption.
  - simpl. unfold vswap. case (x0 == x); case (x0 == y); intros; subst; apply pure_abs; assumption.
Qed.

Lemma pure_swap_2: forall t x y, pure (swap x y t) -> pure t.
Proof.
  induction t as [z | z t1 | t1 IHt1 t2 IHt2 | t1 IHt1 z t2 IHt2 ].
  - intros x y Hpure. apply pure_var.
  - intros x y Hpure. apply pure_abs. simpl in Hpure. inversion Hpure; subst. apply IHt1 with x y. assumption.
  - intros x y Hpure. apply pure_app.
    + simpl in Hpure. inversion Hpure; subst. apply IHt1 with x y. assumption.
    + simpl in Hpure. inversion Hpure; subst. apply IHt2 with x y. assumption.
  - intros x y Hpure. simpl in Hpure. inversion Hpure.
Qed.

Inductive ctx  (R : Rel n_sexp): Rel n_sexp :=
 | step_redex: forall (t1 t2: n_sexp), R t1 t2 -> ctx R t1 t2
 | step_n_abs: forall (t1 t2: n_sexp) (x: atom), ctx R t1 t2 -> ctx R (n_abs x t1) (n_abs x t2)
 | step_n_app_left: forall (t1 t1' t2: n_sexp) , ctx R t1 t1' -> ctx R (n_app t1 t2) (n_app t1' t2)
 | step_n_app_right: forall (t1 t2 t2': n_sexp) , ctx R t2 t2' -> ctx R (n_app t1 t2) (n_app t1 t2')
 | step_n_sub_out: forall (t1 t1' t2: n_sexp) (x : atom) , ctx R t1 t1' -> ctx R ([x := t2]t1) ([x := t2]t1')
 | step_n_sub_in: forall (t1 t2 t2': n_sexp) (x:atom), ctx R t2 t2' -> ctx R ([x := t2]t1) ([x := t2']t1).

Lemma n_sexp_induction_ctx: forall (R: Rel n_sexp) (P : n_sexp -> n_sexp -> Prop), (forall t1 t2 : n_sexp, R t1 t2 -> P t1 t2) -> 
       (forall (t1 t2 : n_sexp) (x: atom), ctx R t1 t2 -> (forall t1' t2', size t1' = size t1 -> size t2' = size t2 -> ctx R t1' t2' -> P t1' t2') -> P (n_abs x t1) (n_abs x t2)) ->
       (forall t1 t1' t2 : n_sexp, ctx R t1 t1' -> P t1 t1' -> P (n_app t1 t2) (n_app t1' t2)) ->
       (forall t1 t2 t2' : n_sexp, ctx R t2 t2' -> P t2 t2' -> P (n_app t1 t2) (n_app t1 t2')) ->
       (forall (t1 t1' t2 : n_sexp) (x: atom), ctx R t1 t1' -> (forall t1'' t1''', size t1'' = size t1 -> size t1''' = size t1' -> ctx R t1'' t1''' -> P t1'' t1''') -> P ([x := t2] t1) ([x := t2] t1')) ->
       (forall (t1 t2 t2' : n_sexp) (x y: atom), ctx R t2 t2' -> P t2 t2' -> P ([x := t2] t1) ([y := t2'] t1)) ->
       forall t1 t2 : n_sexp, ctx R t1 t2 -> P t1 t2.
Proof.
  intros R P H Habs Happ_left Happ_right Hsub_out Hsub_in t1 t2 Hctx. remember (size t1 + size t2) as n. generalize dependent t2. generalize dependent t1. induction n using strong_induction. intros t1 t2 Hctx Hsize. induction Hctx.
  - apply H. assumption.
  - apply Habs.
    + assumption.
    + intros t1' t2' Hsize1 Hsize2 Hbeta'. apply H0 with (size t1 + size t2).
      * rewrite Hsize. simpl. lia.
      * assumption.
      * rewrite Hsize1. rewrite Hsize2. reflexivity.
  - apply Happ_left.
    + assumption.
    + apply H0 with (size t1 + size t1').
      * rewrite Hsize. simpl. lia.
      * assumption.
      * reflexivity.
  - apply Happ_right.
    + assumption.
    + apply H0 with (size t2 + size t2').
      * rewrite Hsize. simpl. lia.
      * assumption.
      * reflexivity.
  - apply Hsub_out.
    + assumption.
    + intros t1'' t1''' Hsize1 Hsize2 Hbeta'. apply H0 with (size t1'' + size t1''').
      * rewrite Hsize. simpl. lia.
      * assumption.
      * reflexivity.
  - apply Hsub_in.
    + assumption.
    + apply H0 with (size t2 + size t2').
      * rewrite Hsize. simpl. lia.
      * assumption.
      * reflexivity.
Qed.
(* end hide *)

(** * The Nominal Framework *)

(**

As usual in the standard presentations of the $\lambda$-calculus, our formalization is done considering terms modulo $\alpha$-equivalence. This means that terms that differ only by the names of bound variables are _equal_. Formally, the notion of $\alpha$-equivalence is defined by the following rules of inference: 

%\begin{mathpar}
 \inferrule*[Left={({\rm\it aeq\_abs\_same})}]{t_1 =_\alpha t_2}{\lambda_x.t_1 =_\alpha \lambda_x.t_2} 
\and \inferrule*[Right={({\rm\it aeq\_abs\_diff})}]{x \neq y \and x \notin fv(t_2) \and t_1 =_\alpha \swap{y}{x}{t_2}}{\lambda_x.t_1 =_\alpha \lambda_y.t_2} 
\end{mathpar}%

%\begin{mathpar}
 \inferrule*[Left={({\rm\it aeq\_var})}]{~}{x =_\alpha x} \and \inferrule*[Right={({\rm\it aeq\_app})}]{t_1 =_\alpha t_1' \and t_2 =_\alpha t_2'}{t_1\ t_2 =_\alpha t_1'\ t_2'} \and  \inferrule*[Right={({\rm\it aeq\_sub\_same})}]{t_1 =_\alpha t_1' \and t_2 =_\alpha t_2'}{\esub{t_1}{x}{t_2} =_\alpha \esub{t_1'}{x}{t_2'}} 
\end{mathpar}%

%\begin{mathpar}
\inferrule*[Right={({\rm\it aeq\_sub\_diff})}]{t_2 =_\alpha t_2' \and x \neq y \and x \notin fv(t_1') \and t_1 =_\alpha \swap{y}{x}{t_1'}}{\esub{t_1}{x}{t_2} =_\alpha \esub{t_1'}{y}{t_2'}} 
\end{mathpar}%

%\noindent% where $fv(t)$ denotes the set of free variables of $t$, and $\swap{x}{y}{t}$ is defined as follows:

%\begin{equation}\label{def:swap}
\swap{x}{y}{t} := \left\{ \begin{array}{ll}
\vswap{x}{y}{z}, & \mbox{ if } t = z; \\
\lambda_{\vswap{x}{y}{z}}.\swap{x}{y}{t_1}, & \mbox{ if } t = \lambda_z.t_1; \\
\swap{x}{y}{t_1}\ \swap{x}{y}{t_2}, & \mbox{ if } t = t_1\ t_2\\
\esub{(\swap{x}{y}{t_1})}{\vswap{x}{y}{z}}{\swap{x}{y}{t_2}}\ , & \mbox{ if } t = \esub{t_1}{z}{t_2}\\
\end{array}\right.
\end{equation}% and
$\vswap{x}{y}{z} := \left\{ \begin{array}{ll}
y, & \mbox{ if } z = x; \\
x, & \mbox{ if } z = y; \\
z, & \mbox{ otherwise. } \\
\end{array}\right.$

The corresponding Coq code for $\alpha$-equivalence is given by the inductive definition [aeq] below. Note that each rule corresponds to a constructor with its corresponding name.

 *)

Inductive aeq : Rel n_sexp :=
| aeq_var : forall x, aeq (n_var x) (n_var x)
| aeq_abs_same : forall x t1 t2, aeq t1 t2 -> aeq (n_abs x t1)(n_abs x t2)
| aeq_abs_diff : forall x y t1 t2, x <> y -> x `notin` fv_nom t2 -> aeq t1 (swap y x t2) ->
  aeq (n_abs x t1) (n_abs y t2)
| aeq_app : forall t1 t2 t1' t2', aeq t1 t1' -> aeq t2 t2' -> aeq (n_app t1 t2) (n_app t1' t2')
| aeq_sub_same : forall t1 t2 t1' t2' x, aeq t1 t1' -> aeq t2 t2' -> aeq ([x := t2] t1) ([x := t2'] t1')
| aeq_sub_diff : forall t1 t2 t1' t2' x y, aeq t2 t2' -> x <> y -> x `notin` fv_nom t1' -> aeq t1 (swap y x t1') -> aeq ([x := t2] t1) ([y := t2'] t1').

Notation "t =a u" := (aeq t u) (at level 60).
(* begin hide *)
Lemma aeq_refl : forall t, t =a t.
Proof.
  induction t.
  - apply aeq_var.
  - apply aeq_abs_same; assumption.
  - apply aeq_app; assumption.
  - apply aeq_sub_same; assumption.
Qed.

Example aeq1 : forall x y, x <> y -> (n_abs x (n_var x)) =a (n_abs y (n_var y)).
Proof.
  intros x y Hneq. apply aeq_abs_diff.
  - assumption.
  - simpl. apply notin_singleton. apply aux_not_equal; assumption.
  - simpl. unfold vswap. rewrite eq_dec_refl. apply aeq_var.
Qed.

Lemma aeq_var_2 : forall x y, (n_var x) =a (n_var y) -> x = y.
Proof.
  intros. inversion H; subst. reflexivity.
Qed.

Lemma aeq_nvar_1: forall t x, t =a (n_var x) -> t = n_var x.
Proof.
  induction t.
  - intros x' H. inversion H; subst. reflexivity.
  - intros x' H. inversion H.
  - intros x H. inversion H.
  - intros x' H. inversion H.
Qed.

Lemma aeq_n_app: forall  t t' t'', n_app t t' =a t'' -> exists u u', t'' = n_app u u'.
Proof.
  intros t t' t'' H. inversion H; subst. exists t1', t2'. reflexivity.
Qed.  

Lemma aeq_n_abs: forall t' t x, n_abs x t =a t' -> exists y t'', t' = n_abs y t''.
Proof.
  induction t' as [z | z t1 | t1 IHt1 t2 IHt2 | t1 IHt1 z t2 IHt2 ].
  - intros t x Haeq. inversion Haeq.
  - intros t x Haeq. inversion Haeq; subst.
    + exists z, t1. reflexivity.
    + exists z, t1. reflexivity.
  - intros t x Haeq. inversion Haeq.
  - intros t x Haeq. inversion Haeq.
Qed.


Lemma aeq_n_abs2: forall t t' x y, n_abs x t =a n_abs y t' -> t =a (swap x y t').
Proof.
  intros t t' x y H. case (x == y).
  - intro Heq. subst. rewrite swap_id. inversion H; subst.
    + assumption.
    + contradiction.
  - intro Hneq. inversion H; subst.
    + contradiction.
    + rewrite (swap_symmetric _ x y). assumption.
Qed.

Lemma eq_aeq: forall t u, t = u -> t =a u.
Proof.
  intros t u H; rewrite H; apply aeq_refl.
Qed.

Lemma aeq_size: forall t1 t2, t1 =a t2 -> size t1 = size t2.
Proof.
  induction 1.
  - reflexivity.
  - simpl. rewrite IHaeq; reflexivity.
  - simpl. rewrite IHaeq. rewrite swap_size_eq. reflexivity.
  - simpl. rewrite IHaeq1. rewrite IHaeq2. reflexivity.
  - simpl. rewrite IHaeq1. rewrite IHaeq2. reflexivity.
  - simpl. rewrite IHaeq1. rewrite IHaeq2. rewrite swap_size_eq. reflexivity.
Qed.

Lemma swap_remove_reduction: forall x y t, remove x (remove y (fv_nom (swap y x t))) [=] remove x (remove y (fv_nom t)).
Proof.
  induction t as [z | z t1 | t1 IHt1 t2 IHt2 | t1 IHt1 z t2 IHt2 ].
  - rewrite remove_symmetric. simpl. unfold vswap. destruct (z == y).
    +  subst. repeat rewrite remove_singleton_empty. repeat rewrite remove_empty. reflexivity.
    + destruct (z == x).
      * subst. rewrite remove_symmetric. rewrite remove_singleton_empty. rewrite remove_symmetric. rewrite remove_singleton_empty. repeat rewrite remove_empty. reflexivity.
      * rewrite remove_symmetric. reflexivity.
  - simpl. unfold vswap. destruct (z == y).
    +  subst. rewrite double_remove. rewrite remove_symmetric. rewrite double_remove. rewrite remove_symmetric. assumption.
    + destruct (z == x).
      * subst. rewrite double_remove. symmetry. rewrite remove_symmetric. rewrite double_remove. rewrite remove_symmetric. symmetry. assumption.
      * rewrite (remove_symmetric y z _). rewrite (remove_symmetric x z _). rewrite IHt1. rewrite (remove_symmetric y z _). symmetry. rewrite (remove_symmetric x z _). reflexivity.
  - simpl. repeat rewrite remove_union_distrib. apply Equal_union_compat.
    + assumption.
    + assumption.
  - simpl. unfold vswap. destruct (z == y).
    + subst. repeat rewrite remove_union_distrib. apply Equal_union_compat.
      * rewrite remove_symmetric. repeat rewrite double_remove. rewrite remove_symmetric. assumption.
      * assumption.
    + repeat rewrite remove_union_distrib. apply Equal_union_compat.
      * destruct (z == x).
        ** subst. symmetry. rewrite (remove_symmetric x y _). repeat rewrite double_remove. rewrite remove_symmetric. symmetry. assumption.
        ** rewrite (remove_symmetric y z _). rewrite (remove_symmetric x z _). rewrite IHt1. rewrite (remove_symmetric z x _). rewrite (remove_symmetric z y _). reflexivity.
      * assumption. 
Qed.

Lemma remove_fv_swap: forall x y t, x `notin` fv_nom t -> remove x (fv_nom (swap y x t)) [=] remove y (fv_nom t).
Proof. 
  intros x y t. induction t.
  - intro Hfv. simpl in *. apply notin_singleton_1 in Hfv. unfold vswap. case (x0 == y).
    + intro Heq. subst. apply remove_singleton.
    + intro Hneq. case (x0 == x).
      * intro Heq. contradiction.
      * intro Hneq'. rewrite AtomSetProperties.remove_equal.
        ** rewrite AtomSetProperties.remove_equal.
           *** reflexivity.
           *** apply notin_singleton_2; assumption.
        ** apply notin_singleton_2; assumption.
  - intros Hfv. simpl in *. apply notin_remove_1 in Hfv. destruct Hfv.
    + subst. assert (H: vswap y x x = y).
      {
        unfold vswap. destruct (x == y).
        - assumption.
        - rewrite eq_dec_refl. reflexivity.
      }
      rewrite H. rewrite remove_symmetric. rewrite swap_symmetric. apply swap_remove_reduction.
    + unfold vswap. destruct (x0 == y).
      * subst. repeat rewrite double_remove. apply IHt. assumption.
      * destruct (x0 == x).
        ** subst. rewrite remove_symmetric. rewrite swap_symmetric. apply swap_remove_reduction.
        ** rewrite remove_symmetric. assert (Hr: remove y (remove x0 (fv_nom t)) [=] remove x0 (remove y (fv_nom t))).
           {
           rewrite remove_symmetric. reflexivity.
           }
           rewrite Hr. clear Hr. apply AtomSetProperties.Equal_remove. apply IHt. assumption.
  - intro Hfv. simpl in *. pose proof Hfv as Hfv'. apply notin_union_1 in Hfv'. apply notin_union_2 in Hfv.
    apply IHt1 in Hfv'. apply IHt2 in Hfv. pose proof remove_union_distrib as H1. pose proof H1 as H2.
    specialize (H1 (fv_nom (swap y x t1)) (fv_nom (swap y x t2)) x). specialize (H2 (fv_nom t1) (fv_nom t2) y). rewrite Hfv' in H1. rewrite Hfv in H1. rewrite H1. rewrite H2. reflexivity.
  - intro Hfv. simpl in *. pose proof Hfv as Hfv'. apply notin_union_1 in Hfv'. apply notin_union_2 in Hfv.
    pose proof remove_union_distrib as H1. pose proof H1 as H2.
    specialize (H1 (remove (vswap y x x0) (fv_nom (swap y x t1))) (fv_nom (swap y x t2)) x). rewrite H1.
    specialize (H2 (remove x0 (fv_nom t1)) (fv_nom t2) y). rewrite H2. apply Equal_union_compat.
    + unfold vswap. case (x0 == y); intros; subst.
      unfold vswap in H1. rewrite eq_dec_refl in H1. rewrite double_remove in *. apply IHt2 in Hfv. case (x == y); intros; subst.
      * repeat rewrite swap_id in *. rewrite double_remove. reflexivity.
      * rewrite double_remove. apply IHt1. apply diff_remove_2 in Hfv'.
        ** assumption.
        ** assumption.
      * destruct (x0 == x).
        ** subst. rewrite remove_symmetric. rewrite swap_symmetric. apply swap_remove_reduction.
        ** subst. rewrite remove_symmetric. assert (Hr: remove y (remove x0 (fv_nom t1)) [=] remove x0 (remove y (fv_nom t1))).
           {
           rewrite remove_symmetric. reflexivity.
           }
           rewrite Hr. clear Hr. apply AtomSetProperties.Equal_remove. apply IHt1. apply diff_remove_2 in Hfv'.
            *** assumption.
            *** auto.
    + apply IHt2. apply Hfv.
Qed.

Lemma aeq_fv_nom : forall t1 t2, t1 =a t2 -> fv_nom t1 [=] fv_nom t2.
Proof.
  induction 1.
  - reflexivity.
  - simpl. rewrite IHaeq. reflexivity.
  - simpl. inversion H1; subst; rewrite IHaeq; apply remove_fv_swap; assumption.
  - simpl. rewrite IHaeq1; rewrite IHaeq2. reflexivity.
  - simpl. rewrite IHaeq1; rewrite IHaeq2. reflexivity.
  - simpl. pose proof remove_fv_swap. specialize (H3 x y t1'). apply H3 in H1. inversion H2; subst; rewrite IHaeq1; rewrite IHaeq2; rewrite H1; reflexivity.
Qed.

Lemma notin_fv_nom_equivariance: forall t x' x y, x' `notin` fv_nom t -> vswap x y x'  `notin` fv_nom (swap x y t).
Proof.
  induction t as [z | z t1 | t1 IHt1 t2 IHt2 | t1 IHt1 z t2 IHt2 ].
  - intros x' x y Hfv. simpl in *. apply notin_singleton_1 in Hfv. apply notin_singleton. apply swap_neq. assumption.
  - intros x' x y H. simpl. simpl in H. apply notin_remove_1 in H. destruct H.
    + subst. apply notin_remove_3. reflexivity.
    + apply notin_remove_2. apply IHt1. assumption.
  - intros x' x y Hfv. simpl in *. apply notin_union. 
    + apply IHt1. apply notin_union_1 in Hfv. assumption.
    + apply IHt2. apply notin_union_2 in Hfv. assumption. 
  - intros x' x y Hfv. simpl in *. apply notin_union. 
    + apply notin_union_1 in Hfv. apply notin_remove_1 in Hfv. destruct Hfv. 
      * subst. apply notin_remove_3. reflexivity.
      * apply notin_remove_2. apply IHt1. assumption.
    + apply IHt2. apply notin_union_2 in Hfv. assumption. 
Qed.

Lemma in_fv_nom_equivariance : forall t x y z, z `in` fv_nom t -> vswap x y z `in` fv_nom (swap x y t).
Proof.
  induction t as [w | w t1 | t1 IHt1 t2 IHt2 | t1 IHt1 w t2 IHt2 ].
  - intros x y z Hin. simpl in *. unfold vswap. destruct (z == x) eqn: Hzx.
    + destruct (w == x) eqn: Hwx.
      * apply AtomSetImpl.singleton_2. reflexivity.
      * destruct (w == y) eqn: Hwy.
        ** subst. apply AtomSetImpl.singleton_1 in Hin. contradiction.
        ** apply AtomSetImpl.singleton_1 in Hin. subst. contradiction.
    + destruct (z == y) eqn: Hzy.
      * destruct (w == x) eqn: Hwx.
        ** subst. apply AtomSetImpl.singleton_1 in Hin. symmetry in Hin. contradiction.
        ** destruct (w == y) eqn: Hwy.
           *** subst.  apply AtomSetImpl.singleton_2. reflexivity.
           *** subst. apply AtomSetImpl.singleton_1 in Hin. contradiction.
      * destruct (w == x) eqn: Hwx.
        ** subst. apply AtomSetImpl.singleton_1 in Hin. symmetry in Hin. contradiction.
        ** destruct (w == y) eqn: Hwy.
           *** subst.  apply AtomSetImpl.singleton_1 in Hin. symmetry in Hin. contradiction.
           *** assumption.
  - intros x y z Hin. unfold vswap. destruct (z == x) eqn: Hzx.
    + simpl in *. unfold vswap. destruct (w == x) eqn: Hwx.
      * subst. apply remove_iff in Hin. destruct Hin as [Hin H]. contradiction.
      * destruct (w == y) eqn: Hwy.
        ** subst. apply AtomSetImpl.remove_2.
           *** apply aux_not_equal. assumption.
           *** replace y with (vswap x y x) at 1.
               **** apply IHt1. apply AtomSetImpl.remove_3 in Hin. assumption.
               **** unfold vswap. rewrite eq_dec_refl. reflexivity.
        ** subst. apply AtomSetImpl.remove_2.
           *** assumption.
           *** replace y with (vswap x y x) at 1.
               **** apply IHt1. apply AtomSetImpl.remove_3 in Hin. assumption.
               **** unfold vswap. rewrite eq_dec_refl. reflexivity.
    + destruct (z == y) eqn: Hzy.
      * simpl in *. unfold vswap. destruct (w == x) eqn: Hwx.
        ** subst. apply AtomSetImpl.remove_2.
           *** assumption.
           *** replace x with (vswap x y y) at 1.
               **** apply IHt1. apply AtomSetImpl.remove_3 in Hin. assumption.
               **** unfold vswap. rewrite eq_dec_refl. destruct (y == x).
                    ***** contradiction.
                    ***** reflexivity.
        ** destruct (w == y) eqn: Hwy.
           *** subst. apply remove_iff in Hin. destruct Hin as [Hin H]. contradiction.
           *** subst. apply remove_iff in Hin. destruct Hin as [Hin H]. apply remove_iff. split.
               **** replace x with (vswap x y y) at 1.
               ***** apply IHt1. assumption.
               ***** unfold vswap. rewrite eq_dec_refl. destruct (y == x).
                    ****** contradiction.
                    ****** reflexivity.
               **** assumption.
      * simpl in *. unfold vswap. destruct (w == x) eqn: Hwx.
        ** subst. apply remove_iff. split.
           *** apply remove_iff in Hin. destruct Hin as [Hin H]. replace z with (vswap x y z) at 1.
               **** apply IHt1. assumption.
               **** unfold vswap. rewrite Hzx. rewrite Hzy. reflexivity.
           *** apply aux_not_equal. assumption.
        ** destruct (w == y) eqn: Hwy.
           *** subst. apply remove_iff in Hin. destruct Hin as [Hin H]. apply remove_iff. split.
               **** replace z with (vswap x y z) at 1.
                    ***** apply IHt1. assumption.
                    ***** unfold vswap. rewrite Hzx. rewrite Hzy. reflexivity.
               **** apply aux_not_equal. assumption.
           *** apply remove_iff in Hin. destruct Hin as [Hin H]. apply remove_iff. split.
               **** replace z with (vswap x y z) at 1.
                    ***** apply IHt1. assumption.
                    ***** unfold vswap. rewrite Hzx. rewrite Hzy. reflexivity.
               **** assumption.
  - intros x y z Hin. simpl in *. apply AtomSetImpl.union_1 in Hin. destruct Hin as [Hin | Hin].
    + apply AtomSetImpl.union_2. apply IHt1. assumption.
    + apply AtomSetImpl.union_3. apply IHt2. assumption.
  - intros x y z Hin. simpl in *. apply AtomSetImpl.union_1 in Hin. destruct Hin as [Hin | Hin].
    + apply AtomSetImpl.union_2. unfold vswap. destruct (z == x) eqn: Hzx.
      * simpl in *. unfold vswap. destruct (w == x) eqn: Hwx.
        ** subst. apply remove_iff in Hin. destruct Hin as [Hin H]. contradiction.
        ** destruct (w == y) eqn: Hwy.
           *** subst. apply AtomSetImpl.remove_2.
               **** apply aux_not_equal. assumption.
               **** replace y with (vswap x y x) at 1.
                    ***** apply IHt1. apply AtomSetImpl.remove_3 in Hin. assumption.
                    ***** unfold vswap. rewrite eq_dec_refl. reflexivity.
           *** subst. apply AtomSetImpl.remove_2.
               **** assumption.
               **** replace y with (vswap x y x) at 1.
                    ***** apply IHt1. apply AtomSetImpl.remove_3 in Hin. assumption.
                    ***** unfold vswap. rewrite eq_dec_refl. reflexivity.
      * destruct (z == y) eqn: Hzy.
        ** simpl in *. unfold vswap. destruct (w == x) eqn: Hwx.
           *** subst. apply AtomSetImpl.remove_2.
               **** assumption.
               **** replace x with (vswap x y y) at 1.
                    ***** apply IHt1. apply AtomSetImpl.remove_3 in Hin. assumption.
                    ***** unfold vswap. rewrite eq_dec_refl. destruct (y == x).
                    ****** contradiction.
                    ****** reflexivity.
           *** destruct (w == y) eqn: Hwy.
               **** subst. apply remove_iff in Hin. destruct Hin as [Hin H]. contradiction.
               **** subst. apply remove_iff in Hin. destruct Hin as [Hin H]. apply remove_iff. split.
                    ***** replace x with (vswap x y y) at 1.
                    ****** apply IHt1. assumption.
                    ****** unfold vswap. rewrite eq_dec_refl. destruct (y == x).
                    ******* contradiction.
                    ******* reflexivity.
                    ***** assumption.
        ** simpl in *. unfold vswap. destruct (w == x) eqn: Hwx.
           *** subst. apply remove_iff. split.
               **** apply remove_iff in Hin. destruct Hin as [Hin H]. replace z with (vswap x y z) at 1.
                    ***** apply IHt1. assumption.
                    ***** unfold vswap. rewrite Hzx. rewrite Hzy. reflexivity.
               **** apply aux_not_equal. assumption.
           *** destruct (w == y) eqn: Hwy.
               **** subst. apply remove_iff in Hin. destruct Hin as [Hin H]. apply remove_iff. split.
                    ***** replace z with (vswap x y z) at 1.
                    ****** apply IHt1. assumption.
                    ****** unfold vswap. rewrite Hzx. rewrite Hzy. reflexivity.
                    ***** apply aux_not_equal. assumption.
               **** apply remove_iff in Hin. destruct Hin as [Hin H]. apply remove_iff. split.
                    ***** replace z with (vswap x y z) at 1.
                    ****** apply IHt1. assumption.
                    ****** unfold vswap. rewrite Hzx. rewrite Hzy. reflexivity.
                    ***** assumption.
    +  apply AtomSetImpl.union_3. apply IHt2. assumption.
Qed.

Lemma aeq_pure: forall t1 t2, t1 =a t2 -> pure t1 -> pure t2.
Proof.
  intros t1 t2 Haeq Hpure. induction Haeq.
  - assumption.
  - apply pure_abs. apply IHHaeq. inversion Hpure; subst. assumption.
  - apply pure_abs. apply (pure_swap_2 _ y x). apply IHHaeq. inversion Hpure; subst. assumption.
  - inversion Hpure; subst. apply pure_app.
    + apply IHHaeq1; assumption.
    + apply IHHaeq2; assumption.
  - inversion Hpure.
  - inversion Hpure.
Qed.

Lemma notin_fv_nom_remove_swap: forall t x' x y, vswap x y x' `notin` fv_nom (swap x y t) -> x' `notin` fv_nom t.
Proof.
  induction t as [z | z t1 | t1 IHt1 t2 IHt2 | t1 IHt1 z t2 IHt2 ].
  - intros x' x y Hfv. simpl in *. apply notin_singleton_1 in Hfv. apply notin_singleton. intro Hneq. subst. contradiction.
  - intros x' x y Hfv. simpl in *. apply notin_remove_1 in Hfv. destruct Hfv.
    + apply swap_eq in H. subst. apply notin_remove_3. reflexivity.
    + apply notin_remove_2. apply IHt1 with x y. assumption.
  - intros x' x y Hfv. simpl in *. apply notin_union.
    + apply IHt1 with x y. apply notin_union_1 in Hfv. assumption.
    + apply IHt2 with x y. apply notin_union_2 in Hfv. assumption.
  - intros x' x y Hfv. simpl in *. apply notin_union.
    + apply notin_union_1 in Hfv. case (x' == z).
      * intro Heq. subst. apply notin_remove_3. reflexivity.
      * intro Hneq. apply notin_remove_1 in Hfv. destruct Hfv.
        ** apply swap_eq in H. symmetry in H. contradiction.
        ** apply notin_remove_2. apply IHt1 with x y. assumption.
    + apply IHt2 with x y. apply notin_union_2 in Hfv. assumption.
Qed.  

Lemma aeq_swap1: forall t1 t2 x y, t1 =a t2 -> (swap x y t1) =a (swap x y t2).
Proof.
  induction 1.
  - apply aeq_refl.
  - simpl. apply aeq_abs_same. assumption.
  - simpl. apply (swap_neq x y) in H. apply aeq_abs_diff.
    + assumption.
    + apply notin_fv_nom_equivariance. assumption.
    + rewrite <- swap_equivariance. apply IHaeq.
  - simpl. apply aeq_app; assumption.
  - simpl. apply aeq_sub_same; assumption.
  - simpl. apply (swap_neq x y) in H0. apply aeq_sub_diff.
    + assumption.
    + assumption.
    + apply notin_fv_nom_equivariance. assumption.
    + rewrite <- swap_equivariance. apply IHaeq2.
Qed.

Lemma aeq_swap2: forall t1 t2 x y, (swap x y t1) =a (swap x y t2) -> t1 =a t2.
Proof.
  induction t1 as [z | z t1' | t1' IHt1' t2 IHt2 | t1' IHt1' z t2 IHt2 ].
  - intros t2 x y H. apply (aeq_swap1 _ _ x y) in H. repeat rewrite swap_involutive in H. assumption.
  - intros t2 x y H. apply (aeq_swap1 _ _ x y) in H. repeat rewrite swap_involutive in H. assumption.
  - intros t x y H. simpl in *. apply (aeq_swap1 _ _ x y) in H. simpl in H. repeat rewrite swap_involutive in H. assumption.
  - intros t x y H. apply (aeq_swap1 _ _ x y) in H. repeat rewrite swap_involutive in H. assumption.
Qed.
(* end hide *)
(**

The key point of the nominal approach is that the swap operation is stable under $\alpha$-equivalence in the sense that, $t_1 =_\alpha t_2$ if, and only if $\swap{x}{y}{t_1} =_\alpha \swap{x}{y}{t_2}, \forall t_1, t_2, x, y$, while the metasubstitution is not. The following corollary stablishes this result in Coq:

 *)

Corollary aeq_swap: forall t1 t2 x y, t1 =a t2 <-> (swap x y t1) =a (swap x y t2).
Proof.
  intros t1 t2 x y. split.
  - apply aeq_swap1.
  - apply aeq_swap2.
Qed.

(**

In order to see that metasubstitution is not stable under $\alpha$-equivalence, note that if $x \neq y$ then we have that $\metasub{x}{x}{y} =_\alpha \metasub{y}{x}{y}$ but $x \neq_\alpha y$.

*)
(* begin hide *)
Lemma aeq_abs_notin: forall t1 t2 x y, x <> y ->  n_abs x t1 =a n_abs y t2 -> x `notin` fv_nom t2.
Proof.
  intros t1 t2 x y Hneq Haeq. inversion Haeq; subst.
  - contradiction.
  - assumption.
Qed.


Lemma var_diff: forall t x y, x`notin` fv_nom t -> y `in` fv_nom t -> x <> y.
Proof.
  intros. destruct (x == y).
   - subst. contradiction.
   - assumption. 
Qed.

Lemma fv_nom_swap : forall z y t, z `notin` fv_nom t -> y `notin` fv_nom (swap y z t).
Proof.
  induction t; intros; simpl; unfold vswap; default_simp.
Qed.

Lemma fv_nom_swap_2 : forall z y t, z `notin` fv_nom (swap y z t) -> y `notin` fv_nom t.
Proof.
  intros. induction t; simpl in *; unfold vswap in H; default_simp.
Qed.

Lemma fv_nom_swap_remove: forall t x y y0, x <> y ->  x <> y0 -> x `notin` fv_nom (swap y0 y t) -> x `notin` fv_nom t.
Proof.
  intros. induction t; simpl in *; unfold vswap in *; default_simp.
Qed.
    
Lemma fv_nom_remove_swap: forall t x y y0, x <> y ->  x <> y0 -> x `notin` fv_nom t -> x `notin` fv_nom (swap y0 y t).
  Proof.
    induction t; simpl in *; unfold vswap; default_simp.
Qed.

Lemma fv_nom_remove_swap_inc: forall t x y, x <> y -> y `notin` fv_nom t -> x `notin` fv_nom (swap x y t).
Proof.
  induction t as [z | z t1 | t1 IHt1 t2 IHt2 | t1 IHt1 z t2 IHt2 ].
  - intros x y Hneq Hnotin. simpl in *. apply notin_singleton_1 in Hnotin. unfold vswap. destruct (z == x).
    + apply notin_singleton. apply aux_not_equal. assumption.
    + destruct (z == y).
      * contradiction.
      * apply notin_singleton. assumption.
  - intros x y Hneq Hnotin. simpl in *. apply notin_remove_1 in Hnotin. destruct Hnotin as [Heq | Hnotin].
    + subst. unfold vswap. destruct (y == x).
      * symmetry in e. contradiction.
      * rewrite eq_dec_refl. apply notin_remove_3. reflexivity.
    + unfold vswap. destruct (z == x).
      * apply notin_remove_2. apply IHt1; assumption.
      * destruct (z == y).
        ** apply notin_remove_3. reflexivity.
        ** apply notin_remove_2. apply IHt1; assumption.
  - intros x y Hneq Hnotin. simpl in *. apply notin_union.
    + apply IHt1.
      * assumption.
      * apply notin_union_1 in Hnotin; assumption.
    + apply IHt2.
      * assumption.
      * apply notin_union_2 in Hnotin. assumption.
  - intros x y Hneq Hnotin. simpl in *. apply notin_union.
    + apply notin_union_1 in Hnotin. apply notin_remove_1 in Hnotin. destruct Hnotin as [Heq | Hnotin].
      * subst. unfold vswap. destruct (y == x).
        ** symmetry in e. contradiction.
        ** rewrite eq_dec_refl. apply notin_remove_3. reflexivity.
      * apply notin_remove_2. apply IHt1; assumption.
    + apply notin_union_2 in Hnotin. apply IHt2; assumption.
Qed.
  
Example swap1 : forall x y z, x <> z -> y <> z -> swap x y (n_abs z (n_app (n_var x)(n_var y))) = n_abs z (n_app (n_var y) (n_var x)).
Proof.
  intros. simpl; unfold vswap; default_simp.
Qed.

Example swap2 : forall x y, x <> y -> swap x y (n_abs x (n_var x)) = n_abs y (n_var y).
Proof.
  intros. simpl; unfold vswap; default_simp.
Qed.

Example swap3 : forall x y, x <> y -> swap x y (n_abs y (n_var x)) = n_abs x (n_var y).
Proof.
  intros. simpl; unfold vswap; default_simp.
Qed.

Lemma diff_equal: forall s s' t, s [=] s' -> AtomSetImpl.diff s t [=] AtomSetImpl.diff s' t.
Proof.
intros. rewrite H. reflexivity.
Qed.

Lemma swap_symmetric_2: forall x y x' y' t,
    x <> x' -> y <> y' -> x <> y'-> y <> x' -> swap x y (swap x' y' t) = swap x' y' (swap x y t). 
Proof.
  intros. induction t; simpl in *; unfold vswap in *; default_simp.
Qed.

Lemma aeq_sym: forall t1 t2, t1 =a t2 -> t2 =a t1.
Proof.
  induction 1.
  - apply aeq_refl.
  - apply aeq_abs_same; assumption.
  - apply aeq_abs_diff.
    + apply aux_not_equal; assumption.
    + apply fv_nom_swap with x y t2 in H0. apply aeq_fv_nom in H1. rewrite H1; assumption.
    + apply aeq_swap2 with x y. rewrite swap_involutive. rewrite swap_symmetric. assumption.
  - apply aeq_app; assumption.
  - apply aeq_sub_same; assumption.
  - apply aeq_sub_diff.
    + assumption.
    + apply aux_not_equal. assumption.
    + apply aeq_fv_nom in H2. rewrite H2. apply fv_nom_swap. assumption.
    + rewrite swap_symmetric. apply aeq_swap2 with y x. rewrite swap_involutive. assumption.
Qed.

Lemma aeq_abs: forall t x y, y `notin` fv_nom t -> (n_abs y (swap x y t)) =a (n_abs x t).
Proof.
  intros t x y H. case (x == y). 
  - intro Heq. subst. rewrite swap_id. apply aeq_refl.
  - intro Hneq. apply aeq_abs_diff.
    + apply aux_not_equal. assumption.
    + assumption.
    + apply aeq_refl.
Qed.

Lemma swap_reduction: forall t x y, x `notin` fv_nom t -> y `notin` fv_nom t -> (swap x y t) =a  t.
Proof. 
  induction t as [z | z t1 | t1 IHt1 t2 IHt2 | t1 IHt1 z t2 IHt2 ].
  - intros x y H1 H2. simpl in *. unfold vswap. destruct (z == x). 
    + subst. apply notin_singleton_is_false in H1. contradiction.
    + destruct (z == y). 
      * subst. apply notin_singleton_is_false in H2. contradiction. 
      * apply aeq_refl.
  - intros x y H1 H2. simpl in *. unfold vswap. apply notin_remove_1 in H1. apply notin_remove_1 in H2. destruct H1.
    + subst. rewrite eq_dec_refl. destruct H2.
      * subst. rewrite swap_id. apply aeq_refl.
      * apply aeq_abs; assumption.
    + destruct (z == x).
      * subst. destruct H2.
        ** subst. rewrite swap_id. apply aeq_refl.
        ** apply aeq_abs; assumption.
      * destruct H2.
        ** subst. rewrite eq_dec_refl. rewrite swap_symmetric. apply aeq_abs; assumption.
        ** destruct (z == y).
           *** subst. rewrite swap_symmetric. apply aeq_abs; assumption.
           *** apply aeq_abs_same. apply IHt1; assumption.
  - intros x y H1 H2. simpl in *. assert (H1' := H1). apply notin_union_1 in H1. apply notin_union_2 in H1'. assert (H2' := H2).  apply notin_union_1 in H2. apply notin_union_2 in H2'. apply aeq_app.
    + apply IHt1; assumption.
    + apply IHt2; assumption.
  - intros x y H1 H2. simpl in *. assert (H1' := H1). apply notin_union_1 in H1. apply notin_union_2 in H1'. assert (H2' := H2). apply notin_union_1 in H2. apply notin_union_2 in H2'. apply notin_remove_1 in H1. apply notin_remove_1 in H2. unfold vswap. destruct H1.
    + subst. rewrite eq_dec_refl. destruct H2.
      * subst. repeat rewrite swap_id. apply aeq_refl.
      * case (x == y). 
        ** intro Heq. subst. repeat rewrite swap_id. apply aeq_refl.
        ** intro Hneq. apply aeq_sub_diff.
           *** apply IHt2; assumption.
           *** apply aux_not_equal; assumption.
           *** assumption.
           *** apply aeq_refl.
    + destruct (z == x).
      * subst. destruct H2.
        ** subst. repeat rewrite swap_id. apply aeq_refl.
        ** case (x == y). 
           *** intro Heq. subst. repeat rewrite swap_id. apply aeq_refl.
           *** intro Hneq. apply aeq_sub_diff.
           **** apply IHt2; assumption.
           **** apply aux_not_equal; assumption.
           **** assumption.
           **** apply aeq_refl.
      * destruct H2.
        ** subst. rewrite eq_dec_refl. apply aeq_sub_diff.
           *** apply IHt2; assumption.
           *** apply aux_not_equal; assumption.
           *** assumption.
           *** rewrite swap_symmetric. apply aeq_refl.            
        ** destruct (z == y).
           *** subst. apply aeq_sub_diff.
               **** apply IHt2; assumption.
               **** apply aux_not_equal; assumption.
               **** assumption.
               **** rewrite swap_symmetric. apply aeq_refl.
           *** apply aeq_sub_same.
               **** apply IHt1; assumption.
               **** apply IHt2; assumption.
Qed.

Lemma aeq_diff_abs: forall x y t1 t2, (n_abs x t1) =a (n_abs y t2) -> t1 =a (swap x y t2).
Proof.
  intros x y t1 t2 H. inversion H; subst.
  - rewrite swap_id; assumption.
  - rewrite swap_symmetric; assumption.
Qed.

Corollary aeq_same_abs: forall x t1 t2, n_abs x t1 =a n_abs x t2 -> t1 =a t2.
Proof.
  intros x t1 t2 H. pose proof aeq_diff_abs as H'.  specialize (H' x x t1 t2). rewrite swap_id in H'. apply H'; assumption.
Qed.

Lemma aeq_diff_sub: forall x y t1 t1' t2 t2', (n_sub t1 x t2) =a (n_sub t1' y t2') -> t1 =a (swap x y t1') /\ t2 =a t2'.
Proof.
  intros x y t1 t1' t2 t2' H. inversion H; subst.
  - split.
    + rewrite swap_id; assumption.
    + assumption.
  - split.
    + rewrite swap_symmetric; assumption.
    + assumption.
Qed.

Corollary aeq_same_sub: forall x t1 t1' t2 t2', (n_sub t1 x t2) =a (n_sub t1' x t2') -> t1 =a t1' /\ t2 =a t2'.
Proof.
  intros x t1 t1' t2 t2' H. pose proof aeq_diff_sub as H'. specialize (H' x x t1 t1' t2 t2'). rewrite swap_id in H'. apply H'; assumption.
Qed.

Lemma aeq_sub: forall t1 t2 x y, y `notin` fv_nom t1 -> (n_sub (swap x y t1) y t2) =a (n_sub t1 x t2).
Proof.
  intros t1 t2 x y H. case (x == y). 
  - intro Heq. subst. rewrite swap_id; apply aeq_refl.
  - intro Hneq. apply aeq_sub_diff.
    + apply aeq_refl.
    + apply aux_not_equal; assumption.
    + assumption.
    + apply aeq_refl.
Qed.

Lemma aeq_swap_swap: forall t x y z, z `notin` fv_nom t -> x `notin` fv_nom t -> (swap z x (swap x y t)) =a (swap z y t).
Proof.
  intros t x y z Hfv Hfv'. case (z == y). 
  - intro Heq. subst. rewrite swap_id. rewrite (swap_symmetric _ y x). rewrite swap_involutive. apply aeq_refl. 
  - intro Hneq. case (x == y). 
    + intro Heq. subst. rewrite swap_id. apply aeq_refl. 
    + intro Hneq'. rewrite shuffle_swap. 
      * apply aeq_swap. apply swap_reduction; assumption.
      * assumption.
      * assumption.
Qed. 

Lemma aeq_trans: forall t1 t2 t3, t1 =a t2 -> t2 =a t3 -> t1 =a t3.
Proof.
  induction t1 as [x | t11 x | t11 t12 | t11 t12 x] using n_sexp_induction.
  - intros t2 t3 H1 H2. inversion H1; subst. assumption.
  - intros t2 t3 H1 H2. inversion H1; subst.
    + inversion H2; subst.
      * apply aeq_abs_same. replace t11 with (swap x x t11).
        ** apply H with t0.
           *** rewrite swap_id; reflexivity.
           *** rewrite swap_id; assumption.
           *** assumption.
        ** apply swap_id.
      * apply aeq_abs_diff.
        ** assumption.
        ** assumption.
        ** apply aeq_sym.
           apply H with t0.
           *** apply eq_trans with (size t0).
               **** apply aeq_size in H8. symmetry; assumption.
               **** apply aeq_size in H5. symmetry; assumption.
           *** apply aeq_sym; assumption.
           *** apply aeq_sym; assumption.
    + inversion H2; subst.
      * apply aeq_abs_diff.
        ** assumption.
        ** apply aeq_fv_nom in H8. rewrite <- H8; assumption. 
        ** apply aeq_sym. apply H with (swap y x t0).
           *** apply eq_trans with (size t0).
               **** apply aeq_size in H8. rewrite swap_size_eq. symmetry; assumption.
               **** apply aeq_size in H7. rewrite H7. rewrite swap_size_eq. reflexivity.
           *** apply aeq_sym. apply aeq_swap1; assumption.
           *** apply aeq_sym; assumption.
      * case (x == y0).
        ** intro Heq; subst. apply aeq_abs_same. apply (aeq_swap1 _ _  y0 y) in H10. rewrite swap_involutive in H10. apply aeq_sym. replace t2 with (swap y y t2).
           *** apply H with (swap y0 y t0).
               **** apply aeq_size in H7. rewrite  H7. apply aeq_size in H10. rewrite swap_id. symmetry. rewrite swap_symmetric. assumption.
               **** apply aeq_sym. rewrite swap_id; assumption.
               **** apply aeq_sym. rewrite swap_symmetric; assumption.
           *** apply swap_id.             
        ** intro Hneq. apply aeq_fv_nom in H10. assert (H5' := H5). rewrite H10 in H5'. apply fv_nom_swap_remove in H5'.           
           *** apply aeq_abs_diff.
               **** assumption.
               **** assumption.
               **** apply aeq_sym. apply H with (swap y x t0).
                    ***** apply aeq_size in H1. apply aeq_size in H2. simpl in *. inversion H1; subst. inversion H2; subst. symmetry. rewrite swap_size_eq. apply eq_trans with (size t0); assumption.
                    ***** inversion H2; subst.
                    ****** apply aeq_swap. apply aeq_sym; assumption.
                    ****** apply (aeq_swap _ _ y x). rewrite swap_involutive. rewrite (swap_symmetric _ y0 x). apply H with (swap y0 y t2).
                    ******* apply aeq_size in H7. rewrite swap_size_eq in *. rewrite H7. apply aeq_size in H14. rewrite swap_size_eq in *. symmetry; assumption.
                    ******* rewrite (swap_symmetric _  y0 y). apply aeq_swap_swap; assumption.
                    ******* apply aeq_sym. assumption.
                    ***** apply aeq_sym; assumption.
           *** assumption.
           *** assumption.
  - intros t2 t3 H1 H2. inversion H1; subst. inversion H2; subst. apply aeq_app. 
    + apply IHt12 with t1'; assumption. 
    + apply IHt1_1 with t2'; assumption. 
  - intros t2 t3 H1 H2. inversion H1; subst.
    + inversion H2; subst.
      * apply aeq_sub_same.
        ** apply H with t1'.
           *** reflexivity.
           *** assumption.
           *** assumption.
        ** apply IHt1_1 with t2'; assumption.
      * apply aeq_sub_diff.
        ** apply IHt1_1 with t2'; assumption.
        ** assumption.
        ** assumption.
        ** apply H with t1'.
           *** reflexivity.
           *** assumption.
           *** assumption.
    + inversion H2; subst.            
      * apply aeq_sub_diff.
        ** apply IHt1_1 with t2'; assumption.
        ** assumption.
        ** apply aeq_fv_nom in H10. rewrite H10 in H8. assumption.
        ** apply (aeq_swap _ _  y x) in H10. apply H with (swap y x t1').
           *** reflexivity.
           *** assumption.
           *** assumption.
      * case (x == y0). 
        ** intro Heq. subst. apply aeq_sub_same.
           *** apply (aeq_swap _ _ y0 y). apply H with t1'.
               **** rewrite swap_size_eq. reflexivity.
               **** apply (aeq_swap _ _ y0 y). rewrite swap_involutive. rewrite (swap_symmetric _ y0 y). assumption.
               **** assumption.
           *** apply IHt1_1 with t2'; assumption.
        ** intro Hneq. apply aeq_sub_diff.
           *** apply IHt1_1 with t2'; assumption.
           *** assumption.
           *** apply aeq_fv_nom in H13. rewrite H13 in H8. apply fv_nom_swap_remove in H8.
               **** assumption.
               **** assumption.
               **** assumption.
           *** apply (aeq_swap _ _ y x). apply H with t1'.
               **** rewrite swap_size_eq. reflexivity.
               ****  apply (aeq_swap _ _ y x). rewrite swap_involutive. assumption.
               **** apply aeq_sym. apply H with (swap y y0 t1'0).
                    ***** apply aeq_size in H9. rewrite swap_size_eq in *. rewrite H9. apply aeq_size in H13. rewrite H13. repeat rewrite swap_size_eq. reflexivity.
                    ***** rewrite (swap_symmetric _ y0 x). apply aeq_swap_swap.
                    ****** assumption.
                    ****** apply aeq_fv_nom in H13. rewrite H13 in H8. apply fv_nom_swap_remove in H8; assumption.
                    ***** apply aeq_sym. rewrite (swap_symmetric _ y y0). assumption.
Qed.

Instance Equivalence_aeq: Equivalence aeq.
Proof.
  split.
  - unfold Reflexive. apply aeq_refl.
  - unfold Symmetric. apply aeq_sym.
  - unfold Transitive. apply aeq_trans.
Qed.
(* end hide *)
(**

As presented in introduction, the main operation of the $\lambda$-calculus is the $\beta$-reduction %(\ref{lambda:beta})% that expresses how to evaluate a function applied to an argument. The $\beta$-contractum $\metasub{t}{x}{u}$ represents a capture free in the sense that no free variable becomes bound by the application of the metasubstitution. This operation is in the meta level because it is outside the grammar of the $\lambda$-calculus. In textbooks %\cite{barendregtLambdaCalculusIts1984a}%, the metasubstition is usually defined  as follows:

%\vspace{.5cm}%
$\metasub{t}{x}{u} = \left\{
 \begin{array}{ll}
  u, & \mbox{ if } t = x; \\
  y, & \mbox{ if } t = y \mbox{ and } x \neq y; \\
  \metasub{t_1}{x}{u}\ \metasub{t_2}{x}{u}, & \mbox{ if } t = t_1\ t_2; \\
  \lambda_y.(\metasub{t_1}{x}{u}), & \mbox{ if } t = \lambda_y.t_1.
 \end{array}\right.$ %\vspace{.5cm}%

%\noindent% where it is assumed the so called _Barendregt's variable convention_:

%\begin{tcolorbox}
 If $t_1, t_2, \ldots, t_n$ occur in a certain mathematical context (e.g. definition, proof), then in these terms all bound variables are chosen to be different from the free variables.  
\end{tcolorbox}%

This means that we are assumming that both $x \neq y$ and $y\notin fv(u)$ in the case $t = \lambda_y.t_1$. This approach is very convenient in informal proofs because it avoids having to rename bound variables. In order to formalize the capture free substitution, %{\it i.e.}% the metasubstitution, there are different possible approaches. In our case, we rename bound variables whenever the metasubstitution is propagated inside a binder, %\emph{i.e.}% inside an abstraction or an explicit substitution.

In a formal framework, like a proof assistant, the implementation of Barendregt's variable is not trivial%\cite{urbanBarendregtsVariableConvention2007}%. In our approach, we rename bound variables whenever the metasubstitution needs to be propagated inside an abstraction or an explicit substitution:%\newline%
%\begin{equation}\label{msubst}
\metasub{t}{x}{u} = \left\{
 \begin{array}{ll}
  u, & \mbox{ if } t = x; \\
  y, & \mbox{ if } t = y\ (x \neq y); \\
  \metasub{t_1}{x}{u}\ \metasub{t_2}{x}{u}, & \mbox{ if } t = t_1\ t_2; \\
  \lambda_x.t_1, & \mbox{ if } t = \lambda_x.t_1; \\
  \lambda_z.(\metasub{(\swap{y}{z}{t_1})}{x}{u}), & \mbox{ if } t = \lambda_y.t_1, x \neq y \mbox{ and } z\notin fv(t)\cup fv(u) \cup \{x\}; \\
  \esub{t_1}{x}{\metasub{t_2}{x}{u}}, & \mbox{ if } t = \esub{t_1}{x}{t_2}; \\
  \esub{\metasub{(\swap{y}{z}{t_1})}{x}{u}}{z}{\metasub{t_2}{x}{u}}, & \mbox{ if } t = \esub{t_1}{y}{t_2}, x \neq y \mbox{ and } z\notin fv(t)\cup fv(u) \cup \{x\}.
 \end{array}\right.
\end{equation}%

%\noindent% and the corresponding Coq code is as follows:
 *)

(* begin hide *)
Require Import Recdef.
(* end hide *)

Function subst_rec_fun (t:n_sexp) (u :n_sexp) (x:atom) {measure size t} : n_sexp :=
  match t with
  | n_var y => if (x == y) then u else t
  | n_abs y t1 => if (x == y) then t else let (z,_) :=
    atom_fresh (fv_nom u `union` fv_nom t `union` {{x}}) in n_abs z (subst_rec_fun (swap y z t1) u x)
  | n_app t1 t2 => n_app (subst_rec_fun t1 u x) (subst_rec_fun t2 u x)
  | n_sub t1 y t2 => if (x == y) then n_sub t1 y (subst_rec_fun t2 u x) else let (z,_) :=
    atom_fresh (fv_nom u `union` fv_nom t `union` {{x}}) in
    n_sub (subst_rec_fun (swap y z t1) u x) z (subst_rec_fun t2 u x) end.
Proof.
 - intros. simpl. rewrite swap_size_eq. auto.
 - intros. simpl. lia.
 - intros. simpl. lia.
 - intros. simpl. lia.
 - intros. simpl. lia.
 - intros. simpl. rewrite swap_size_eq. lia.
Defined.

Definition m_subst (u : n_sexp) (x:atom) (t:n_sexp) := subst_rec_fun t u x.
Notation "{ x := u } t" := (m_subst u x t) (at level 60).
(* begin hide *)
Lemma m_subst_var_eq: forall u x, {x := u}(n_var x) = u.
Proof.
  intros u x. unfold m_subst. rewrite subst_rec_fun_equation. rewrite eq_dec_refl. reflexivity.
Qed.

Lemma m_subst_var_neq: forall u x y, x <> y -> {y := u}(n_var x) = n_var x.
Proof.
  intros u x y H. unfold m_subst. rewrite subst_rec_fun_equation. destruct (y == x) eqn:Hxy.
  - subst. contradiction.
  - reflexivity.
Qed.

Lemma m_subst_app: forall t1 t2 u x, {x := u}(n_app t1 t2) = n_app ({x := u}t1) ({x := u}t2).
Proof.
  intros t1 t2 u x. unfold m_subst. rewrite subst_rec_fun_equation. reflexivity.
Qed.

Lemma m_subst_abs_eq: forall u x t, {x := u}(n_abs x t) = n_abs x t.
Proof.
  intros u x t. unfold m_subst. rewrite subst_rec_fun_equation. rewrite eq_dec_refl. reflexivity.
Qed.

Lemma m_subst_sub_eq: forall u x t1 t2, {x := u}(n_sub t1 x t2) = n_sub t1 x ({x := u}t2).
Proof.
  intros u x t1 t2. unfold m_subst. rewrite subst_rec_fun_equation. rewrite eq_dec_refl. reflexivity.
Qed.

Lemma fv_nom_remove: forall t u x y, y `notin` fv_nom u -> y `notin` remove x (fv_nom t) -> y `notin` fv_nom ({x := u}t).
Proof.
    intros t u x y H0 H1. unfold m_subst. functional induction (subst_rec_fun t u x).
  - assumption.
  - apply notin_remove_1 in H1. destruct H1.
    + subst. simpl. apply notin_singleton. apply aux_not_equal; assumption.
    + assumption.
  - simpl in *. rewrite double_remove in H1. assumption.
  - simpl in *. case (y == z).
    + intro Heq. subst. apply notin_remove_3; reflexivity.
    + intro Hneq. apply notin_remove_2. apply IHn.
      * assumption.
      * apply notin_remove_1 in H1. destruct H1.
        ** subst. apply notin_remove_3; reflexivity.
        ** clear IHn e1 e0. case (y == x).
           *** intro Heq. subst. apply notin_remove_3; reflexivity.
           *** intro Hneq'. apply notin_remove_2. apply notin_remove_1 in H. destruct H.
               **** subst. apply fv_nom_swap. apply notin_union_2 in _x0. apply notin_union_1 in _x0. apply notin_remove_1 in _x0. destruct _x0.
                    ***** contradiction.
                    ***** assumption.
               **** case (y == y0).
                    ***** intro Heq. subst. apply fv_nom_swap. apply notin_union_2 in _x0. apply notin_union_1 in _x0. apply notin_remove_1 in _x0. destruct _x0.
                    ****** contradiction.
                    ****** assumption.
                    ***** intro Hneq''. apply fv_nom_remove_swap; assumption.
  - simpl in *. apply notin_union_3. 
    + apply IHn.
      * assumption.
      * apply notin_remove_1 in H1. destruct H1. 
        ** subst. apply notin_remove_3'; reflexivity.
        ** apply notin_union_1 in H. apply notin_remove_2. assumption.
    + apply IHn0.
      * assumption.
      * apply notin_remove_1 in H1. destruct H1. 
        ** subst. apply notin_remove_3'. reflexivity.
        ** apply notin_union_2 in H. apply notin_remove_2. assumption.
  - simpl in *. apply notin_union_3. 
    + apply notin_remove_1 in H1. destruct H1.
      * subst. apply notin_remove_3'. reflexivity.
      * simpl. apply notin_union_1 in H. assumption.
    + apply IHn. 
      * assumption. 
      * apply notin_remove_1 in H1. destruct H1.
        ** subst. apply notin_remove_3'. reflexivity.
        ** simpl. apply notin_union_2 in H. apply notin_remove_2. assumption.
  - simpl in *. apply notin_remove_1 in H1. destruct H1.
    + subst. apply notin_union_3.
      * case (y == z).
        ** intros Heq. subst. apply notin_remove_3'; reflexivity.
        ** intros Hneq. apply notin_remove_2. clear e1. apply notin_union_2 in _x0. apply notin_union_1 in _x0. 
           apply IHn.
          *** assumption.
          *** apply notin_remove_3; reflexivity.
      * simpl. apply IHn0. 
        ** assumption.
        ** apply notin_remove_3; reflexivity.
    + simpl. apply notin_union_3.
      * case (y == z). 
        ** intro Heq. subst. apply notin_remove_3; reflexivity.
        ** intro Hneq. apply notin_remove_2. apply notin_union_1 in H. apply IHn.
            *** assumption.
            *** apply notin_remove_1 in H. destruct H.
                **** simpl. subst. apply notin_remove_2. apply fv_nom_swap. clear e1. apply notin_union_2 in _x0. apply notin_union_1 in _x0. apply notin_union_1 in _x0. apply notin_remove_1 in _x0. destruct _x0.
                     ***** contradiction.
                     ***** assumption.
                **** apply notin_remove_2. case (y == y0). 
                     ***** intro Heq. subst. apply fv_nom_swap. clear e1. apply notin_union_2 in _x0. apply notin_union_1 in _x0. apply notin_union_1 in _x0. apply notin_remove_1 in _x0. destruct _x0.
                     ****** contradiction.
                     ****** assumption.
                     ***** intro Hneq'. apply fv_nom_remove_swap.
                     ****** assumption.
                     ****** assumption.
                     ****** assumption.
      * apply IHn0.
        ** assumption.
        ** apply notin_union_2 in H. apply notin_remove_2. assumption.
Qed.

Corollary fv_nom_remove_eq: forall t1 t2 x, x `notin` fv_nom t2 -> x `notin` fv_nom ({x := t2} t1).
Proof.
  intros t1 t2 x Hnotin. apply fv_nom_remove.
  - assumption.
  - apply notin_remove_3. reflexivity.
Qed.

Lemma pure_m_subst : forall t u x, pure t -> pure u -> pure ({x := u}t).
Proof.
  induction t as [y | t1 y IHt1 | t1 t2 IHt1 IHt2 | t1 t2 y IHt1 IHt2] using n_sexp_induction.
  - intros u x H1 H2. unfold m_subst. rewrite subst_rec_fun_equation. destruct (x == y).
    + assumption.
    + assumption.
  - intros u x H1 H2. unfold m_subst in *. rewrite subst_rec_fun_equation. destruct (x == y).
    + assumption.
    + destruct (atom_fresh (union (fv_nom u) (union (fv_nom (n_abs y t1)) (singleton x)))) as [z Hnotin]. apply pure_abs. inversion H1; subst. pose proof pure_swap as H'. specialize (H' y z t1). pose proof H0 as H''. apply H' in H''. clear H'. apply IHt1.
      * rewrite swap_size_eq. reflexivity.
      * assumption.
      * assumption.
  - intros u x Happ Hpure. inversion Happ; subst. unfold m_subst in *. rewrite subst_rec_fun_equation. apply pure_app.
    + apply IHt1; assumption.
    + apply IHt2; assumption.
  - intros u x Hsubst Hpure. inversion Hsubst. 
Qed. 

Axiom aeq_fv_nom_eq: forall t1 t2, t1 =a t2 -> fv_nom t1 = fv_nom t2.
(* end hide*)

(**

We list several important properties of the metasubstitution include its compatibility with $\alpha$-equivalence when the variables of the metasubstitutions are the same.

*)
Lemma aeq_m_subst_in: forall t u u' x, u =a u' -> ({x := u}t) =a ({x := u'}t).
Proof.
  induction t as [y | t1 y | t1 t2 | t1 t2 y ] using n_sexp_induction. 
  - intros u u' x Haeq. unfold m_subst. repeat rewrite subst_rec_fun_equation. destruct (x == y).
    + assumption.
    + apply aeq_refl.
  - intros u u' x Haeq. unfold m_subst in *. repeat rewrite subst_rec_fun_equation. destruct (x == y). 
    + apply aeq_refl. 
    + pose proof Haeq as Hfv. apply aeq_fv_nom_eq in Hfv. rewrite Hfv. destruct (atom_fresh (union (fv_nom u') (union (fv_nom (n_abs y t1)) (singleton x)))). destruct (atom_fresh (union (fv_nom u) (union (fv_nom (n_abs y t1)) (singleton x)))). apply aeq_abs_same. apply H.
      * rewrite swap_size_eq. reflexivity.
      * assumption.
  - intros u u' x Haeq. unfold m_subst in *. rewrite subst_rec_fun_equation. apply aeq_sym. rewrite subst_rec_fun_equation. apply aeq_app.
    + apply IHt2. apply aeq_sym. assumption.
    + apply IHt1. apply aeq_sym. assumption.
  - intros u u' x Haeq. case (x == y).
    + intro Heq. subst. repeat rewrite m_subst_sub_eq. apply aeq_sub_same.
      * apply aeq_refl.
      * apply IHt1. assumption.
    + intro Hneq. unfold m_subst in *. rewrite subst_rec_fun_equation. apply aeq_sym. rewrite subst_rec_fun_equation. destruct (x == y).
      * contradiction.
      * pose proof Haeq as Hfv. apply aeq_fv_nom_eq in Hfv. rewrite Hfv. destruct (atom_fresh (union (fv_nom u') (union (fv_nom ([y := t2]t1)) (singleton x)))). apply aeq_sub_same.     
        ** apply H.
           *** rewrite swap_size_eq. reflexivity.
           *** apply aeq_sym. assumption.
        ** apply IHt1. apply aeq_sym. assumption.
Qed. 
(* begin hide *)
Lemma m_subst_notin: forall t u x, x `notin` fv_nom t -> {x := u}t =a t.
Proof.
  induction t as [y | t1 y | t1 t2 | t1 t2 y ] using n_sexp_induction. 
  - intros u x Hfv. simpl in *. apply notin_singleton_1 in Hfv. rewrite m_subst_var_neq.
    + apply aeq_refl.
    + assumption.
  - intros u x Hfv. simpl in *. unfold m_subst in *. rewrite subst_rec_fun_equation. destruct (x == y). 
    + subst. apply aeq_refl. 
    + destruct (atom_fresh (union (fv_nom u) (union (fv_nom (n_abs y t1)) (singleton x)))) as [z]. case (z == y). 
      * intro Heq. subst. apply aeq_abs_same. apply aeq_trans with (swap y y t1).
        ** apply H. 
           *** rewrite swap_id. reflexivity.
           *** rewrite swap_id. apply notin_remove_1 in Hfv. destruct Hfv.
               **** symmetry in H0. contradiction.
               **** assumption.
        ** rewrite swap_id. apply aeq_refl. 
      * intro Hneq. apply aeq_abs_diff. 
        ** assumption.
        ** apply notin_union_2 in n0. apply notin_union_1 in n0. simpl in n0. apply notin_remove_1 in n0. destruct n0.
           *** subst. contradiction.
           *** assumption.
        ** apply H.
           *** rewrite swap_size_eq. reflexivity.
           *** apply notin_remove_1 in Hfv. destruct Hfv.
               **** symmetry in H0. contradiction.
               **** repeat apply notin_union_2 in n0. apply notin_singleton_1 in n0. apply fv_nom_remove_swap; assumption.
  - intros u x Hfv. unfold m_subst in *. simpl in *. rewrite subst_rec_fun_equation. apply aeq_app.
    + apply IHt2. apply notin_union_1 in Hfv. assumption.
    + apply IHt1. apply notin_union_2 in Hfv. assumption.
  - intros u x Hfv. simpl in *. unfold m_subst in *. rewrite subst_rec_fun_equation. destruct (atom_fresh (union (fv_nom u) (union (fv_nom (n_sub t1 y t2)) (singleton x)))). destruct (x == y). 
    + subst. apply aeq_sub_same.
      * apply aeq_refl.
      * apply notin_union_2 in Hfv. apply IHt1. assumption.
    + case (x0 == y).
      * intro Heq. subst. apply aeq_sub_same.
        ** apply aeq_trans with (swap y y t1). apply H.
           *** rewrite swap_id. reflexivity.
           *** rewrite swap_id. apply notin_union_1 in Hfv. apply notin_remove_1 in Hfv. destruct Hfv.
               **** symmetry in H0. contradiction.
               **** assumption.
           *** rewrite swap_id. apply aeq_refl.
        ** apply IHt1. apply notin_union_2 in Hfv. assumption.
      * intro Hneq. apply aeq_sub_diff.
        ** apply IHt1. apply notin_union_2 in Hfv. assumption.
        ** assumption.
        ** apply notin_union_2 in n. apply notin_union_1 in n. simpl in n. apply notin_union_1 in n. apply notin_remove_1 in n. destruct n.
           *** symmetry in H0. contradiction.
           *** assumption.
        ** apply H.
           *** rewrite swap_size_eq. reflexivity.
           *** apply notin_union_1 in Hfv. apply notin_remove_1 in Hfv. destruct Hfv. 
               **** symmetry in H0. contradiction. 
               **** repeat apply notin_union_2 in n. apply notin_singleton_1 in n. apply fv_nom_remove_swap; assumption.
Qed.

Lemma aeq_sub_notin: forall t1 t1' t2 t2' x y, x <> y ->  n_sub t1 x t2 =a n_sub t1' y t2' -> x `notin` fv_nom t1'.
Proof.
  intros t1 t1' t2 t2' x y Hneq Haeq. inversion Haeq; subst.
  - contradiction.
  - assumption.
Qed.
(* end hide *)
Lemma aeq_m_subst_out: forall t t' u x, t =a t' -> ({x := u}t) =a ({x := u}t').
Proof.
  induction t as [y | t1 y | t1 t2 | t1 t2 y] using n_sexp_induction. 
  - intros t' u x Haeq. inversion Haeq; subst. apply aeq_refl.
  - intros t' u x Haeq. inversion Haeq; subst. 
    + case (x == y).  
      * intro Heq. subst. repeat rewrite m_subst_abs_eq. assumption. 
      * intro Hneq. unfold m_subst in *. repeat rewrite subst_rec_fun_equation. destruct (x == y).
        ** contradiction.
        ** simpl. pose proof H3 as Haeq'. apply aeq_fv_nom_eq in H3. rewrite H3. destruct (atom_fresh (union (fv_nom u) (union (remove y (fv_nom t2)) (singleton x)))) as [z]. apply aeq_abs_same. apply H.
           *** rewrite swap_size_eq. reflexivity. 
           *** apply aeq_swap1. assumption. 
    + case (x == y). 
      * intro Heq. subst. rewrite m_subst_abs_eq. unfold m_subst in *. rewrite subst_rec_fun_equation. destruct (y == y0).
        ** contradiction.
        ** destruct (atom_fresh (union (fv_nom u) (union (fv_nom (n_abs y0 t2)) (singleton y)))) as [x]. apply aeq_trans with (n_abs x (swap y0 x t2)).
           *** apply aeq_trans with (n_abs y0 t2). 
               **** assumption.
               **** case (x == y0).
                    ***** intro Heq. subst. rewrite swap_id. apply aeq_refl.
                    ***** intro Hneq. apply aeq_abs_diff.
                    ****** apply aux_not_equal. assumption.
                    ****** apply fv_nom_swap. apply notin_union_2 in n0. apply notin_union_1 in n0. simpl in n0. apply notin_remove_1 in n0. destruct n0.
                    ******* symmetry in H0. contradiction.
                    ******* assumption.
                    ****** rewrite (swap_symmetric _ y0 x). rewrite swap_involutive. apply aeq_refl.
           *** apply aeq_abs_same. apply aeq_sym. apply m_subst_notin. repeat apply notin_union_2 in n0. apply notin_singleton_1 in n0. apply fv_nom_remove_swap; assumption. 
      * intro Hneq. case (x == y0).
        ** intro Heq. subst. rewrite m_subst_abs_eq. apply aeq_trans with (n_abs y t1).
           *** apply m_subst_notin. apply aeq_sym in Haeq. apply aeq_abs_notin in Haeq.
               ****  simpl. apply notin_remove_2. assumption.
               **** assumption.
           *** assumption.
        ** intro Hneq'. unfold m_subst in *. repeat rewrite subst_rec_fun_equation. destruct (x == y).
           *** contradiction.
           *** destruct (x == y0).
               **** contradiction.
               **** pose proof Haeq as Hfv. apply aeq_fv_nom_eq in Hfv. rewrite Hfv. destruct (atom_fresh (union (fv_nom u) (union (fv_nom (n_abs y0 t2)) (singleton x)))) as [x0]. apply  aeq_abs_same. apply H. 
                    ***** rewrite swap_size_eq. reflexivity.
                    ***** apply (aeq_swap _ _ y x0) in H5. rewrite H5. case (x0 == y0).
                    ****** intro Heq. subst. rewrite swap_id. rewrite (swap_symmetric _ y y0). rewrite swap_involutive. apply aeq_refl.
                    ****** intro Hneq''. rewrite (swap_symmetric _ y x0). rewrite (swap_symmetric _ y0 y). rewrite (swap_symmetric _ y0 x0). apply aeq_swap_swap.
                    ******* apply notin_union_2 in n1. apply notin_union_1 in n1. simpl in n1. apply notin_remove_1 in n1. destruct n1.
                    ******** symmetry  in H0. contradiction.
                    ******** assumption.
                    ******* assumption. 
  - intros t u x Haeq. inversion Haeq; subst. clear Haeq. unfold m_subst in *. rewrite subst_rec_fun_equation. apply aeq_sym. rewrite subst_rec_fun_equation. apply aeq_app.
    + apply aeq_sym. apply IHt2. assumption.
    + apply aeq_sym. apply IHt1. assumption.
  - intros t u x Haeq. inversion Haeq; subst. 
    + case (x == y). 
      * intro Heq. subst. repeat rewrite m_subst_sub_eq. apply aeq_sub_same. 
        ** assumption.
        ** apply IHt1. assumption. 
      * intro Hneq.  unfold m_subst in *. rewrite subst_rec_fun_equation. apply aeq_sym. rewrite subst_rec_fun_equation. destruct (x == y).
        ** contradiction.
        ** pose proof H4 as Hfvt1. apply aeq_fv_nom_eq in Hfvt1. pose proof H5 as Hfvt2. apply aeq_fv_nom_eq in Hfvt2. simpl. rewrite Hfvt1. rewrite Hfvt2. destruct (atom_fresh (union (fv_nom u) (union (union (remove y (fv_nom t1')) (fv_nom t2')) (singleton x)))). apply aeq_sub_same.
           *** apply H. 
               **** apply aeq_size in H4. symmetry. rewrite swap_size_eq. assumption.
               **** apply aeq_swap. apply aeq_sym. assumption.
           *** apply aeq_sym. apply IHt1. assumption.
    + case (x == y). 
      * intro Heq. subst. rewrite m_subst_sub_eq. case (y == y0). 
        ** intro Heq. subst. contradiction. 
        ** intro Hneq. unfold m_subst in *. apply aeq_sym. rewrite subst_rec_fun_equation. destruct (y == y0).
           *** contradiction.
           *** destruct (atom_fresh (union (fv_nom u) (union (fv_nom ([y0 := t2'] t1')) (singleton y)))). apply aeq_sub_diff.
               **** apply aeq_sym. apply IHt1. assumption. 
               **** repeat apply notin_union_2 in n0. apply notin_singleton_1 in n0. apply aux_not_equal. assumption.
               **** pose proof n0 as Hfv. apply notin_union_2 in n0. apply notin_union_1 in n0. simpl in n0. apply notin_union_1 in n0. apply (aeq_swap1 _ _ y0 y) in H7. rewrite swap_involutive in H7. apply aeq_fv_nom in H7. rewrite <- H7 in n0. rewrite <- H7 in H6. case (x == y0).
                    ***** intro Heq. subst. apply fv_nom_swap_2 in H6. assumption.
                    ***** intro Hneq'. apply notin_remove_1 in n0.
                    ****** destruct n0.
                    ******* symmetry in H0. contradiction.
                    ******* apply fv_nom_swap_remove in H0.
                    ******** assumption.
                    ******** repeat apply notin_union_2 in Hfv. apply notin_singleton_1 in Hfv. apply aux_not_equal. assumption.
                    ******** assumption.
               **** apply aeq_trans with (swap y0 x t1'). 
                    ***** apply m_subst_notin. apply fv_nom_remove_swap.
                    ****** repeat apply notin_union_2 in n0. apply notin_singleton_1 in n0. assumption.
                    ****** assumption.
                    ****** assumption.
                    ***** apply (aeq_swap1 _ _ y x) in H7. rewrite H7.  apply aeq_sym. rewrite (swap_symmetric _ y x). rewrite (swap_symmetric _ y0 y). rewrite (swap_symmetric _ y0 x). case (x == y0).
                    ****** intro Heq. subst. rewrite (swap_symmetric _ y0 y). rewrite swap_involutive. rewrite swap_id. apply aeq_refl.
                    ****** intro Hneq'. apply aeq_swap_swap.
                    ******* apply notin_union_2 in n0. apply notin_union_1 in n0. simpl in n0. apply notin_union_1 in n0. apply notin_remove_1 in n0. destruct n0.
                    ******** symmetry in H0. contradiction.
                    ******** assumption.
                    ******* assumption.  
      * intro Hneq. case (x == y0).
        ** intro Heq. subst. rewrite m_subst_sub_eq. unfold m_subst. rewrite subst_rec_fun_equation. destruct (y0 == y).
           *** contradiction.
           *** destruct (atom_fresh (union (fv_nom u) (union (fv_nom ([y := t2] t1)) (singleton y0)))). apply aeq_sub_diff.
               **** apply IHt1. assumption. 
               **** repeat apply notin_union_2 in n0. apply notin_singleton_1 in n0. apply aux_not_equal. assumption.
               **** pose proof n0 as Hfv. apply notin_union_2 in n0. apply notin_union_1 in n0. simpl in n0. apply notin_union_1 in n0. apply (aeq_swap1 _ _ y0 y) in H7. rewrite swap_involutive in H7. apply aeq_fv_nom in H7. rewrite <- H7. case (x == y).
                    ***** intro Heq. subst. rewrite (swap_symmetric _ y0 y). apply fv_nom_swap. apply aeq_sym in Haeq. apply aeq_sub_notin in Haeq.
                    ****** assumption.
                    ****** assumption.
                    ***** intro Hneq'. apply notin_remove_1 in n0. destruct n0.
                    ******* symmetry in H0. contradiction.
                    ******* apply fv_nom_remove_swap.
                    ******** assumption.
                    ******** repeat apply notin_union_2 in Hfv. apply notin_singleton_1 in Hfv. apply aux_not_equal. assumption.
                    ******** assumption.
               **** apply aeq_trans with (swap y x t1). 
                    ***** apply m_subst_notin. apply aeq_sym in Haeq. apply aeq_sub_notin in Haeq. 
                    ****** apply fv_nom_remove_swap.
                    ******* repeat apply notin_union_2 in n0. apply notin_singleton_1 in n0. assumption.
                    ******* assumption.
                    ******* assumption.
                    ****** assumption.
                    ***** apply (aeq_swap1 _ _ y x) in H7. rewrite H7. rewrite (swap_symmetric _ y x). rewrite (swap_symmetric _ y0 y). rewrite (swap_symmetric _ y0 x). case (x == y).
                    ****** intro Heq. subst. rewrite swap_id. apply aeq_refl.
                    ****** intro Hneq'. apply aeq_swap_swap.
                    *******  pose proof n0 as Hfv. apply notin_union_2 in n0. apply notin_union_1 in n0. simpl in n0. apply notin_union_1 in n0. apply notin_remove_1 in n0. destruct n0.
                    ******** symmetry in H0. contradiction.
                    ******** apply aeq_swap in H7. apply aeq_sym in H7. apply (aeq_swap1 _ _ y0 y) in H7. rewrite swap_involutive in H7. apply aeq_fv_nom in H7. rewrite H7. apply fv_nom_remove_swap.
                    ********* assumption.  
                    ********* repeat apply notin_union_2 in Hfv. apply notin_singleton_1 in Hfv. apply aux_not_equal. assumption.
                    ********* assumption.
                    ******* assumption.
        ** intro Hneq'. unfold m_subst in *. rewrite subst_rec_fun_equation. destruct (x == y).
           *** contradiction.
           *** apply aeq_sym. rewrite subst_rec_fun_equation. destruct (x == y0).
               **** contradiction.
               ****  apply aeq_fv_nom_eq in Haeq. simpl in *. rewrite Haeq. destruct (atom_fresh (union (fv_nom u) (union (union (remove y0 (fv_nom t1')) (fv_nom t2')) (singleton x)))). apply aeq_sub_same.
                    ***** apply H.
                    ****** apply aeq_size in H7. rewrite swap_size_eq in H7. symmetry. rewrite swap_size_eq. assumption.
                    ****** apply (aeq_swap1 _ _ y x0) in H7. rewrite H7. apply aeq_sym. rewrite (swap_symmetric _ y x0). rewrite (swap_symmetric _ y0 y). rewrite (swap_symmetric _ y0 x0). case (x0 == y0).
                    ******* intro Heq. subst. rewrite (swap_symmetric _ y0 y). rewrite swap_involutive. rewrite swap_id. apply aeq_refl.
                    ******* intro Hneq''. apply aeq_swap_swap.
                    ******** apply notin_union_2 in n1. apply notin_union_1 in n1. apply notin_union_1 in n1. apply notin_remove_1 in n1. destruct n1. subst. contradiction.
                    ********* assumption.
                    ******** assumption.
                    ***** apply aeq_sym. apply IHt1. assumption.
Qed.
(* begin hide *)
Corollary aeq_m_subst_eq: forall t t' u u' x, t =a t' -> u =a u' -> ({x := u}t) =a ({x := u'}t').
Proof.
  intros t t' u u' x H1 H2. apply aeq_trans with ({x:=u}t').
  - apply aeq_m_subst_out. assumption.
  - apply aeq_m_subst_in. assumption.
Qed.

Lemma aeq_swap_m_subst: forall x y z t u, swap x y ({z := u}t) =a ({(vswap x y z) := (swap x y u)}(swap x y t)).
Proof.
  intros x y z t u. destruct (x == y). 
  - subst. repeat rewrite swap_id. rewrite vswap_id. apply aeq_refl.
  - generalize dependent u. generalize dependent z. generalize dependent y. generalize dependent x. induction t as  [y' | t1 y' | t1 t2 | t1 t2 y'] using n_sexp_induction.    
    + intros x y Hneq z u. unfold m_subst. rewrite subst_rec_fun_equation. destruct (z == y').
      * subst. simpl swap at 2. rewrite subst_rec_fun_equation. rewrite eq_dec_refl. apply aeq_refl.
      * pose proof n as Hswap. apply (swap_neq x y) in n. simpl swap at 2. rewrite subst_rec_fun_equation. destruct (vswap x y z == vswap x y y').
        ** contradiction.
        ** simpl swap. apply aeq_refl.
    + intros x y Hneq z u. simpl. case (y' == z). 
      * intro Heq. subst. repeat rewrite m_subst_abs_eq. simpl. apply aeq_refl. 
      * intro Hneq'. unfold m_subst in *. repeat rewrite subst_rec_fun_equation. destruct (z == y').
        ** symmetry in e. contradiction.
        ** destruct (vswap x y z == vswap x y y').
           *** apply (swap_neq x y) in n. contradiction.
           *** simpl. destruct (atom_fresh (union (fv_nom u) (union (remove y' (fv_nom t1)) (singleton z)))) as [x0]. destruct (atom_fresh (union (fv_nom (swap x y u)) (union (remove (vswap x y y') (fv_nom (swap x y t1))) (singleton (vswap x y z))))) as [x1]. simpl. case (x1 == vswap x y x0).
               **** intro Heq. subst. apply aeq_abs_same. rewrite H. 
                    ***** rewrite <- swap_equivariance. apply aeq_refl.
                    ***** rewrite swap_size_eq. reflexivity.
                    ***** assumption.
               **** intro Heq''. apply aeq_abs_diff.  
                    ***** apply aux_not_equal. assumption.
                    ***** apply fv_nom_remove.
                    ****** apply notin_fv_nom_equivariance. apply notin_union_1 in n1. assumption.
                    ****** apply notin_remove_2. pose proof n1 as Hx0. case (y' == x0).
                    ******** intro Heq. subst. apply fv_nom_swap. apply notin_union_2 in n2. apply notin_union_1 in n2. apply notin_remove_1 in n2. destruct n2.
                    ********* symmetry in H0. contradiction.
                    ********* assumption.
                    ******** intros Hneq'''. apply fv_nom_remove_swap.
                    ********* apply aux_not_equal. assumption.
                    ********* apply aux_not_equal. apply swap_neq. assumption.
                    ********* apply notin_union_2 in n1. apply notin_union_1 in n1. apply notin_remove_1 in n1. destruct n1.
                    ********** contradiction.
                    ********** apply notin_fv_nom_equivariance. assumption. 
                    ***** rewrite H. 
                    ****** apply aeq_sym. rewrite H.
                    ******* replace (vswap x1 (vswap x y x0) (vswap x y z)) with (vswap x y z).
                    ******** apply aeq_m_subst_eq.
                    ********* rewrite (swap_symmetric _ x1 (vswap x y x0)). rewrite (swap_symmetric _ (vswap x y y') x1). case (x0 == y'). 
                    *********** intro Heq. subst. rewrite (swap_symmetric _ (vswap x y y') x1). rewrite swap_involutive. rewrite swap_id. apply aeq_refl.
                    *********** intro Hneq''. rewrite (swap_symmetric _ y' x0). rewrite (swap_equivariance _ x y x0 y'). case (x1 == vswap x y y'). 
                    ************ intro Heq. subst. rewrite swap_id. apply aeq_refl.
                    ************ intro Hneq'''. apply aeq_swap_swap.
                    ************** apply notin_fv_nom_equivariance. apply notin_union_2 in n1. apply notin_union_1 in n1. apply notin_remove_1 in n1. destruct n1.
                    *************** symmetry in H0. contradiction.
                    *************** assumption.
                    ************** apply notin_union_2 in n2. apply notin_union_1 in n2. apply notin_remove_1 in n2. destruct n2.
                    *************** symmetry in H0. contradiction.
                    *************** assumption.
                    ********* apply swap_reduction.
                    ********** apply notin_union_1 in n2. assumption.
                    ********** apply notin_union_1 in n1. apply notin_fv_nom_equivariance. assumption.
                    ******** symmetry. unfold vswap at 1. destruct (vswap x y z ==  x1).
                    ********* repeat apply notin_union_2 in n2. apply notin_singleton_1 in n2. contradiction.
                    ********* destruct (vswap x y z == vswap x y x0).
                    ********** repeat apply notin_union_2 in n1. apply notin_singleton_1 in n1. apply (swap_neq x y) in n1. contradiction.
                    ********** reflexivity.
                    ******* repeat rewrite swap_size_eq. reflexivity.
                    ******* assumption.
                    ****** rewrite swap_size_eq. reflexivity.
                    ****** assumption.
    + intros x y H z u. unfold m_subst in *. rewrite subst_rec_fun_equation. simpl. apply aeq_sym. rewrite subst_rec_fun_equation. apply aeq_sym. apply aeq_app.
      * apply IHt2. assumption.
      * apply IHt1. assumption.
    + intros x y Hneq z u. simpl. case (y' == z). 
      * intro Heq. subst. repeat rewrite m_subst_sub_eq. simpl. apply aeq_sub_same. 
        ** apply aeq_refl.
        ** apply IHt1. assumption.
      * intro Hneq'. unfold m_subst. rewrite subst_rec_fun_equation. apply aeq_sym. rewrite subst_rec_fun_equation. destruct (z == y').
        ** symmetry in e. contradiction.
        ** destruct (vswap x y z == vswap x y y').
           *** apply (swap_neq x y) in n. contradiction.
           *** destruct (atom_fresh (union (fv_nom u) (union (fv_nom (n_sub t1 y' t2)) (singleton z)))). destruct (atom_fresh (union (fv_nom (swap x y u)) (union (fv_nom (n_sub (swap x y t1) (vswap x y y') (swap x y t2))) (singleton (vswap x y z))))). simpl in *. apply aeq_sym. case (x1 == vswap x y x0). 
               **** intro Heq. subst. apply aeq_sub_same. 
                    ***** rewrite <- swap_equivariance. apply H.
                    ****** rewrite swap_size_eq. reflexivity.
                    ****** assumption.
                    ***** apply IHt1. assumption.
               **** intro Hneq''. apply aeq_sub_diff.
                    ***** apply IHt1. assumption. 
                    ***** apply aux_not_equal. assumption.
                    ***** apply fv_nom_remove.
                    ****** apply notin_fv_nom_equivariance. apply notin_union_1 in n1. assumption.
                    ****** apply notin_remove_2. case (y' == x0).
                    ******* intro Heq. subst. apply fv_nom_swap. apply notin_union_2 in n2. apply notin_union_1 in n2. apply notin_union_1 in n2. apply notin_remove_1 in n2. destruct n2.
                    ******** symmetry in H0. contradiction.
                    ******** assumption.
                    ******* intro Hneq'''. apply fv_nom_remove_swap.
                    ******** apply aux_not_equal. assumption.
                    ******** apply (swap_neq x y) in Hneq'''. apply aux_not_equal. assumption.
                    ******** apply notin_fv_nom_equivariance. apply notin_union_2 in n1. apply notin_union_1 in n1. apply notin_union_1 in n1. apply notin_remove_1 in n1. destruct n1.
                    ********* contradiction.
                    ********* assumption.
                    ***** unfold m_subst in *. rewrite H. 
                    ****** apply aeq_sym. rewrite H.
                    ******* replace (vswap x1 (vswap x y x0) (vswap x y z)) with (vswap x y z).
                    ******** apply aeq_m_subst_eq.
                    ********* rewrite (swap_symmetric _ x1 (vswap x y x0)). rewrite (swap_symmetric _ (vswap x y y') x1). case (x0 == y'). 
                    *********** intro Heq. subst. rewrite (swap_symmetric _ (vswap x y y') x1). rewrite swap_involutive. rewrite swap_id. apply aeq_refl.
                    *********** intro Hneq'''. rewrite (swap_symmetric _ y' x0). rewrite (swap_equivariance _ x y x0 y'). case (x1 == vswap x y y'). 
                    ************ intro Heq. subst. rewrite swap_id. apply aeq_refl.
                    ************ intro Hneq''''. apply aeq_swap_swap.
                    ************** apply notin_fv_nom_equivariance. apply notin_union_2 in n1. apply notin_union_1 in n1. apply notin_union_1 in n1. apply notin_remove_1 in n1. destruct n1.
                    *************** symmetry in H0. contradiction.
                    *************** assumption.
                    ************** apply notin_union_2 in n2. apply notin_union_1 in n2. apply notin_union_1 in n2. apply notin_remove_1 in n2. destruct n2.
                    *************** symmetry in H0. contradiction.
                    *************** assumption.
                    ********* apply swap_reduction.
                    ********** apply notin_union_1 in n2. assumption.
                    ********** apply notin_union_1 in n1. apply notin_fv_nom_equivariance. assumption.
                    ******** symmetry. unfold vswap at 1. destruct (vswap x y z ==  x1).
                    ********* repeat apply notin_union_2 in n2. apply notin_singleton_1 in n2. contradiction.
                    ********* destruct (vswap x y z == vswap x y x0).
                    ********** repeat apply notin_union_2 in n1. apply notin_singleton_1 in n1. apply (swap_neq x y) in n1. contradiction.
                    ********** reflexivity.
                    ******* repeat rewrite swap_size_eq. reflexivity.
                    ******* assumption.
                    ****** rewrite swap_size_eq. reflexivity.
                    ****** assumption.
Qed.
(* end hide *)
(**
Also the propagation of the metasubstitution inside an abstraction with an adequate renaming to avoid capture of variables:
*)
Lemma m_subst_abs_neq: forall t u x y z, x <> y -> z `notin` fv_nom u `union` fv_nom (n_abs y t) `union` {{x}} -> {x := u}(n_abs y t) =a n_abs z ({x := u}(swap y z t)).
Proof.
  intros t u x y z H1 H2. unfold m_subst. rewrite subst_rec_fun_equation. destruct (x == y).
  - subst. contradiction.
  - destruct (atom_fresh (union (fv_nom u) (union (fv_nom (n_abs y t)) (singleton x)))). case (x0 == z).
    + intro Heq. subst. apply aeq_refl.
    + intro Hneq. apply aeq_abs_diff.
      * assumption.
      * apply fv_nom_remove.
        ** apply notin_union_1 in n0. assumption.
        ** simpl in *. case (x0 == y).
           *** intro Heq. subst. apply notin_remove_2. apply fv_nom_swap. apply notin_union_2 in H2. apply notin_union_1 in H2. simpl in H2. apply notin_remove_1 in H2. destruct H2.
               **** contradiction.
               **** assumption.
           *** intro Hneq'. apply notin_remove_2. apply notin_union_2 in n0. apply notin_union_1 in n0. apply notin_remove_1 in n0. destruct n0.
               **** symmetry in H. contradiction.
               **** apply fv_nom_remove_swap; assumption.
      * apply aeq_sym. apply aeq_trans with (subst_rec_fun (swap z x0 (swap y z t)) (swap z x0 u) (vswap z x0 x)).
        ** apply aeq_swap_m_subst.
        ** replace (vswap z x0 x) with x.
           *** apply aeq_m_subst_eq.
               **** rewrite (swap_symmetric _ z x0). rewrite (swap_symmetric _ y z). rewrite (swap_symmetric _ y x0). case (x0 == y).
                    ***** intro Heq. subst. rewrite (swap_symmetric _ y z). rewrite swap_involutive. rewrite swap_id. apply aeq_refl.
                    ***** intro Hneq'. case (z == y).
                    ****** intro Heq. subst. rewrite swap_id. apply aeq_refl.
                    ****** intro Hneq''. apply aeq_swap_swap.
                    ******* apply notin_union_2 in n0. apply notin_union_1 in n0. simpl in n0. apply notin_remove_1 in n0. destruct n0.
                    ******** symmetry in H. contradiction.
                    ******** assumption.
                    ******* apply notin_union_2 in H2. apply notin_union_1 in H2. simpl in H2. apply notin_remove_1 in H2. destruct H2.
                    ******** symmetry in H. contradiction.
                    ******** assumption.
               **** apply swap_reduction.
                    ***** apply notin_union_1 in H2. assumption.
                    ***** apply notin_union_1 in n0. assumption.
           *** unfold vswap. repeat apply notin_union_2 in H2. apply notin_singleton_1 in H2. repeat apply notin_union_2 in n0. apply notin_singleton_1 in n0. default_simp.
Qed.               
(* begin hide *)
Corollary m_subst_n_abs_neq_notin: forall t1 t2 x y, x <> y -> x `notin` fv_nom t2 -> {y := t2} (n_abs x t1) =a n_abs x ({y := t2} t1).
Proof.
  intros t1 t2 x y Hneq Hnotin. apply aeq_trans with (let (z,_) := (atom_fresh (Metatheory.union (fv_nom t2) (Metatheory.union (fv_nom t1) (Metatheory.union (singleton y) (singleton x))))) in n_abs z ({y := t2} (swap z x t1))).
  - default_simp. rewrite (swap_symmetric _ x0 x). apply m_subst_abs_neq.
    + apply aux_not_equal. assumption.
    + apply notin_union.
      * apply notin_union_1 in n. assumption.
      * apply notin_union.
        ** simpl. apply notin_remove_2. apply notin_union_2 in n. apply notin_union_1 in n. assumption.
        ** apply notin_union_2 in n. apply notin_union_2 in n. apply notin_union_1 in n. assumption.
  - default_simp. apply aeq_abs_diff.
    + repeat apply notin_union_2 in n. apply notin_singleton_1 in n. apply aux_not_equal. assumption.
    + apply fv_nom_remove.
      * apply notin_union_1 in n. assumption.
      * apply notin_remove_2. apply notin_union_2 in n. apply notin_union_1 in n. assumption.
    + apply aeq_trans with ({(vswap x0 x y) := swap x0 x t2} (swap x0 x t1)).
      * unfold vswap. destruct (y == x0).
        ** apply notin_union_2 in n. apply notin_union_2 in n. apply notin_union_1 in n. apply notin_singleton_1 in n. contradiction.
        ** destruct (y == x).
           *** symmetry in e. contradiction.
           *** apply aeq_m_subst_in. apply aeq_sym. apply swap_reduction.
               **** apply notin_union_1 in n. assumption.
               **** assumption.
      * apply aeq_sym. rewrite (swap_symmetric _ x x0). apply aeq_swap_m_subst.
Qed. 
    
Lemma m_subst_sub_neq: forall t1 t2 u x y z, x <> y -> z `notin` fv_nom u `union` fv_nom ([y := t2]t1) `union` {{x}} -> {x := u}([y := t2]t1) =a ([z := ({x := u}t2)]({x := u}(swap y z t1))).
Proof.
  intros t1 t2 u x y z H1 H2. unfold m_subst. rewrite subst_rec_fun_equation. destruct (x == y). 
  - contradiction.
  - destruct (atom_fresh (union (fv_nom u) (union (fv_nom ([y := t2]t1)) (singleton x)))). destruct (x0 == z).
    + subst. apply aeq_refl.
    + apply aeq_sub_diff.
      * apply aeq_refl.
      * assumption.
      * apply fv_nom_remove. 
        ** apply notin_union_1 in n0. assumption.
        ** simpl in *. case (x0 == y). 
           *** intro Heq. subst. apply notin_remove_2. apply fv_nom_swap. apply notin_union_2 in H2. apply notin_union_1 in H2. apply notin_union_1 in H2. apply notin_remove_1 in H2. destruct H2.
               **** contradiction.
               **** assumption.
           *** intro Hneq. apply notin_remove_2. apply fv_nom_remove_swap. 
               **** assumption.
               **** assumption.
               **** apply notin_union_2 in n0. apply notin_union_1 in n0. apply notin_union_1 in n0. apply diff_remove_2 in n0; assumption.
      * apply aeq_sym. apply aeq_trans with (subst_rec_fun (swap z x0 (swap y z t1)) (swap z x0 u) (vswap z x0 x)). 
        ** apply aeq_swap_m_subst.
        ** replace (vswap z x0 x) with x. 
           *** apply aeq_m_subst_eq. 
               **** rewrite (swap_symmetric _ z x0). rewrite (swap_symmetric _ y z). rewrite (swap_symmetric _ y x0). simpl in *. case (x0 == y).
                    ***** intro Heq. subst. rewrite (swap_symmetric _ y z). rewrite swap_involutive. rewrite swap_id. apply aeq_refl.
                    ***** intro Hneq. case (z == y). 
                    ****** intro Heq. subst. rewrite swap_id. apply aeq_refl.
                    ****** intro Hneq'. apply aeq_swap_swap.
                    ******* apply notin_union_2 in n0. apply notin_union_1 in n0. apply notin_union_1 in n0. apply notin_remove_1 in n0. destruct n0.
                    ******** symmetry in H. contradiction.
                    ******** assumption.
                    ******* apply notin_union_2 in H2. apply notin_union_1 in H2. apply notin_union_1 in H2. apply notin_remove_1 in H2. destruct H2.
                    ******** symmetry in H. contradiction.
                    ******** assumption.
               **** apply swap_reduction.
                    ***** apply notin_union_1 in H2. assumption.
                    ***** apply notin_union_1 in n0. assumption.
           *** unfold vswap. repeat apply notin_union_2 in H2. apply notin_singleton_1 in H2. repeat apply notin_union_2 in n0. apply notin_singleton_1 in n0. default_simp.
Qed.


Lemma aeq_double_m_subst: forall t t1 t2 x, {x := t1}({x := t2}t) =a ({x := ({x := t1}t2)}t).
Proof.
 intros. induction t using n_sexp_size_induction.
    - destruct (x0 == x).
      + subst. repeat rewrite m_subst_var_eq. apply aeq_refl.
      + repeat rewrite m_subst_var_neq; try assumption. apply aeq_refl.
    - destruct (x == z).
      + subst. repeat rewrite m_subst_abs_eq. apply aeq_refl.
      + apply aeq_trans with (let (z0,_) := (atom_fresh (Metatheory.union (fv_nom t1) (Metatheory.union (fv_nom t2)
               (Metatheory.union (fv_nom (n_abs z t)) (singleton x))))) in ({x := t1}(n_abs z0 ({x := t2} swap z z0 t)))).
        * default_simp. apply aeq_m_subst_out. apply m_subst_abs_neq.
          ** assumption.
          ** apply notin_union_3; auto.
        * default_simp. pose proof m_subst_abs_neq.  apply aeq_trans with (n_abs x0 ({x := {x := t1} t2} (swap z x0 t))).
          ** apply aeq_trans with (let (z0,_) := (atom_fresh (Metatheory.union (fv_nom t1) (Metatheory.union (fv_nom t2)
               (Metatheory.union (fv_nom (n_abs z t)) (Metatheory.union (singleton x0) (Metatheory.union (singleton x) (singleton z))))))) in (n_abs z0 ({x := t1} (swap x0 z0 ({x := t2} swap z x0 t))))).
            *** default_simp. apply m_subst_abs_neq; auto. apply notin_union_3.
              **** auto.
              **** apply notin_union_3; try auto. simpl. apply notin_remove_2. apply fv_nom_remove.
                ***** auto.
                ***** apply notin_remove_2. apply fv_nom_remove_swap; auto.
            *** default_simp. apply aeq_abs_diff.
              **** auto.
              **** apply fv_nom_remove.
                ***** apply fv_nom_remove; auto.
                ***** apply notin_remove_2. apply fv_nom_remove_swap; auto.
              **** apply aeq_trans with ({x := t1} ({vswap x0 x1 x := swap x0 x1 t2} swap x0 x1 (swap z x0 t))).
                ***** apply aeq_m_subst_out. apply aeq_swap_m_subst.
                ***** assert (Hneq: x <> x0). auto. assert (Hneq2: x <> x1). auto. 
                      unfold vswap. destruct (x == x0); try contradiction. destruct (x == x1); try contradiction. apply aeq_trans with ({x := t1} ({x := t2} swap x0 x1 (swap z x0 t))).
                  ****** apply aeq_m_subst_out. apply aeq_m_subst_in. apply swap_reduction; try auto.
                  ****** apply aeq_trans with ({vswap x0 x1 x := swap x0 x1 ({x := t1} t2)} swap x0 x1 (swap z x0 t)).
                    ******* unfold vswap. destruct (x == x0); try contradiction. destruct (x == x1); try contradiction. apply aeq_trans with ({x := ({x := t1} t2)} swap x0 x1 (swap z x0 t)).
                      ******** apply H. repeat rewrite swap_size_eq. lia.
                      ******** apply aeq_m_subst_in. pose proof aeq_swap_m_subst. specialize (H1 x0 x1 x t2 t1). apply aeq_trans with ({vswap x0 x1 x := swap x0 x1 t1} swap x0 x1 t2).
                        *********  unfold vswap. destruct (x == x0); try contradiction. destruct (x == x1); try contradiction. apply aeq_m_subst_eq.
                          ********** apply aeq_sym. apply swap_reduction; auto.
                          ********** apply aeq_sym. apply swap_reduction; auto.
                        ********* apply aeq_sym. apply aeq_swap_m_subst.
                    ******* apply aeq_sym. apply aeq_swap_m_subst.
          ** apply aeq_sym. apply m_subst_abs_neq; try assumption. apply notin_union_3.
            *** apply fv_nom_remove; auto.
            *** auto.
    - repeat rewrite m_subst_app. apply aeq_app.
      + apply H. simpl. lia.
      + apply H. simpl. lia.
    - destruct (x == z).
      + subst. repeat rewrite m_subst_sub_eq. apply aeq_sub_same.
        * reflexivity.
        * apply H. simpl. lia.
      + apply aeq_trans with (let (z0,_) := (atom_fresh (Metatheory.union (fv_nom t3) (Metatheory.union (fv_nom t4)
               (Metatheory.union (fv_nom t1) (Metatheory.union (fv_nom t2) (Metatheory.union (singleton z) 
              (singleton x))))))) in (({x := t1} ([z0 := {x := t2} t4] ({x := t2} swap z z0 t3))))).
        * default_simp. apply aeq_m_subst_out. apply m_subst_sub_neq; default_simp.
        * default_simp. apply aeq_trans with ([x0 := {x := {x := t1} t2} t4] ({x := {x := t1} t2} swap z x0 t3)).
          ** apply aeq_trans with ([x0 := {x := t1} ({x := t2} t4)] ({x := t1} swap x0 x0 ({x := t2} swap z x0 t3))).
            *** apply m_subst_sub_neq; default_simp. repeat apply notin_union_3; default_simp. apply fv_nom_remove; default_simp.
            *** rewrite swap_id. apply aeq_sub_same.
              **** apply H. rewrite swap_size_eq. lia.
              **** apply H. lia.
          ** apply aeq_sym. apply m_subst_sub_neq. 
            *** assumption.
            *** apply notin_union_3; try apply fv_nom_remove; default_simp.
Qed. 


Lemma m_subst_abs: forall t u x y, {x := u}(n_abs y t) =a if (x == y) then (n_abs y t) else let (z,_) := atom_fresh (fv_nom u `union` fv_nom (n_abs y t) `union` {{x}}) in n_abs z ({x := u}(swap y z t)).
Proof.
  intros t u x y. destruct (x == y).
  - subst. unfold m_subst. rewrite subst_rec_fun_equation. rewrite eq_dec_refl. apply aeq_refl.
  - unfold m_subst. rewrite subst_rec_fun_equation. destruct (x == y).
    + contradiction.
    + destruct (atom_fresh (union (fv_nom u) (union (fv_nom (n_abs y t)) (singleton x)))). apply aeq_refl.
Qed.

Lemma m_subst_sub: forall t1 t2 u x y, {x := u}(n_sub t1 y t2) =a if (x == y) then (n_sub t1 y ({x := u}t2)) else let (z,_) := atom_fresh (fv_nom u `union` fv_nom (n_sub t1 y t2) `union` {{x}}) in n_sub ({x := u}(swap y z t1)) z ({x := u}t2).
Proof.
  intros t1 t2 u x y. destruct (x == y).
  - subst. unfold m_subst. rewrite subst_rec_fun_equation. rewrite eq_dec_refl. apply aeq_refl.
  - unfold m_subst. rewrite subst_rec_fun_equation. destruct (x == y).
    + contradiction.
    + simpl. destruct (atom_fresh (union (fv_nom u) (union (fv_nom (n_sub t1 y t2)) (singleton x)))). apply aeq_refl.
Qed.

Lemma aeq_m_subst_out_neq: forall t1 t1' t2 x y, x <> y -> x `notin` (fv_nom t1') -> t1 =a (swap x y t1') -> ({x := t2}t1) =a ({y := t2}t1').
Proof. 
 intros t1 t1' t2 x y Hneq Hnotin Haeq. apply aeq_trans with ({x := t2} swap x y t1').
    - apply aeq_m_subst_out. assumption.
    - assert (Hnotin' := Hnotin). 
      assert (Haeq': t1' =a swap x y t1).
      {
        apply aeq_swap2 with x y. rewrite swap_involutive. apply aeq_sym. assumption.
      }
      apply aeq_fv_nom in Haeq'. rewrite Haeq' in Hnotin'. clear Haeq Haeq'.
      generalize dependent y. generalize dependent x. generalize dependent t2. generalize dependent t1.
      induction t1' as [ z | t1' z IH | t1' t1'' IH | t1' t1'' z IH] using n_sexp_size_induction.
      + intros t1 t2 x Hnotin y Hneq Hnotin'. simpl in *. unfold vswap. destruct (z == x).
        * subst. apply notin_singleton_1 in Hnotin. contradiction.
        * destruct (z == y).
          ** subst. repeat rewrite m_subst_var_eq. apply aeq_refl.
          ** repeat rewrite m_subst_var_neq.
             *** apply aeq_refl.
             *** assumption.
             *** assumption.
      + intros t1 t2 x Hnotin y Hneq Hnotin'. simpl in *. apply notin_remove_1 in Hnotin. destruct Hnotin as [Heq | Hnotin].
        * subst. unfold vswap. rewrite eq_dec_refl. apply aeq_trans with (let (z,_) := (atom_fresh (Metatheory.union (fv_nom t2) (Metatheory.union (fv_nom t1') (Metatheory.union (fv_nom (swap x y t1)) (Metatheory.union (singleton y) (singleton x)))))) in n_abs z ({y := t2} (swap x z t1'))).
          ** default_simp. assert (Hneq': x0 <> x). { repeat apply notin_union_2 in n. apply notin_singleton_1 in n. apply aux_not_equal. assumption. }
             apply aeq_trans with (n_abs x0 ({x := t2}(swap y x0 (swap x y t1')))).
             *** apply m_subst_abs_neq.
                 **** assumption.
                 **** apply notin_union.
                      ***** apply notin_union_1 in n. assumption.
                      ***** apply notin_union.
                      ****** simpl. apply notin_remove_2. apply fv_nom_remove_swap. 
                      ******* apply notin_union_2 in n. apply notin_union_2 in n. apply notin_union_2 in n. apply notin_union_1 in n. apply notin_singleton_1 in n. apply aux_not_equal. assumption.
                      ******* assumption.
                      ******* apply notin_union_2 in n. apply notin_union_1 in n. assumption.
                      ****** apply notin_singleton. apply aux_not_equal. assumption.
             *** apply aeq_abs_same. rewrite (swap_symmetric _ y x0). rewrite (swap_symmetric _ x y). rewrite shuffle_swap.
                 **** rewrite (swap_symmetric _ x0 x). rewrite shuffle_swap.
                      ***** apply IH with t1.
                      ****** simpl. rewrite swap_size_eq. lia.
                      ****** apply fv_nom_remove_swap_inc.
                      ******* apply aux_not_equal. assumption.
                      ******* apply notin_union_2 in n. apply notin_union_1 in n. assumption.
                      ****** assumption.
                      ****** assumption.
                      ***** assumption.
                      ***** apply notin_union_2 in n. apply notin_union_2 in n. apply notin_union_2 in n. apply notin_union_1 in n. apply notin_singleton_1 in n. apply aux_not_equal. assumption. 
                 **** assumption.
                 **** apply aux_not_equal. assumption.
          ** default_simp. apply aeq_sym. apply m_subst_abs_neq.
             *** apply aux_not_equal. assumption.
             *** apply notin_union.
                 **** apply notin_union_1 in n. assumption.
                 **** apply notin_union.
                      ***** simpl. apply notin_remove_2. apply notin_union_2 in n. apply notin_union_1 in n. assumption.
                      ***** auto.
        * unfold vswap. destruct (z == x).
          ** subst.  apply aeq_trans with (let (z,_) := (atom_fresh (Metatheory.union (fv_nom t2) (Metatheory.union (fv_nom t1') (Metatheory.union (fv_nom (swap x y t1)) (Metatheory.union (singleton y) (singleton x)))))) in n_abs z ({y := t2} (swap x z t1'))).
          *** default_simp. assert (Hneq': x0 <> x). { repeat apply notin_union_2 in n. apply notin_singleton_1 in n. apply aux_not_equal. assumption. }
             apply aeq_trans with (n_abs x0 ({x := t2}(swap y x0 (swap x y t1')))).
             **** apply m_subst_abs_neq.
                 ***** assumption.
                 ***** apply notin_union.
                      ****** apply notin_union_1 in n. assumption.
                      ****** apply notin_union.
                      ******* simpl. apply notin_remove_2. apply fv_nom_remove_swap. 
                      ******** apply notin_union_2 in n. apply notin_union_2 in n. apply notin_union_2 in n. apply notin_union_1 in n. apply notin_singleton_1 in n. apply aux_not_equal. assumption.
                      ******** assumption.
                      ******** apply notin_union_2 in n. apply notin_union_1 in n. assumption.
                      ******* apply notin_singleton. apply aux_not_equal. assumption.
             **** apply aeq_abs_same. rewrite (swap_symmetric _ y x0). rewrite (swap_symmetric _ x y). rewrite shuffle_swap.
                 ***** rewrite (swap_symmetric _ x0 x). rewrite shuffle_swap.
                      ****** apply IH with t1.
                      ******* simpl. rewrite swap_size_eq. lia.
                      ******* apply fv_nom_remove_swap_inc.
                      ******** apply aux_not_equal. assumption.
                      ******** apply notin_union_2 in n. apply notin_union_1 in n. assumption.
                      ******* assumption.
                      ******* assumption.
                      ****** assumption.
                      ****** apply notin_union_2 in n. apply notin_union_2 in n. apply notin_union_2 in n. apply notin_union_1 in n. apply notin_singleton_1 in n. apply aux_not_equal. assumption. 
                 ***** assumption.
                 ***** apply aux_not_equal. assumption.
          *** default_simp. apply aeq_sym. apply m_subst_abs_neq.
             **** apply aux_not_equal. assumption.
             **** apply notin_union.
                 ***** apply notin_union_1 in n. assumption.
                 ***** apply notin_union.
                      ****** simpl. apply notin_remove_2. apply notin_union_2 in n. apply notin_union_1 in n. assumption.
                      ****** auto.
          ** destruct (z == y).
            *** subst. repeat rewrite m_subst_abs_eq. apply aeq_abs_diff; try assumption. rewrite swap_symmetric. apply aeq_refl.
            *** apply aeq_trans with (let (z0,_) := (atom_fresh (Metatheory.union (fv_nom t2) (Metatheory.union (fv_nom t1') (Metatheory.union (fv_nom (swap x y t1)) (Metatheory.union (singleton y) (singleton x)))))) in n_abs z0 ({y := t2} (swap z z0 t1'))).
              **** default_simp. apply aeq_trans with (n_abs x0 ({x := t2} swap z x0 (swap x y t1'))).
                ***** apply m_subst_abs_neq.
                  ****** apply aux_not_equal. assumption.
                  ****** repeat apply notin_union.
                  ******* apply notin_union_1 in n1. assumption.
                  ******* simpl. apply notin_remove_2. apply fv_nom_remove_swap.
                  ******** apply notin_union_2 in n1. apply notin_union_2 in n1. apply notin_union_2 in n1. apply notin_union_1 in n1. apply notin_singleton_1 in n1. apply aux_not_equal. assumption. 
                  ******** repeat apply notin_union_2 in n1. apply notin_singleton_1 in n1. apply aux_not_equal. assumption.
                  ******** apply notin_union_2 in n1. apply notin_union_1 in n1. assumption. 
                  ******* repeat apply notin_union_2 in n1. assumption.
                ***** apply aeq_abs_same. rewrite swap_symmetric_2; try auto. apply IH with t1.
                  ****** simpl. rewrite swap_size_eq. lia.
                  ****** apply fv_nom_remove_swap; auto.
                  ****** assumption.
                  ****** assumption. 
              **** default_simp. apply aeq_sym. apply m_subst_abs_neq. 
                ***** apply aux_not_equal. assumption. 
                ***** apply notin_union. 
                ****** apply notin_union_1 in n1. assumption.
                ****** apply notin_union.
                ******* simpl. apply notin_remove_2. apply notin_union_2 in n1. apply notin_union_1 in n1. assumption.
                ******* apply notin_union_2 in n1. apply notin_union_2 in n1. apply notin_union_2 in n1. apply notin_union_1 in n1. assumption.
      + intros t1 t2 x Hnotin y Hneq Hnotin'. simpl in *. repeat rewrite m_subst_app. apply aeq_app.
        * apply IH with t1.
          ** lia.
          ** apply notin_union_1 in Hnotin. assumption.
          ** assumption.
          ** assumption.
        * apply IH with t1. 
          ** lia.
          ** apply notin_union_2 in Hnotin. assumption.
          ** assumption.
          ** assumption.
      + intros t1 t2 x Hnotin y Hneq Hnotin'. simpl in *. unfold vswap. destruct (z == x).
        * apply aeq_trans with (let (z,_) := (atom_fresh (Metatheory.union (fv_nom t2) (Metatheory.union (fv_nom t1') (Metatheory.union (fv_nom (swap x y t1)) 
          (Metatheory.union (fv_nom t1'') (Metatheory.union (singleton y) (singleton x))))))) in ([z := {x := t2} swap x y t1''] ({x := t2} swap y z (swap x y t1')))).
          ** destruct (atom_fresh (union (fv_nom t2) (union (fv_nom t1') (union (fv_nom (swap x y t1)) (union (fv_nom t1'') (union (singleton y) (singleton x))))))).  
             apply m_subst_sub_neq.
            *** assumption.
            *** apply notin_union.
              **** apply notin_union_1 in n. assumption.
              **** apply notin_union.
              ***** simpl. apply notin_union.
              ****** apply notin_remove_2. apply fv_nom_remove_swap.
              ******* apply notin_union_2 in n. apply notin_union_2 in n. apply notin_union_2 in n. apply notin_union_2 in n. apply notin_union_1 in n. apply notin_singleton_1 in n. apply aux_not_equal. assumption.
              ******* repeat apply notin_union_2 in n. apply notin_singleton_1 in n. apply aux_not_equal. assumption.
              ******* apply notin_union_2 in n. apply notin_union_1 in n. assumption.
              ****** apply fv_nom_remove_swap.
              ******* apply notin_union_2 in n. apply notin_union_2 in n. apply notin_union_2 in n.  apply notin_union_2 in n.  apply notin_union_1 in n. apply notin_singleton_1 in n. apply aux_not_equal. assumption. 
              ******* repeat apply notin_union_2 in n. apply notin_singleton_1 in n. apply aux_not_equal. assumption.
              ******* apply notin_union_2 in n. apply notin_union_2 in n. apply notin_union_2 in n. apply notin_union_1 in n. assumption.  
              ***** repeat apply notin_union_2 in n. assumption.
          ** default_simp. pose proof m_subst_sub_neq. specialize (H t1' t1'' t2 y x x0). apply aeq_trans with ([x0 := {y := t2} t1''] ({y := t2} swap x x0 t1')).
            *** apply aeq_sub_same.
              **** rewrite (swap_symmetric _ y x0). rewrite (swap_symmetric _ x y). rewrite shuffle_swap; auto.
                   rewrite swap_symmetric. rewrite shuffle_swap; auto. apply IH with t1. 
                ***** simpl. rewrite swap_size_eq. lia.
                ***** apply fv_nom_remove_swap_inc; auto. 
                ***** assumption.
                ***** assumption.
              **** apply IH with t1; auto. lia.
            *** apply aeq_sym. apply aux_not_equal in Hneq. apply m_subst_sub_neq.
              **** assumption.
              **** apply notin_union.
                ***** apply notin_union_1 in n. assumption.
                ***** apply notin_union.
                ****** simpl. apply notin_union.
                ******* apply notin_union_2 in n. apply notin_union_1 in n. apply notin_remove_2. assumption.
                ******* apply notin_union_2 in n. apply notin_union_2 in n. apply notin_union_2 in n. apply notin_union_1 in n. assumption.
                ****** apply notin_union_2 in n. apply notin_union_2 in n. apply notin_union_2 in n. apply notin_union_2 in n. apply notin_union_1 in n. assumption. 
        * destruct (z == y).
          ** subst. repeat rewrite m_subst_sub_eq. apply aeq_sub_diff.
            *** apply IH with t1.
              **** lia.
              **** apply notin_union_2 in Hnotin. assumption.
              **** assumption.
              **** assumption.
            *** assumption.
            *** apply notin_union_1 in Hnotin. apply notin_remove_1 in Hnotin. destruct Hnotin.
              **** contradiction.
              **** assumption.
            *** rewrite swap_symmetric. apply aeq_refl.
          ** apply aeq_trans with (let (z',_) := (atom_fresh (Metatheory.union (fv_nom t2) (Metatheory.union (fv_nom t1') (Metatheory.union (singleton z)
          (Metatheory.union (fv_nom t1'') (Metatheory.union (singleton y) (singleton x))))))) in ([z' := {x := t2} swap x y t1''] ({x := t2} swap z z' (swap x y t1')))).
            *** destruct (atom_fresh (union (fv_nom t2) (union (fv_nom t1')
           (union (singleton z) (union (fv_nom t1'') (union (singleton y) (singleton x))))))). apply m_subst_sub_neq.
              **** apply aux_not_equal. assumption.
              **** apply notin_union.
              ***** apply notin_union_1 in n1. assumption.
              ***** apply notin_union.
              ****** simpl. apply notin_union.
              ******* apply notin_remove_2. apply fv_nom_remove_swap; auto.
              ******* apply fv_nom_remove_swap; auto.
              ****** repeat apply notin_union_2 in n1. assumption.
            *** default_simp. apply aeq_trans with ([x0 := {y := t2} t1''] ({y := t2} swap z x0 t1')).
              **** apply aeq_sub_same.
                ***** rewrite swap_symmetric_2; auto. apply IH with t1.
                  ****** rewrite swap_size_eq. lia.
                  ****** apply fv_nom_remove_swap; auto.
                  ****** assumption.
                  ****** assumption.
                ***** apply IH with t1.
                  ****** lia.
                  ****** apply notin_union_2 in Hnotin. assumption.
                  ****** assumption.
                  ****** apply notin_union_1 in Hnotin. apply notin_remove_1 in Hnotin. destruct Hnotin.
                  ******* subst. contradiction.
                  ******* assumption.
              **** apply aeq_sym. apply m_subst_sub_neq.
                ***** apply aux_not_equal. assumption.
                ***** apply notin_union.
                ****** apply notin_union_1 in n1. assumption.
                ****** apply notin_union; auto.
Qed.
(* end hide *)
(**
The next corollary stablishes the compatibility of the metasubstitution operation with $\alpha$-equivalence when the variables of the metasubstitutions are different: 
*)
Corollary aeq_m_subst_neq: forall t1 t1' t2 t2' x y, t2 =a t2' -> x <> y -> x `notin` fv_nom t1' -> t1 =a (swap x y t1') -> ({x := t2}t1) =a ({y := t2'}t1').
Proof.
  intros t1 t1' t2 t2' x y Haeq Hneq Hnotin Haeq'. apply aeq_trans with ({y := t2} t1').
  - apply aeq_m_subst_out_neq; assumption.
  - apply aeq_m_subst_in. assumption.
Qed.

(**

%\noindent% and the Substitution Lemma whose formalization was the main achievement of %\cite{limaFormalizedExtensionSubstitution2023}% together with several lemmas that formed the infrastructure concerning $\alpha$-equivalence and metasubstitution.

*)
Lemma m_subst_lemma: forall t1 t2 t3 x y, x <> y -> x `notin` (fv_nom t3) ->
                     ({y := t3}({x := t2}t1)) =a ({x := ({y := t3}t2)}({y := t3}t1)).
Proof.
  induction t1 as  [z | t11 z | t11 t12 | t11 t12 z] using n_sexp_induction. 
- intros t2 t3 x y Hneq Hfv. case (x == z).
  + intro Heq. subst. rewrite m_subst_var_eq. case (y == z).
      * intro Heq. subst. contradiction.
      * intro Hneq'. rewrite m_subst_var_neq.
        ** rewrite m_subst_var_eq. apply aeq_refl.
        ** assumption.
  + intro Hneq'. case (x == z).
      * intro Heq. subst. contradiction.
      * intro Hneq''. rewrite m_subst_var_neq.
        ** case (y == z). 
           *** intro Heq. subst. rewrite m_subst_var_eq. apply aeq_sym. apply m_subst_notin. assumption.
           *** intro Hneq'''. repeat rewrite m_subst_var_neq.
               **** apply aeq_refl.
               **** apply aux_not_equal. assumption.
               **** apply aux_not_equal. assumption.
        ** apply aux_not_equal. assumption.
- intros t2 t3 x y Hneq Hfv. case (z == x). 
    + intro Heq. subst. rewrite m_subst_abs_eq. apply aeq_sym. apply m_subst_notin. apply fv_nom_remove. 
        * assumption.
        * apply notin_remove_2. simpl. apply notin_remove_3. reflexivity.
    + intro Hneq'. destruct (y == z). 
      * subst. rewrite m_subst_abs_eq. pose proof m_subst_abs_neq as Habs. pick fresh w for (union (fv_nom t3) (union (fv_nom t2) (union (fv_nom (n_abs z t11)) (singleton x)))). specialize (Habs t11 t2 x z w). apply aeq_trans with ({z := t3} n_abs w ({x := t2} swap z w t11)). 
        ** apply aeq_m_subst_out. apply Habs. 
           *** assumption.
           *** apply notin_union_2 in Fr. assumption.
        ** destruct (z == w). 
           *** subst. rewrite swap_id. rewrite m_subst_abs_eq. pose proof m_subst_abs_neq as H'. specialize (H' t11 ({w := t3}t2) x w w). rewrite swap_id in H'. rewrite H'.
               **** apply aeq_abs_same. assert (Fr' := Fr). apply notin_union_2 in Fr'. apply notin_union_1 in Fr'. apply aeq_m_subst_in. apply aeq_sym. apply m_subst_notin. assumption.
               **** assumption.
               **** apply notin_union.
                    ***** apply fv_nom_remove.
                    ****** apply notin_union_1 in Fr. assumption.
                    ****** apply notin_remove_3. reflexivity.
                    ***** apply notin_union.
                    ****** simpl. apply notin_remove_3. reflexivity.
                    ****** apply notin_singleton. assumption.
           *** pose proof m_subst_abs_neq as Habs'. specialize (Habs' t11 ({z := t3}t2) x z w). rewrite Habs'. 
               **** pose proof m_subst_abs_neq as H'. specialize (H' ({x := t2} swap z w t11) t3 z w w). rewrite swap_id in H'. rewrite H'.
                    ***** apply aeq_abs_same. apply aeq_trans with ({x := {z := t3} t2}({z := t3}(swap z w t11))).
                    ****** apply H.
                    ******* rewrite swap_size_eq. reflexivity.
                    ******* assumption.
                    ******* assumption.
                    ****** apply aeq_m_subst_out. apply m_subst_notin. apply fv_nom_swap. apply notin_union_2 in Fr. apply notin_union_2 in Fr. apply notin_union_1 in Fr. simpl in Fr. apply notin_remove_1 in Fr. destruct Fr.
                    ******* contradiction.
                    ******* assumption.
                    ***** assumption.
                    *****  apply notin_union.
                    ****** apply notin_union_1 in Fr. assumption.
                    ****** apply notin_union.
                    ******* simpl. apply notin_remove_3. reflexivity.
                    ******* apply notin_singleton. assumption.
               **** apply aux_not_equal. assumption.
               **** apply notin_union.
                    ***** apply fv_nom_remove.
                    ****** apply notin_union_1 in Fr. assumption.
                    ****** apply notin_remove_2. apply notin_union_2 in Fr. apply notin_union_1 in Fr. assumption. 
                    ***** apply notin_union.
                    ****** simpl. apply notin_remove_2. apply notin_union_2 in Fr. apply notin_union_2 in Fr.  apply notin_union_1 in Fr. simpl in Fr. apply diff_remove_2 in Fr.
                    ******* assumption.
                    ******* apply not_eq_sym. assumption.
                    ****** apply notin_singleton. repeat apply notin_union_2 in Fr. apply notin_singleton_1 in Fr. assumption.          
      * pose proof m_subst_abs_neq as Habs. pick fresh w for (union (fv_nom t3) (union (fv_nom t2) (union (fv_nom (n_abs z t11)) (union (singleton x) (singleton y))))). specialize (Habs t11 t2 x z w). apply aeq_trans with ({y := t3} n_abs w ({x := t2} swap z w t11)). 
        *** apply aeq_m_subst_out. apply Habs.
            **** apply aux_not_equal. assumption.
            **** apply notin_union_2 in Fr. pose proof AtomSetProperties.union_assoc as H'. specialize (H' (fv_nom (n_abs z t11)) (singleton x) (singleton y)). rewrite <- H' in Fr. rewrite <- AtomSetProperties.union_assoc in Fr. apply notin_union_1 in Fr. assumption.
        *** pose proof m_subst_abs_neq as Habs'. specialize (Habs' ({x := t2} swap z w t11) t3 y w w). rewrite swap_id in Habs'. rewrite Habs'. 
        **** pose proof m_subst_abs_neq as Habs''. specialize (Habs'' t11 t3 y z w). apply aeq_trans with ({x := {y := t3} t2} (n_abs w ({y := t3} swap z w t11))).
        ***** pose proof m_subst_abs_neq as Habs'''. specialize (Habs''' ({y := t3} swap z w t11) ({y := t3} t2) x w w). rewrite swap_id in Habs'''. rewrite Habs'''. 
        ****** apply aeq_abs_same. apply H.
        ******* rewrite swap_size_eq. reflexivity.
        ******* assumption.
        ******* assumption.
        ****** apply notin_union_2 in Fr. apply notin_union_2 in Fr. apply notin_union_2 in Fr. apply notin_union_1 in Fr. apply notin_singleton_1 in Fr. assumption.
        ****** apply notin_union.
        ******* apply fv_nom_remove.
        ******** apply notin_union_1 in Fr. assumption.
        ******** apply notin_union_2 in Fr. apply notin_union_1 in Fr. apply notin_remove_2. assumption.
        ******* apply notin_union.
        ******** simpl. apply notin_remove_3. reflexivity.
        ******** apply notin_union_2 in Fr. apply notin_union_2 in Fr. apply notin_union_2 in Fr. apply notin_union_1 in Fr. assumption.
        ***** apply aeq_m_subst_out. apply aeq_sym. apply Habs''.
        ****** assumption.
        ****** apply notin_union.
        ******* apply notin_union_1 in Fr. assumption.
        ******* apply notin_union.
        ******** apply notin_union_2 in Fr. apply notin_union_2 in Fr. apply notin_union_1 in Fr. assumption.
        ******** repeat apply notin_union_2 in Fr. assumption. 
        **** repeat apply notin_union_2 in Fr. apply notin_singleton_1 in Fr. assumption.
        **** apply notin_union.
        ***** apply notin_union_1 in Fr. assumption.
        ***** apply notin_union.
        ****** simpl. apply notin_remove_3. reflexivity.
        ****** repeat apply notin_union_2 in Fr. assumption. 
- intros t2 t3 x y Hneq Hfv. repeat rewrite m_subst_app. apply aeq_app. 
  + apply IHt12; assumption.
  + apply IHt1_1; assumption.
- intros t2 t3 x y Hneq Hfv. case (z == x).
  + intro Heq. subst. rewrite m_subst_sub_eq. pick fresh w for (union (fv_nom t3) (union (fv_nom t2) (union (fv_nom ([x := t12]t11)) (singleton y)))). pose proof m_subst_sub_neq as Hsubneq. specialize (Hsubneq t11 t12 t3 y x w). apply aeq_trans with ({x := {y := t3} t2} ([w := {y := t3} t12] ({y := t3} swap x w t11))).
    * case (x == w). 
      ** intro Heq. subst. rewrite m_subst_sub_eq. rewrite swap_id. pose proof m_subst_sub_neq as Hsubneq'. specialize (Hsubneq' t11 ({w := t2} t12) t3 y w w). rewrite Hsubneq'. 
         *** apply aeq_sub_same. 
             **** rewrite swap_id. apply aeq_refl. 
             **** apply IHt1_1; assumption. 
         *** apply aux_not_equal. assumption.
         *** apply notin_union.
             **** apply notin_union_1 in Fr. assumption.
             **** apply notin_union.
                  ***** simpl. apply notin_union.
                  ****** apply notin_remove_3. reflexivity.
                  ****** apply fv_nom_remove.
                  *******  apply notin_union_2 in Fr. apply notin_union_1 in Fr. assumption.
                  ******* apply notin_remove_3. reflexivity.
                  ***** repeat apply notin_union_2 in Fr. assumption.
      ** intro Hneq'. pose proof m_subst_sub_neq as Hsubneq'. specialize (Hsubneq' ({y := t3} swap x w t11) ({y := t3} t12) ({y := t3} t2) x w w). rewrite swap_id in Hsubneq'. rewrite Hsubneq'. 
         *** pose proof m_subst_sub_neq as Hsubneq''. specialize (Hsubneq'' t11 ({x := t2} t12) t3 y x w). rewrite Hsubneq''.
             **** apply aeq_sub_same. 
                  ***** apply aeq_sym. apply m_subst_notin. apply fv_nom_remove.
                  ******* assumption.
                  ******* apply notin_remove_2. apply fv_nom_swap. apply notin_union_2 in Fr. apply notin_union_2 in Fr. apply notin_union_1 in Fr. simpl in Fr. apply notin_union_1 in Fr. apply notin_remove_1 in Fr. destruct Fr.
                  ******** contradiction.
                  ******** assumption.
             ***** apply IHt1_1; assumption. 
         **** apply aux_not_equal. assumption.
         **** apply notin_union.
                  ***** apply notin_union_1 in Fr. assumption.
                  ***** apply notin_union.
                  ****** simpl. apply notin_union.
                  ******* apply notin_remove_2. apply notin_union_2 in Fr. apply notin_union_2 in Fr. apply notin_union_1 in Fr. simpl in Fr. apply notin_union_1 in Fr. apply notin_remove_1 in Fr. destruct Fr.
                  ******** contradiction.
                  ******** assumption.
                  ******* apply fv_nom_remove.
                  ******** apply notin_union_2 in Fr. apply notin_union_1 in Fr. assumption.
                  ******** apply notin_remove_2. apply notin_union_2 in Fr. apply notin_union_2 in Fr. apply notin_union_1 in Fr. simpl in Fr. apply notin_union_2 in Fr. assumption.
                  ****** repeat apply notin_union_2 in Fr. assumption.
         *** assumption.
         *** apply notin_union.
             **** apply fv_nom_remove.
                  ***** apply notin_union_1 in Fr. assumption.
                  ***** apply notin_remove_2. apply notin_union_2 in Fr. apply notin_union_1 in Fr. assumption.
                  **** apply notin_union.
                       ***** simpl. apply notin_union.
                       ****** apply notin_remove_3. reflexivity.
                       ****** apply fv_nom_remove.
                       ******* apply notin_union_1 in Fr. assumption.
                       ******* apply notin_remove_2. apply notin_union_2 in Fr. apply notin_union_2 in Fr. apply notin_union_1 in Fr. simpl in Fr. apply notin_union_2 in Fr. assumption.
                       ***** apply notin_singleton. assumption.
    * apply aeq_m_subst_out. rewrite Hsubneq.                 
      ** apply aeq_sub_same.
         *** apply aeq_refl.
         *** apply aeq_refl.
      ** apply aux_not_equal. assumption.
      ** apply notin_union.
         *** apply notin_union_1 in Fr. assumption.
         *** apply notin_union.
             **** simpl. apply notin_union.
                  ***** case (w == x).
                  ****** intro Heq. subst. apply notin_remove_3. reflexivity.
                  ****** intro Hneq'. apply notin_remove_2. apply notin_union_2 in Fr. apply notin_union_2 in Fr. apply notin_union_1 in Fr. simpl in Fr. apply notin_union_1 in Fr. apply notin_remove_1 in Fr. destruct Fr.
                  ******* symmetry in H0. contradiction.
                  ******* assumption.
                  ***** apply notin_union_2 in Fr. apply notin_union_2 in Fr. apply notin_union_1 in Fr. simpl in Fr. apply notin_union_2 in Fr. assumption.
             **** repeat apply notin_union_2 in Fr. assumption.
  + intro Hneq'. pick fresh w for (union (fv_nom t3) (union (fv_nom t2) (union (fv_nom ([z := t12]t11)) (union (singleton x) (singleton y))))). pose proof m_subst_sub_neq as Hsubneq. specialize (Hsubneq t11 t12 t2 x z w). apply aeq_trans with ({y := t3} ([w := {x := t2} t12] ({x := t2} swap z w t11))).
    * apply aeq_m_subst_out. pose proof m_subst_sub_neq as Hsubneq'. specialize (Hsubneq' t11 t12 t2 x z w). rewrite Hsubneq'.
      ** apply aeq_refl.
      ** apply aux_not_equal. assumption.
      ** apply notin_union.
         *** apply notin_union_2 in Fr. apply notin_union_1 in Fr. assumption.
         *** apply notin_union.
             **** simpl. apply notin_union.
                  ***** case (w == z).
                  ****** intro Heq. subst. apply notin_remove_3. reflexivity.
                  ****** intro Hneq''. apply notin_remove_2. apply notin_union_2 in Fr. apply notin_union_2 in Fr. apply notin_union_1 in Fr. simpl in Fr. apply notin_union_1 in Fr. apply notin_remove_1 in Fr. destruct Fr.
                  ******* symmetry in H0. contradiction.
                  ******* assumption.
                  ***** apply notin_union_2 in Fr. apply notin_union_2 in Fr. apply notin_union_1 in Fr. simpl in Fr. apply notin_union_2 in Fr. assumption.
             **** apply notin_union_2 in Fr. apply notin_union_2 in Fr. apply notin_union_2 in Fr. apply notin_union_1 in Fr. assumption.
    * case (y == z). 
      ** intro Heq. subst. rewrite m_subst_sub_eq.  pose proof m_subst_sub_neq as Hsubneq'. specialize (Hsubneq' ({x := t2} swap z w t11) ({x := t2} t12) t3 z w w). rewrite swap_id in Hsubneq'. rewrite Hsubneq'.
         *** pose proof m_subst_sub_neq as Hsubneq''. specialize (Hsubneq'' t11 ({z := t3} t12) ({z := t3} t2) x z w). rewrite Hsubneq''.
             **** apply aeq_sub_same.
                  ***** apply aeq_trans with ({x := {z := t3} t2} ({z := t3}(swap z w t11))).
                  ****** apply H.
                  ******* rewrite swap_size_eq. reflexivity.
                  ******* assumption.
                  ******* assumption.
                  ****** apply aeq_m_subst_out. apply m_subst_notin. apply fv_nom_swap. pose proof Fr as Fr'. repeat apply notin_union_2 in Fr'. apply notin_singleton_1 in Fr'. apply notin_union_2 in Fr. apply notin_union_2 in Fr. apply notin_union_1 in Fr. simpl in Fr. apply notin_union_1 in Fr. apply notin_remove_1 in Fr. destruct Fr.
                  ******* contradiction.
                  ******* assumption.
                  ***** apply IHt1_1; assumption.
                  **** assumption.
                  **** apply notin_union.
                       ***** apply fv_nom_remove.
                       ****** apply notin_union_1 in Fr. assumption.
                       ******  apply notin_remove_2. apply notin_union_2 in Fr. apply notin_union_1 in Fr. assumption.
                       ***** apply notin_union.
                       ****** simpl. apply notin_union.
                       ******* pose proof Fr as Fr'. repeat apply notin_union_2 in Fr'. apply notin_singleton_1 in Fr'. apply notin_union_2 in Fr. apply notin_union_2 in Fr. apply notin_union_1 in Fr. simpl in Fr. apply notin_union_1 in Fr. apply notin_remove_1 in Fr. destruct Fr.
                       ******** contradiction.
                       ******** apply notin_remove_2. assumption.
                       ******* apply fv_nom_remove.
                       ******** apply notin_union_1 in Fr. assumption.
                       ******** apply notin_remove_2. apply notin_union_2 in Fr. apply notin_union_2 in Fr. apply notin_union_1 in Fr. simpl in Fr. apply notin_union_2 in Fr. assumption.
                       ****** apply notin_union_2 in Fr. apply notin_union_2 in Fr. apply notin_union_2 in Fr. apply notin_union_1 in Fr. assumption.
         *** repeat apply notin_union_2 in Fr. apply notin_singleton_1 in Fr. assumption.
         *** apply notin_union.
             **** apply notin_union_1 in Fr. assumption.
             **** apply notin_union.
                  ***** simpl. apply notin_union.
                  ****** apply notin_remove_3. reflexivity.
                  ****** apply fv_nom_remove.
                  ******* apply notin_union_2 in Fr. apply notin_union_1 in Fr. assumption.
                  ******* apply notin_remove_2. apply notin_union_2 in Fr. apply notin_union_2 in Fr. apply notin_union_1 in Fr. simpl in Fr. apply notin_union_2 in Fr. assumption.
                  ***** repeat apply notin_union_2 in Fr. assumption.                
      ** intro Hneq''. pose proof m_subst_sub_neq as Hsubneq'. specialize (Hsubneq' t11 t12 t3 y z w). apply aeq_trans with ({x := {y := t3} t2} ([w := {y := t3} t12] ({y := t3} swap z w t11))).
         ***  pose proof m_subst_sub_neq as Hsubneq''. specialize (Hsubneq'' ({x := t2} swap z w t11) ({x := t2} t12) t3 y w w). rewrite swap_id in Hsubneq''. rewrite Hsubneq''.
              **** pose proof m_subst_sub_neq as Hsubneq'''. specialize (Hsubneq''' ({y := t3} swap z w t11) ({y := t3} t12) ({y := t3} t2) x w w). rewrite swap_id in Hsubneq'''. rewrite Hsubneq'''.
                   ***** apply aeq_sub_same.
                   ****** apply H.
                   ******* rewrite swap_size_eq. reflexivity.
                   ******* assumption.
                   ******* assumption.
                   ****** apply IHt1_1.
                   ******* assumption.
                   ******* assumption.
                   ***** apply notin_union_2 in Fr. apply notin_union_2 in Fr. apply notin_union_2 in Fr. apply notin_union_1 in Fr. apply notin_singleton_1 in Fr. assumption.
                   ***** apply notin_union.
                   ****** apply fv_nom_remove.
                   ******* apply notin_union_1 in Fr. assumption.
                   ******* apply notin_remove_2. apply notin_union_2 in Fr. apply notin_union_1 in Fr. assumption.
                   ****** apply notin_union.
                   ******* simpl. apply notin_union.
                   ******** apply notin_remove_3. reflexivity.
                   ******** apply fv_nom_remove.
                   ********* apply notin_union_1 in Fr. assumption.
                   ********* apply notin_remove_2. apply notin_union_2 in Fr. apply notin_union_2 in Fr. apply notin_union_1 in Fr. simpl in Fr. apply notin_union_2 in Fr. assumption.
                   ******* apply notin_union_2 in Fr. apply notin_union_2 in Fr. apply notin_union_2 in Fr. apply notin_union_1 in Fr. assumption.                 
                   **** repeat apply notin_union_2 in Fr. apply notin_singleton_1 in Fr. assumption.
                   **** apply notin_union.
                        ***** apply notin_union_1 in Fr. assumption.
                        ***** apply notin_union.
                        ****** simpl. apply notin_union.
                        ******* apply notin_remove_3. reflexivity.
                        ******* apply fv_nom_remove.
                        ******** apply notin_union_2 in Fr. apply notin_union_1 in Fr. assumption.
                        ******** apply notin_remove_2. apply notin_union_2 in Fr. apply notin_union_2 in Fr. apply notin_union_1 in Fr. simpl in Fr. apply notin_union_2 in Fr. assumption.
                        ****** repeat apply notin_union_2 in Fr. assumption.
         *** apply aeq_m_subst_out. apply aeq_sym. apply Hsubneq'.
             **** assumption.
             **** apply notin_union.
                  ***** apply notin_union_1 in Fr. assumption.
                  ***** apply notin_union.
                  ****** simpl. apply notin_union.
                  ******* case (w == z).
                  ******** intro Heq. subst. apply notin_remove_3. reflexivity.
                  ******** intro Hneq'''. apply notin_union_2 in Fr. apply notin_union_2 in Fr. apply notin_union_1 in Fr. simpl in Fr. apply notin_union_1 in Fr. apply notin_remove_1 in Fr. destruct Fr.
                  ********* symmetry in H0. contradiction.
                  ********* apply notin_remove_2. assumption.
                  ******* apply notin_union_2 in Fr. apply notin_union_2 in Fr. apply notin_union_1 in Fr. simpl in Fr. apply notin_union_2 in Fr. assumption.
                  ****** repeat apply notin_union_2 in Fr. assumption.
Qed.

(**

The reflexive-transitive closure of a binary relation $R$ is defined as
%\begin{mathpar}
 \inferrule*[Right={({\rm\it refl})}]{~}{t \tto t} \and  \inferrule*[Right={({\rm\it rtrans})}]{t_1 \to t_2 \and t_2 \tto t_3}{t_1 \tto t_3} 
\end{mathpar}%

Since we are working modulo $\alpha$-equivalence, an application of the axiom (refl) must account for the fact that a term reduces to itself in zero steps, as well as to any other term within its $\alpha$-equivalence class. To address this, we define the reflexive-transitive closure of a binary relation modulo $\alpha$-equivalence as follows:
%\begin{mathpar}
 \inferrule*[Right={({\rm\it refl})}]{t_1 =_\alpha t_2}{t_1 \tto t_2} \and  \inferrule*[Right={({\rm\it rtrans})}]{t_1 \to t_2 \and t_2 \tto t_3}{t_1 \tto t_3} \and  \inferrule*[Right={({\rm\it rtrans\_aeq})}]{t_1 =_\alpha t_2 \and t_2 \tto t_3}{t_1 \tto t_3} 
\end{mathpar}%

%\noindent% and the corresponding Coq definition is as follows:
*)
Inductive refltrans (R: Rel n_sexp) : Rel n_sexp :=
| refl: forall t1 t2, t1 =a t2 -> refltrans R t1 t2
| rtrans: forall t1 t2 t3, R t1 t2 -> refltrans R t2 t3 -> refltrans R t1 t3
| rtrans_aeq: forall t1 t2 t3, t1 =a t2 -> refltrans R t2 t3 -> refltrans R t1 t3.
(* begin hide *)
Lemma refltrans_refl {R: Rel n_sexp}: forall t, refltrans R t t.
Proof.
  intro t. apply refl. apply aeq_refl.
Qed.  
  
Lemma refltrans_composition {R: Rel n_sexp}: forall t1 t2 t3, refltrans R t1 t2 -> refltrans R t2 t3 -> refltrans R t1 t3.
Proof.
  intros t1 t2 t3 H1 H2. generalize dependent t3. induction H1.
  - intros t3 H'. apply rtrans_aeq with t2; assumption.
  - intros t' H'. apply rtrans with t2.
    + assumption.
    + apply IHrefltrans. assumption.
  - intros t' H'. apply rtrans_aeq with t2.
    + assumption.
    + apply IHrefltrans. assumption.
Qed.

Lemma refltrans_n_app_left {R: Rel n_sexp}: forall t1 t1' t2, (refltrans (ctx R) t1 t1') -> refltrans (ctx R) (n_app t1 t2) (n_app t1' t2).
Proof.
  induction 1.
  - apply refl. apply aeq_app.
    + assumption.
    + apply aeq_refl.
  - apply rtrans with (n_app t0 t2).
    + apply step_n_app_left. assumption.
    + apply IHrefltrans.
  - apply rtrans_aeq with (n_app t0 t2).
    + apply aeq_app.
      * assumption.
      * apply aeq_refl.
    + apply IHrefltrans.
Qed.

Lemma refltrans_n_app_right {R: Rel n_sexp}: forall t1 t2 t2', refltrans (ctx R) t2 t2' -> refltrans (ctx R) (n_app t1 t2) (n_app t1 t2').
Proof.
  induction 1.
  - apply refl. apply aeq_app.
    + apply aeq_refl.
    + assumption.
  - apply rtrans with (n_app t1 t2).
    + apply step_n_app_right. assumption.
    + apply IHrefltrans.
  - apply rtrans_aeq with (n_app t1 t2).
    + apply aeq_app.
      * apply aeq_refl.
      * assumption.
    + apply IHrefltrans.
Qed.

Lemma refltrans_n_app (R: Rel n_sexp): forall t1 t2 t3 t4, refltrans (ctx R) t1 t2 -> refltrans (ctx R) t3 t4 -> refltrans (ctx R) (n_app t1 t3) (n_app t2 t4).
Proof.
  intros. apply refltrans_composition with (n_app t2 t3).
    - apply refltrans_n_app_left. assumption.
    - apply refltrans_n_app_right. assumption.
Qed.

Lemma refltrans_n_abs {R: Rel n_sexp}: forall t t' x, refltrans (ctx R) t t' -> refltrans (ctx R) (n_abs x t) (n_abs x t').
Proof.
  induction 1.
  - apply refl. apply aeq_abs_same. assumption.
  - apply rtrans with (n_abs x t2).
    + apply step_n_abs. assumption.
    + apply IHrefltrans.
  - apply rtrans_aeq with (n_abs x t2).
    + apply aeq_abs_same. assumption.
    + apply IHrefltrans.
Qed.

Lemma refltrans_n_abs_diff {R: Rel n_sexp}: forall t1 t2 x y, x <> y -> x `notin` fv_nom t2 -> refltrans (ctx R) t1 (swap x y t2) -> refltrans (ctx R) (n_abs x t1) (n_abs y t2).
Proof.
  intros. inversion H1;subst.
    - apply refl. apply aeq_abs_diff.
      + assumption.
      + assumption.
      + rewrite swap_symmetric. assumption.
    - apply rtrans with (n_abs x t3).
      + apply step_n_abs. assumption.
      + apply refltrans_composition with (n_abs x (swap x y t2)).
        * apply refltrans_n_abs. assumption.
        * apply refl. apply aeq_abs_diff.
          ** assumption.
          ** assumption.
          ** rewrite swap_symmetric. apply aeq_refl.
    - apply refltrans_composition with (n_abs x (swap x y t2)).
      + apply refltrans_n_abs.  assumption.
      + apply refl. apply aeq_abs_diff.
        * assumption.
        * assumption.
        * rewrite swap_symmetric. apply aeq_refl.
Qed.

Lemma refltrans_n_sub_in (R: Rel n_sexp): forall t1 t2 t3 x, refltrans (ctx R) t2 t3 -> refltrans (ctx R) ([x := t2] t1) ([x := t3] t1).
Proof.
  intros t1 t2 t3 x H. induction H.
  - apply refl. apply aeq_sub_same.
    + apply aeq_refl.
    + assumption.
  - apply rtrans with ([x := t2] t1).
    + apply step_n_sub_in. assumption.
    + assumption.
  - apply refltrans_composition with ([x := t2] t1).
    + apply refl. apply aeq_sub_same.
      * apply aeq_refl.
      * assumption.
    + assumption.
Qed.
 
Lemma refltrans_n_sub_out (R: Rel n_sexp): forall t1 t2 t3 x, refltrans (ctx R) t2 t3 -> refltrans (ctx R) ([x := t1] t2) ([x := t1] t3).
Proof.
  intros t1 t2 t3 x H. induction H.
  - apply refl. apply aeq_sub_same.
    + assumption.
    + apply aeq_refl.
  - apply rtrans with ([x := t1] t2).
    + apply step_n_sub_out. assumption.
    + assumption.
  - apply refltrans_composition with ([x := t1] t2).
    + apply refl. apply aeq_sub_same.
      * assumption.
      * apply aeq_refl.
    + assumption.
Qed.
 
Lemma refltrans_n_sub (R: Rel n_sexp): forall t1 t2 t3 t4 x, refltrans (ctx R) t1 t3 -> refltrans (ctx R) t2 t4 -> refltrans (ctx R) (n_sub t1 x t2) (n_sub t3 x t4).
Proof.
  intros. apply refltrans_composition with (n_sub t3 x t2).
  - apply refltrans_n_sub_out. assumption.
  - apply refltrans_n_sub_in. assumption.
Qed.

Lemma refltrans_m_subst1 (R: Rel n_sexp): forall t1 t2 t3 x, refltrans (ctx R) t1 t2 -> refltrans (ctx R) ({x := t1}t3) ({x := t2}t3).
Proof.
  intros t1 t2 t3 x H. induction t3 using n_sexp_size_induction.
    - destruct (x0 == x).
      + subst. repeat rewrite m_subst_var_eq. assumption.
      + repeat rewrite m_subst_var_neq.
        * apply refltrans_refl.
        * assumption.
        * assumption.
    - destruct (x == z).
      + subst. repeat rewrite m_subst_abs_eq. apply refltrans_n_abs. apply refltrans_refl.
      + apply refltrans_composition with (let (z',_) := (atom_fresh (Metatheory.union (singleton z) (Metatheory.union (singleton x) 
        (Metatheory.union (fv_nom t3) (Metatheory.union (fv_nom t1) (fv_nom t2)))))) in (n_abs z' ({x := t1} swap z z' t3))).
          * default_simp. apply refl. apply m_subst_abs_neq; default_simp.
          * default_simp. pose proof m_subst_abs_neq. apply refltrans_composition with (n_abs x0 ({x := t2} swap z x0 t3)).
            ** apply refltrans_n_abs. apply H0. rewrite swap_size_eq. lia.
            ** apply refl. apply aeq_sym. apply m_subst_abs_neq; default_simp.
    - repeat rewrite m_subst_app. apply refltrans_n_app.
      + apply H0. simpl. lia.
      + apply H0. simpl. lia. 
    - destruct (x == z).
      * subst. repeat rewrite m_subst_sub_eq. apply refltrans_n_sub_in. apply H0. simpl. lia.
      * apply refltrans_composition with (let (z',_) := (atom_fresh (Metatheory.union (singleton z) (Metatheory.union (singleton x) 
        (Metatheory.union (fv_nom ([z := t3_2] t3_1)) (Metatheory.union (fv_nom t1) (fv_nom t2)))))) in ([z' := {x := t1} t3_2] ({x := t1} swap z z' t3_1))).
            *** default_simp. apply refl. apply m_subst_sub_neq; default_simp.
            *** default_simp. apply refltrans_composition with ([x0 := {x := t2} t3_2] ({x := t2} swap z x0 t3_1)).
              **** apply refltrans_n_sub.
                ***** apply H0. rewrite swap_size_eq. lia.
                ***** apply H0. lia. 
              **** apply refl. apply aeq_sym. apply m_subst_sub_neq; default_simp.
Qed.
(* end hide *)  

(**

In the next section, we present the $\lambda_x$-calculus and its confluence proof. To do

*)
