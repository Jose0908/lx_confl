(* begin hide *)
Require Export Arith Lia.
Require Export Metalib.Metatheory.
Require Export Metalib.LibDefaultSimp.
Require Export Metalib.LibLNgen.

Require Import infra_nom.
Require Import ZtoConfl_nom.
(* end hide *)

(** * The $\lambda_x$ calculus with explicit substitutions *)

(**

The $\lambda_x$ calculus%\cite{blooPreservationStrongNormalisation1995,linsNewFormulaExecution1986,roseExplicitCyclicSubstitutions1992}% is the simplest extension of the $\lambda$-calculus with explicit substitutions. In this section, we will present its confluence proof via the compositional Z property%\cite{nakazawaCompositionalConfluenceProofs2016}%.

Calculi with explicit substitutions are formalisms that deconstruct the metasubstitution operation into finer-grained steps, thereby functioning as an intermediary between the $\lambda$-calculus and its practical implementations. In other words, these calculi shed light on the execution models of higher-order languages. In fact, the development of a calculus with explicit substitutions faithful to the $\lambda$-calculus, in the sense of the preservation of some desired properties were the main motivation for such a long list of calculi with explicit substitutions invented in the last decades %\cite{abadiExplicitSubstitutions1991,roseExplicitSubstitutionNames2011,benaissaLnCalculusExplicit1996,curienConfluencePropertiesWeak1996,munozConfluencePreservationStrong1996,kamareddineExtendingLcalculusExplicit1997a,blooExplicitSubstitutionEdge1999,davidLambdacalculusExplicitWeakening2001,kesnerTheoryExplicitSubstitutions2009a}%. The core idea is that $\beta$-reduction is divided into two parts, one that initiates the simulation of a $\beta$-step, and another that completes the simulation as suggested by the following figure:

%\begin{tcolorbox}
$\centerline{\xymatrix{(\lambda_x.t_1)\ t_2 \ar@{->}[rr]_{\beta} & & \metasub{t_1}{x}{t_2} \\
    (\lambda_x.t_1)\ t_2 \ar@{->}[r]_{\flavio{\tt beta}} & \esub{t_1}{x}{t_2} \ar@{->>}[r]_{\tt subst} & \metasub{t_1}{x}{t_2} \\}}$
\end{tcolorbox}%

In this figure, the [beta] step initiates the simulation of the $\beta$-reduction while the [subst] steps, forming a set of rules known as the _substitution calculus_, completes the simulation. In the case of the $\lambda_x$-calculus, the formalization of the [beta] step is done as follows: firstly, one reduces an application when its left hand side is an abstraction:

*)

Inductive betax : Rel n_sexp :=
 | step_betax : forall (t1 t2: n_sexp) (x: atom),
     betax (n_app  (n_abs x t1) t2)  (n_sub t1 x t2).

(**

%\noindent% then this reduction is done modulo $\alpha$-equivalence:

*)

Inductive betax_aeq: Rel n_sexp :=
| betax_aeq_step: forall t t' u u', t =a t' -> betax t' u' -> u' =a u -> betax_aeq t u.

(**

%\noindent% and finally, the [beta] step in the case of the $\lambda_x$-calculus is the contextual closure of the [beta_aeq] reduction as given by the following notation:

*)

Definition betax_ctx t u := ctx betax_aeq t u. 
Notation "t -->Bx u" := (betax_ctx t u) (at level 60).
Notation "t -->>Bx u" := (refltrans betax_ctx t u) (at level 60).

(**

%\begin{tcolorbox}
\begin{equation}\label{x:rules}
 \begin{array}{lcl}
 (\lambda_x.t_1)\ t_2 & \to_{Bx} & \esub{t_1}{x}{t_2}
\end{array}
\end{equation}
\end{tcolorbox}%


The substitution calculus of the $\lambda_x$-calculus, named [x]-calculus, is formed by the following rules, where $x \neq y$:

%\begin{tcolorbox}
\begin{equation}\label{x:rules}
 \begin{array}{lcll}
 \esub{y}{y}{t} & \to_{var} & t & \\
 \esub{x}{y}{t} & \to_{gc} & x & \\
 \esub{(\lambda_y.t_1)}{y}{t_2} & \to_{abs1} & \lambda_y.t_1 & \\
 \esub{(\lambda_x.t_1)}{y}{t_2} & \to_{abs2} & \lambda_x.(\esub{t_1}{y}{t_2}) & \mbox{, if } x \notin fv(t_2) \\
 \esub{(\lambda_x.t_1)}{y}{t_2} & \to_{abs3} & \lambda_z.(\esub{\swap{x}{z}{t_1}}{y}{t_2}) & \mbox{, where } z \mbox{ is a fresh variable, and } x \in fv(t_2) \\
 \esub{(t_1\ t_2)}{y}{t_3} & \to_{app} & (\esub{t_1}{y}{t_3})\ (\esub{t_2}{y}{t_3}) &
\end{array}
\end{equation}
\end{tcolorbox}%

In rule $abs2$, the condition that $z$ is a fresh variable means that $z$ is a new variable not present in the set $(fv(t_1)\cup fv(t_2) \cup \{x\} \cup \{y\}$. The notation used in %\cite{nakazawaCompositionalConfluenceProofs2016}% inherently handles $\alpha$-equivalence, requiring only one rule for abstraction: $\esub{(\lambda_x.t1)}{y}{t_2} \to \lambda_x.(\esub{t_1}{y}{t_2})$. In this rule assumes that bound variables are renamed as needed to avoid capturing free variables. In our formalization, this rule was divided into $abs1$, $abs2$ and $abs3$ to explicitly prevent variable capture. The corresponding Coq code is as follows:

*)

Inductive pix : n_sexp -> n_sexp -> Prop :=
| step_var : forall (t: n_sexp) (y: atom),
    pix (n_sub (n_var y) y t) t
| step_gc : forall (t: n_sexp) (x y: atom),
    x <> y -> pix (n_sub (n_var x) y t) (n_var x)
| step_abs1 : forall (t1 t2: n_sexp) (y : atom),
    pix (n_sub (n_abs y t1) y t2)  (n_abs y t1)
| step_abs2 : forall (t1 t2: n_sexp) (x y: atom),
    x <> y -> x `notin` fv_nom t2 ->
    pix (n_sub (n_abs x t1) y t2)  (n_abs x (n_sub t1 y t2))
| step_abs3 : forall (t1 t2: n_sexp) (x y z: atom),
    x <> y -> z <> x -> z <> y -> x `in` fv_nom t2 -> z `notin` fv_nom t1 -> z `notin` fv_nom t2 -> 
                   pix (n_sub (n_abs x t1) y t2)  (n_abs z (n_sub (swap x z t1) y t2))
| step_app : forall (t1 t2 t3: n_sexp) (y: atom),
    pix (n_sub (n_app t1 t2) y t3) (n_app (n_sub t1 y t3) (n_sub t2 y t3)).

(**

In a similar way to the rule [-->Bx], we define [-->x] as the contextual closure of the rules in the inductive definition [pix] modulo $\alpha$-equivalence, and [-->lx] as the union of [-->Bx] and [-->x].

 *)
(* begin hide *)
Inductive pix_aeq: Rel n_sexp :=
| pix_aeq_step: forall t t' u u', t =a t' -> pix t' u' -> u' =a u -> pix_aeq t u.

Definition pix_ctx t u := ctx pix_aeq t u. 
Notation "t -->x u" := (pix_ctx t u) (at level 60).
Notation "t -->>x u" := (refltrans pix_ctx t u) (at level 60).

Inductive betapi: Rel n_sexp :=
| b_rule : forall t u, betax_ctx t u -> betapi t u
| x_rule : forall t u, pix_ctx t u -> betapi t u.

Notation "t -->lx u" := (betapi t u) (at level 60).
Notation "t -->>lx u" := (refltrans betapi t u) (at level 60).

Lemma refltrans_lx_betax: forall t t', (t -->>Bx t') -> (t -->>lx t'). 
Proof.
  intros t t' H. induction H.
    - apply refl. assumption.
    - apply rtrans with t2.
      + apply b_rule. assumption.
      + assumption.
    - apply refltrans_composition with t2.
      + apply refl. assumption.
      + assumption.
Qed. 

Lemma refltrans_lx_pix: forall t t', t -->>x t' -> (t -->>lx t'). 
Proof.
    intros t t' H. induction H.
    - apply refl. assumption.
    - apply rtrans with t2.
      + apply x_rule. assumption.
      + assumption.
    - apply refltrans_composition with t2.
      + apply refl. assumption.
      + assumption.
Qed.

Lemma refltrans_n_abs_lx: forall t1 t2 x, t1 -->>lx t2 -> n_abs x t1 -->>lx n_abs x t2.
Proof.
  intros t1 t2 x H. induction H.
    - apply refl. apply aeq_abs_same. assumption.
    - apply refltrans_composition with (n_abs x t2).
      + clear H0. clear IHrefltrans. inversion H; subst.
        * apply refltrans_lx_betax. apply refltrans_n_abs. apply rtrans with t2; try apply refltrans_refl. assumption.
        * apply refltrans_lx_pix. apply refltrans_n_abs. apply rtrans with t2; try apply refltrans_refl. assumption.
      + assumption.
    - apply refltrans_composition with (n_abs x t2).
      + apply refl. apply aeq_abs_same. assumption.
      + assumption. 
Qed. 

Lemma refltrans_n_app_left_lx: forall (t1 t1' t2 : n_sexp), t1 -->>lx t1' -> (n_app t1 t2) -->>lx (n_app t1' t2).
Proof.
  intros t1 t1' t2 H. induction H.
    - apply refl. apply aeq_app; try assumption. apply aeq_refl.
    - apply refltrans_composition with (n_app t0 t2).
      + clear H0. clear IHrefltrans. inversion H; subst.
        * apply refltrans_lx_betax. apply refltrans_n_app_left. apply rtrans with t0; try apply refltrans_refl. assumption.
        * apply refltrans_lx_pix. apply refltrans_n_app_left. apply rtrans with t0; try apply refltrans_refl. assumption.
      + assumption.
    - apply refltrans_composition with (n_app t0 t2).
      + apply refl. apply aeq_app; try assumption. apply aeq_refl.
      + assumption. 
Qed.

Lemma refltrans_n_app_right_lx: forall (t1 t1' t2 : n_sexp), t1' -->>lx t2 -> (n_app t1 t1') -->>lx (n_app t1 t2).
Proof.
  intros t1 t1' t2 H. induction H.
    - apply refl. apply aeq_app; try assumption. apply aeq_refl.
    - apply refltrans_composition with (n_app t1 t2).
      + clear H0. clear IHrefltrans. inversion H; subst.
        * apply refltrans_lx_betax. apply refltrans_n_app_right. apply rtrans with t2; try apply refltrans_refl. assumption.
        * apply refltrans_lx_pix. apply refltrans_n_app_right. apply rtrans with t2; try apply refltrans_refl. assumption.
      + assumption.
    - apply refltrans_composition with (n_app t1 t2).
      + apply refl. apply aeq_app; try assumption. apply aeq_refl.
      + assumption. 
Qed. 
 
Lemma refltrans_n_app_lx: forall (t1 t2 t3 t4 : n_sexp), t1 -->>lx t3 -> t2 -->>lx t4 -> (n_app t1 t2) -->>lx (n_app t3 t4).
Proof.
  intros t1 t2 t3 t4 H1 H2. apply refltrans_composition with (n_app t1 t4).
    - apply refltrans_n_app_right_lx. assumption.
    - apply refltrans_n_app_left_lx. assumption.
Qed.

Lemma refltrans_n_sub_in_lx: forall (t1 t2 t3 : n_sexp) (x : atom), t2 -->>lx t3 -> ([x := t2] t1) -->>lx ([x := t3] t1).
Proof.
  intros t1 t2 t3 x H. induction H.
    - apply refl. apply aeq_sub_same; try assumption. apply aeq_refl.
    - apply refltrans_composition with ([x := t2] t1).
      + clear H0. clear IHrefltrans. inversion H; subst.
        * apply refltrans_lx_betax. apply refltrans_n_sub_in. apply rtrans with t2; try apply refltrans_refl. assumption.
        * apply refltrans_lx_pix. apply refltrans_n_sub_in. apply rtrans with t2; try apply refltrans_refl. assumption.
      + assumption.
    - apply refltrans_composition with ([x := t2] t1).
      + apply refl. apply aeq_sub_same; try assumption. apply aeq_refl.
      + assumption. 
Qed.

Lemma refltrans_n_sub_out_lx: forall (t1 t2 t3 : n_sexp) (x : atom), t2 -->>lx t3 -> ([x := t1] t2) -->>lx ([x := t1] t3).
Proof.
  intros t1 t2 t3 x H. induction H.
    - apply refl. apply aeq_sub_same; try assumption. apply aeq_refl.
    - apply refltrans_composition with ([x := t1] t2).
      + clear H0. clear IHrefltrans. inversion H; subst.
        * apply refltrans_lx_betax. apply refltrans_n_sub_out. apply rtrans with t2; try apply refltrans_refl. assumption.
        * apply refltrans_lx_pix. apply refltrans_n_sub_out. apply rtrans with t2; try apply refltrans_refl. assumption.
      + assumption.
    - apply refltrans_composition with ([x := t1] t2).
      + apply refl. apply aeq_sub_same; try assumption. apply aeq_refl.
      + assumption. 
Qed.  
 
Lemma refltrans_n_sub_lx: forall (t1 t2 t3 t4: n_sexp) (x : atom), t1 -->>lx t3 -> t2 -->>lx t4 -> ([x := t1] t2) -->>lx ([x := t3] t4).
Proof.
  intros t1 t2 t3 t4 x H1 H2. apply refltrans_composition with ([x := t1] t4).
    - apply refltrans_n_sub_out_lx. assumption.
    - apply refltrans_n_sub_in_lx. assumption.
Qed.
(* end hide *)
(**

The next lemma show that the explicit substitution implements the metasubstitution when [t1] is pure.

 *)

Lemma pure_pix: forall t1 x t2, pure t1 -> ([x := t2]t1) -->>x ({x := t2}t1).
Proof.
  induction t1 using n_sexp_size_induction. 
  - intros x' t2 H. unfold m_subst. rewrite subst_rec_fun_equation. destruct (x' == x).
    + subst. apply rtrans with t2.
      * apply step_redex. apply pix_aeq_step with ([x := t2] n_var x) t2.
        ** apply aeq_refl.
        ** apply step_var.
        ** apply aeq_refl.
      * apply refl. apply aeq_refl.
    + apply rtrans with (n_var x).
      * apply step_redex. apply pix_aeq_step with  ([x' := t2] n_var x) (n_var x).
        ** apply aeq_refl.
        ** apply step_gc. apply aux_not_equal. assumption.
        ** apply aeq_refl.        
      * apply refl. apply aeq_refl.
  - intros x t2 Hpure. unfold m_subst. rewrite subst_rec_fun_equation. destruct (x == z).
    + subst. apply rtrans with (n_abs z t1).
      * apply step_redex. apply pix_aeq_step with ([z := t2] n_abs z t1) (n_abs z t1).
        ** apply aeq_refl.
        ** apply step_abs1.
        ** apply aeq_refl.
      * apply refl. apply aeq_refl.
    + destruct (atom_fresh (Metatheory.union (fv_nom t2) (Metatheory.union (fv_nom (n_abs z t1)) (singleton x)))). pose proof in_or_notin as Hin. specialize (Hin z (fv_nom t2)). destruct Hin as [Hin | Hnotin].
      ** apply rtrans with (n_abs x0 ([x := t2](swap z x0 t1))).
         *** assert (Hnotin := n0). apply notin_union_2 in n0. apply notin_union_1 in n0. simpl in n0. apply notin_remove_1 in n0. case (z == x0).
             **** intro Heq. subst. rewrite swap_id. apply notin_union_1 in Hnotin. apply step_redex. apply pix_aeq_step with ([x := t2] n_abs x0 t1) (n_abs x0 ([x := t2] t1)).
                  ***** apply aeq_refl.
                  ***** apply step_abs2.
                  ****** apply aux_not_equal. assumption.
                  ****** assumption.
                  ***** apply aeq_refl.
             **** intro Hneq. destruct n0.
                  ***** contradiction.
                  ***** apply step_redex. apply pix_aeq_step with ([x := t2] n_abs z t1) (n_abs x0 ([x := t2] swap z x0 t1)).
                  ****** apply aeq_refl.
                  ****** apply step_abs3.
                  ******* apply aux_not_equal; assumption.
                  ******* apply aux_not_equal; assumption.
                  ******* repeat apply notin_union_2 in Hnotin. apply notin_singleton_1 in Hnotin. apply aux_not_equal; assumption.
                  ******* assumption.
                  ******* assumption.
                  ******* apply notin_union_1 in Hnotin. assumption.
                  ****** apply aeq_refl.
         *** apply refltrans_n_abs. apply H.
             **** rewrite swap_size_eq. simpl. lia.
             **** apply pure_swap. inversion Hpure; subst. assumption.
      ** apply rtrans with (n_abs z ([x := t2] t1)).
         *** apply step_redex. apply pix_aeq_step with ([x := t2] n_abs z t1) (n_abs z ([x := t2] t1)).
             **** apply aeq_refl.
             **** apply step_abs2.
                  ***** apply aux_not_equal; assumption.
                  ***** assumption.
             **** apply aeq_refl.
         *** assert (Hnotin' := n0). apply notin_union_2 in n0. apply notin_union_1 in n0. simpl in n0. apply notin_remove_1 in n0. destruct n0.
             **** subst. apply refltrans_n_abs. rewrite swap_id. apply H.
                  ***** simpl. lia.
                  ***** inversion Hpure; subst. assumption.
             **** apply refltrans_composition with (n_abs z ({x := t2} t1)).
                  ***** apply refltrans_n_abs. apply H.
                  ****** simpl. lia.
                  ****** inversion Hpure; subst. assumption.
                  ***** apply refl. case (z == x0) eqn: Hz.
                  ****** subst. apply aeq_abs_same. rewrite swap_id. apply aeq_refl.
                  ****** apply aeq_abs_diff.
                  ******* assumption.
                  ******* apply fv_nom_remove.
                  ******** assumption.
                  ******** apply notin_remove_2. apply fv_nom_remove_swap_inc.
                  ********* assumption.
                  ********* apply notin_union_2 in Hnotin'. apply notin_union_1 in Hnotin'. simpl in Hnotin'. apply notin_remove_1 in Hnotin'. destruct Hnotin' as [Heq | Hnotin'].
                  ********** contradiction.
                  ********** assumption.
                  ******* apply aeq_trans with (subst_rec_fun (swap x0 z (swap z x0 t1)) (swap x0 z t2) (vswap x0 z x)).
                  ******** rewrite (swap_symmetric _ x0 z). rewrite swap_involutive. rewrite vswap_neq.
                  ********* apply aeq_m_subst_in. apply aeq_sym. apply swap_reduction.
                  ********** apply notin_union_1 in Hnotin'. assumption.
                  ********** assumption.
                  ********* repeat apply notin_union_2 in Hnotin'. apply notin_singleton_1 in Hnotin'. apply aux_not_equal. assumption.
                  ********* apply aux_not_equal. assumption.
                  ******** apply aeq_sym. apply aeq_swap_m_subst.
  - intros x t2 Hpure. apply rtrans with (n_app ([x := t2]t1_1) ([x := t2]t1_2)).
    + apply step_redex. apply pix_aeq_step with ([x := t2] n_app t1_1 t1_2) (n_app ([x := t2] t1_1) ([x := t2] t1_2)).
      * apply aeq_refl.
      * apply step_app.
      * apply aeq_refl.
    + apply refltrans_composition with (n_app ({x := t2}t1_1) ({x := t2}t1_2)).
      * apply refltrans_composition with (n_app ({x := t2} t1_1) ([x := t2] t1_2)).
        ** apply refltrans_n_app_left. apply H.
           *** simpl. lia.
           *** inversion Hpure; subst. assumption.
        ** apply refltrans_n_app_right. apply H.
           *** simpl. lia.
           *** inversion Hpure; subst. assumption.           
      * apply refl. rewrite m_subst_app. apply aeq_refl.
  - intros x t2 Hpure. inversion Hpure.
Qed.
(* begin hide *)
Lemma ctx_betax_beta_pix: forall t t', t -->lx t' <-> (t -->Bx t' \/ t -->x t'). 
Proof.
  intros t t'. split.
    - intro H. induction H.
      + left. assumption.
      + right. assumption.
    - intro H. destruct H.
      + apply b_rule. assumption.
      + apply x_rule. assumption.  
Qed.

Lemma pure_pix_2: forall t1 x t2, pure t1 -> [x := t2]t1 -->>lx ({x := t2}t1).
Proof.
  intros t1 t2 x H. apply refltrans_lx_pix. apply pure_pix. assumption.
Qed.


Lemma refltrans_m_subst1_lx: forall t1 t2 t3 x, t1 -->>lx t2 -> ({x := t1}t3) -->>lx ({x := t2}t3).
Proof.
  intros t1 t2 t3 x H. induction H.
    - apply refl. apply aeq_m_subst_in. assumption.
    - apply refltrans_composition with ({x := t2} t3).
      + inversion H; subst.
        * apply refltrans_lx_betax. apply refltrans_m_subst1. apply rtrans with t2; try apply refltrans_refl. assumption.
        * apply refltrans_lx_pix. apply refltrans_m_subst1. apply rtrans with t2; try apply refltrans_refl. assumption.
      + assumption.
    - apply refltrans_composition with ({x := t2} t3).
      + apply refl. apply aeq_m_subst_in. assumption.
      + assumption.
Qed.
(* end hide *)

(**

The Z property is a promissing techique used to prove confluence of reduction systems %\cite{vanoostrom:LIPIcs.FSCD.2021.24,felgenhauerProperty2016,dehornoy2008z}%. Shortly, a function [f: n_sexp -> n_sexp] has the Z property for the binary relation [R] if the following diagram holds:

  $\centerline{\xymatrix{ t_1 \ar[r]_R & t_2 \ar@{.>>}[dl]^R\\ f t_1 \ar@{.>>}[r]_R & f t_2}}$

An extension of the Z property, known as _Compositional Z_ property gives a sufficient condition  for that a compositional function satisfies the Z property %\cite{nakazawaCompositionalConfluenceProofs2016}%. For the $\lambda_x$-calculus, we will prove that the following diagram holds:

%\begin{equation}\label{lx:zprop}
 \xymatrix{ t_1 \ar[r]_{lx} & t_2 \ar@{.>>}[dl]^{lx}\\ B(P\ t_1) \ar@{.>>}[r]_{lx} & B(P\ t_2)}
\end{equation}%

%\noindent% where $P$ (resp. $B$) is the complete permutation (resp. complete development) recursively defined as:

*)

Fixpoint P (t : n_sexp) := match t with
                           | n_var x => n_var x
                           | n_abs x t1 => n_abs x (P t1)
                           | n_app t1 t2 => n_app (P t1) (P t2)
                           | n_sub t1 x t2 => {x := (P t2)}(P t1)
                           end.

(**

%\noindent% and

*)

Fixpoint B (t : n_sexp) := match t with
                           | n_var x => n_var x
                           | n_abs x t1 => n_abs x (B t1)
                           | n_app t1 t2 => match t1 with
                                            | n_abs x t3 => {x := (B t2)}(B t3)
                                            | _ => n_app (B t1) (B t2)
                                            end
                           | n_sub t1 x t2 => n_sub (B t1) x (B t2)
                           end.

(* begin hide *)
Lemma notin_P: forall t x, x `notin` fv_nom t -> x `notin` fv_nom (P t).
Proof.
  induction t as [ y | y t1 IHt1 | t1 IHt1 t2 IHt2 | t1 IHt1 y t2  IHt2].
  - intros x Hnotin. simpl in *. assumption.
  - intros x Hnotin. simpl in *. apply notin_remove_1 in Hnotin. destruct Hnotin as [Heq | Hnotin].
    + subst. apply notin_remove_3. reflexivity.
    + apply notin_remove_2. apply IHt1. assumption. 
  - intros x Hnotin. simpl in *. apply notin_union.
    + apply notin_union_1 in Hnotin. apply IHt1; assumption.
    + apply notin_union_2 in Hnotin. apply IHt2; assumption.
  - intros x Hnotin. simpl in *. pose proof Hnotin as Hnotin'. apply notin_union_1 in Hnotin. apply notin_union_2 in Hnotin'. unfold m_subst. pose proof in_or_notin as Hor. specialize (Hor x (fv_nom (P t1))). destruct Hor.
    + apply fv_nom_remove.
      * apply IHt2; assumption.
      * apply notin_remove_1 in Hnotin. destruct Hnotin as [Heq | Hnotin]. 
        ** subst. apply notin_remove_3; reflexivity.
        ** apply notin_remove_2. apply IHt1. assumption. 
    + apply fv_nom_remove.
      * apply IHt2; assumption.
      * apply notin_remove_1 in Hnotin. destruct Hnotin as [Heq | Hnotin].
        ** subst. apply notin_remove_3; reflexivity.
        ** apply notin_remove_2. apply IHt1. assumption.
Qed.
(* end hide  *)

(**

The complete permutation function [P] and the complete development [B] have several interesting properties. In what follows, we will list the most relevant ones to show how to get the confluence proof for the $\lambda_x$-calculus. The first point to be noticed is that [P t] removes all explicit substitution of [t], therefore [P t] is a pure term:

 *)

Lemma pure_P: forall t, pure (P t).
Proof.
  induction t.
  - simpl. apply pure_var.
  - simpl. apply pure_abs. assumption.
  - simpl. apply pure_app; assumption.
  - simpl. apply pure_m_subst; assumption.
Qed.

Lemma aeq_swap_P: forall t x y, (P (swap x y t)) =a (swap x y (P t)).
Proof.
  induction t as [ z | z t1 IHt1 | t1 IHt1 t2 IHt2 | t1 IHt1 z t2  IHt2].
  - intros x y. simpl. apply aeq_refl.
  - intros x y. simpl. apply aeq_abs_same. apply IHt1.
  - intros x y. simpl. apply aeq_app.
    + apply IHt1.
    + apply IHt2.
  - intros x y. simpl. apply aeq_trans with  ({vswap x y z := (swap x y (P t2))} (swap x y (P t1))).
    + apply aeq_m_subst_eq.
      * apply IHt1.
      * apply IHt2.
    + apply aeq_sym. apply aeq_swap_m_subst.
Qed.

Lemma aeq_P: forall t1 t2, t1 =a t2 -> (P t1) =a (P t2).
Proof.
  induction 1.
  - apply aeq_refl.
  - simpl. apply aeq_abs_same. apply IHaeq.
  - simpl. apply aeq_abs_diff.
    + assumption.
    + apply notin_P. assumption.
    + apply aeq_trans with (P (swap y x t2)).
      * assumption.
      * apply aeq_swap_P.
  - simpl. apply aeq_app; assumption.
  - simpl. apply aeq_m_subst_eq; assumption.
  - simpl. apply aeq_m_subst_neq.
    + assumption.
    + assumption.
    + apply notin_P. assumption.
    + apply aeq_trans with (P (swap y x t1')).
      * assumption.
      * rewrite (swap_symmetric _ y x). apply aeq_swap_P.
Qed.


Lemma pure_B: forall t, pure t -> pure (B t).
Proof.
  intros t H. induction H as [ x | t1 t2 | x t1].
  - simpl. apply pure_var.
  - simpl. destruct t1.
    + simpl in *. apply pure_app;assumption.
    + apply pure_m_subst.
       * simpl in IHpure1. inversion IHpure1. assumption.
       * assumption.
    + apply pure_app;assumption.
    + simpl in IHpure1. inversion IHpure1.
  - simpl. apply pure_abs. assumption.
Qed.
(**

Pure terms are standard  $\lambda$-terms, that is, expressions constructed from variables, applications and abstractions. In the following subsection, we define a reduction rule similar to the $\beta$-reduction of the $\lambda$-calculus, but over [n_sexp] expressions.

*)

(** ** The $\beta$-reduction *)

(**

In this subsection, we define a reduction rule analogous to $\beta$-reduction in the $\lambda$-calculus modulo $\alpha$-equivalence. While it shares the same redex as the [-->Bx] rule, its contractum is a term with a metasubstitution. Like the original, this rule is also defined modulo $\alpha$-equivalence, and we refer to it as the $\beta$-rule.

*)

Inductive beta_redex : Rel n_sexp :=
| step_beta : forall (t1 t2: n_sexp) (x: atom),
    beta_redex (n_app  (n_abs x t1) t2)  ({x := t2}t1).

Inductive beta_aeq: Rel n_sexp :=
| beta_aeq_step: forall t t' u u', t =a t' -> beta_redex t' u' -> u' =a u -> beta_aeq t u.

Definition beta_ctx t u := ctx beta_aeq t u. 
Notation "t -->B u" := (beta_ctx t u) (at level 60).
Notation "t -->>B u" := (refltrans beta_ctx t u) (at level 60).

(* begin hide *)
Lemma fv_nom_beta: forall t1 t2 x, x `notin` fv_nom t1 -> t1 -->B t2 -> x `notin` fv_nom t2.
Proof.
  intros t1 t2 x Hnotin Hbeta. induction Hbeta.
  - inversion H; subst. inversion H1; subst. apply aeq_fv_nom in H0. simpl in H0. apply aeq_fv_nom in H2. simpl in H2. rewrite H0 in Hnotin. rewrite <- H2. clear H H0 H1 H2. apply fv_nom_remove.
    + apply notin_union_2 in Hnotin. assumption.
    + apply notin_union_1 in Hnotin. assumption.
  - simpl in *. apply notin_remove_1 in Hnotin. destruct Hnotin as [Heq | Hnotin].
    + subst. apply notin_remove_3. reflexivity.
    + apply notin_remove_2. apply IHHbeta. assumption.
  - simpl in *. apply notin_union.
    + apply notin_union_1 in Hnotin. apply IHHbeta. assumption.
    + apply notin_union_2 in Hnotin. assumption.
  - simpl in *. apply notin_union.
    + apply notin_union_1 in Hnotin. assumption.
    + apply notin_union_2 in Hnotin. apply IHHbeta. assumption.
  - simpl in *. apply notin_union.
    + apply notin_union_1 in Hnotin. apply notin_remove_1 in Hnotin. destruct Hnotin as [Heq | Hnotin].
      * subst. apply notin_remove_3. reflexivity.
      * apply notin_remove_2. apply IHHbeta. assumption.
    + apply notin_union_2 in Hnotin. assumption.
  - simpl in *. apply notin_union.
    + apply notin_union_1 in Hnotin. assumption.
    + apply notin_union_2 in Hnotin. apply IHHbeta. assumption.
Qed.

Lemma beta_var: forall t x, (n_var x) -->B t -> t = n_var x.
Proof.  
  intros t x H. inversion H; subst. inversion H0; subst. inversion H1; subst. inversion H2.
Qed.

Lemma beta_n_abs_alpha: forall t t' x, n_abs x t -->B t' -> exists y t'', t' = n_abs y t''.
Proof.  
  intros t t' x H. remember (n_abs x t) as t''. induction H.
  - inversion H; subst. apply aeq_n_abs in H0. destruct H0 as [y Habs]. destruct Habs as [t'' Habs]. rewrite Habs in H1. inversion H1.
  - inversion Heqt''; subst. exists x, t2. reflexivity.
  - inversion Heqt''.
  - inversion Heqt''.
  - inversion Heqt''.
  - inversion Heqt''.
Qed.

(**

One can choose to keep the external abstraction with the same name during a $\beta$-reduction:

*)
Lemma beta_n_abs: forall t t' x, n_abs x t -->B t' -> exists t'', t' = n_abs x t''.
Proof.  
  intros t t' x H. remember (n_abs x t) as t''. induction H.
  - inversion H; subst. apply aeq_n_abs in H0. destruct H0 as [y Habs]. destruct Habs as [t'' Habs]. rewrite Habs in H1. inversion H1.
  - inversion Heqt''; subst. exists t2. reflexivity.
  - inversion Heqt''.
  - inversion Heqt''.
  - inversion Heqt''.
  - inversion Heqt''.
Qed.

Lemma ctx_beta_swap: forall t1 t2 x y, t1 -->B t2 -> (swap x y t1) -->B (swap x y t2).
Proof.
  intros t1 t2 x y H. induction H.
    - inversion H; subst. inversion H1; subst. apply step_redex. apply beta_aeq_step with (swap x y (n_app (n_abs x0 t0) t3)) ({vswap x y x0 := swap x y t3} swap x y t0).
      + apply aeq_swap. assumption.
      + simpl. apply step_beta.
      + apply aeq_trans with (swap x y ({x0 := t3} t0)).
        * apply aeq_sym. apply aeq_swap_m_subst.        
        * apply aeq_swap. assumption.
    - simpl. apply step_n_abs. apply IHctx.
    - simpl. apply step_n_app_left. apply IHctx.
    - simpl. apply step_n_app_right. apply IHctx.
    - simpl. apply step_n_sub_out. apply IHctx.
    - simpl. apply step_n_sub_in. apply IHctx.
Qed.

Lemma n_abs_step_beta: forall t1 t2 x, n_abs x t1 -->B n_abs x t2 -> t1 -->B t2.
Proof.
  intros t1 t2 x H. unfold beta_ctx in H. inversion H.
  - clear H1 H2 H. inversion H0. apply aeq_n_abs in H. destruct H as [y H]. destruct H as [t'' H]. rewrite H in H1. inversion H1.
  - assumption.
Qed.

Lemma n_abs_step_beta_alpha: forall t1 t2 x y, n_abs x t1 -->B n_abs y t2 -> t1 -->B (swap x y t2).
Proof.
  intros t1 t2 x y Hbeta. case (x == y).
  - intro Heq. subst. rewrite swap_id. apply n_abs_step_beta with y. assumption.
  - intro Hneq. inversion Hbeta; subst.
    + inversion H; subst. apply aeq_n_abs in H0. destruct H0 as [z Habs]. destruct Habs as [t3 Habs]. rewrite Habs in H1. inversion H1.
    + contradiction.
Qed.

Lemma n_abs_step_beta_alpha': forall t1 t2 x y, n_abs x t1 -->B n_abs y t2 -> t1 -->B t2.
Proof.
  intros t1 t2 x y Hbeta. case (x == y).
  - intro Heq. subst. apply n_abs_step_beta with y. assumption.
  - intro Hneq. inversion Hbeta; subst.
    + inversion H; subst. apply aeq_n_abs in H0. destruct H0 as [z Habs]. destruct Habs as [t3 Habs]. rewrite Habs in H1. inversion H1.
    + contradiction.
Qed. 

Lemma refltrans_aeq_beta_beta: forall t1 t2 t3, t1 =a t2 -> t2 -->>B t3 -> t1 -->>B t3.
Proof.
  intros t1 t2 t3 Haeq Hrefl. apply refltrans_composition with t2.
  - apply refl. assumption.
  - assumption.
Qed.

Lemma refltrans_beta_aeq_beta: forall t1 t2 t3, t1 -->>B t2 -> t2 =a t3 -> t1 -->>B t3.
Proof.
  intros t1 t2 t3 Hrefl Haeq. apply refltrans_composition with t2.
  - assumption.
  - apply refl. assumption.
Qed.

Corollary refltrans_n_abs_step_beta: forall t1 t2 x y, n_abs x t1 -->>B n_abs y t2 -> t1 -->>B (swap x y t2).
Proof.
  intros t1 t2 x y H. remember (n_abs x t1) as t. remember (n_abs y t2) as t'. apply eq_aeq in Heqt. apply eq_aeq in Heqt'. generalize dependent y. generalize dependent x. generalize dependent t2. generalize dependent t1. induction H.
  - intros t3 t4 x H1 y H2. apply refl.
    assert (Haeq: n_abs x t3 =a n_abs y t4).
    {
      apply aeq_trans with t1.
      - apply aeq_sym; assumption.
      - rewrite H2 in H. assumption.
    }
    inversion Haeq; subst.
    + rewrite swap_id. assumption.
    + rewrite (swap_symmetric _ x y). assumption.
  - intros t4 t5 x Haeq1 y Haeq2. apply aeq_sym in Haeq1. assert (Haeq1' := Haeq1).
    apply aeq_n_abs in Haeq1. destruct Haeq1 as [z Haeq1]. destruct Haeq1 as [t6 Haeq1]. subst. assert (Hbeta := H).
    assert (Hrefl: t2 -->>B n_abs y t5).
    {
     apply refltrans_beta_aeq_beta with t3; assumption. 
    }
    apply refltrans_composition with (swap x z t6).
    + apply refl. inversion Haeq1'; subst.
      * rewrite swap_id. assumption.
      * rewrite (swap_symmetric _ x z). assumption.
    + apply beta_n_abs in H. destruct H as [t7 H]. inversion Haeq1'; subst.
      * rewrite swap_id. apply refltrans_composition with t7. apply rtrans with t7.
        ** apply n_abs_step_beta in Hbeta. assumption.
        ** apply refl. apply aeq_refl.
        ** apply IHrefltrans.
           *** apply aeq_refl.
           *** assumption.
      * apply rtrans with (swap x z t7).
        ** apply n_abs_step_beta in Hbeta. apply ctx_beta_swap. assumption.
        ** apply IHrefltrans.
           *** apply aeq_sym. rewrite (swap_symmetric _ x z). apply aeq_abs. apply n_abs_step_beta in Hbeta. apply fv_nom_beta with t6; assumption.
           *** assumption.              
  - intros t4 t5 x H1 y H2.
    assert (Haeq: n_abs x t4 =a t2).
    {
      apply aeq_trans with t1.
      - apply aeq_sym; assumption.
      - assumption.
    }
    assert (Haeq' := Haeq). apply aeq_n_abs in Haeq. destruct Haeq as [z Haeq]. destruct Haeq as [t6 Haeq]. subst. inversion Haeq'; subst.
    + apply refltrans_composition with t6.
      * apply refl. assumption.
      * apply IHrefltrans.
      ** apply aeq_refl.
      ** assumption.
    + apply refltrans_composition with (swap z x t6).
      * apply refl. assumption.
      * apply IHrefltrans.
        ** apply aeq_abs_diff.
           *** apply aux_not_equal. assumption.
           *** apply fv_nom_remove_swap_inc.
               **** apply aux_not_equal. assumption.
               **** assumption.
           *** rewrite (swap_symmetric _ x z). rewrite swap_involutive. apply aeq_refl.
        ** assumption.
Qed.
(* end hide *)

(**

The next lemma shows that the $\beta$-rule does not introduce explicit substitutions, and several other properties can be found in the source code of the formalization.

*)
Lemma pure_beta_trans: forall t1 t2, pure t1 -> t1 -->B t2 -> pure t2.
Proof.
  intros. induction H0.
  - inversion H0; subst. inversion H2; subst. assert (Hpure: pure(n_app(n_abs x t0) t3)).
      + apply aeq_pure with t1; assumption.
      + apply aeq_pure with ({x := t3} t0).
        * assumption.
        * apply pure_m_subst.
          ** inversion Hpure. inversion H6. assumption.
          ** inversion Hpure. assumption.  
  - inversion H. apply pure_abs. apply IHctx. assumption.
  - inversion H. apply pure_app.
    + apply IHctx. assumption.
    + assumption.
  - inversion H. apply pure_app.
    + assumption.
    + apply IHctx. assumption.
  - inversion H.
  - inversion H.
Qed.
(* begin hide *)
Lemma refltrans_m_subst2_ctx_beta: forall t1 t2 t3 x, pure t1 -> t1 -->B t2 -> ({x := t3} t1) -->>B ({x := t3} t2).
Proof.
  intros t1 t2 t3 x Hpure Hbeta. induction Hbeta using n_sexp_induction_ctx.
  - inversion H; subst. induction H1. apply refltrans_composition with ({x := t3} (n_app (n_abs x0 t0) t4)).
    + apply refl. apply aeq_m_subst_out. assumption.
    + apply refltrans_composition with ({x := t3} ({x0 := t4} t0)).
      * rewrite m_subst_app. destruct (x == x0).
        ** subst. rewrite m_subst_abs_eq. apply rtrans with ({x0 := t3} ({x0 := t4} t0)).
           *** apply step_redex. apply beta_aeq_step with (n_app (n_abs x0 t0) ({x0 := t3} t4)) ({x0 := {x0 := t3} t4} t0).
               **** apply aeq_refl.
               **** apply step_beta.
               **** apply aeq_sym. apply aeq_double_m_subst.
           *** apply refltrans_refl.
        ** apply refltrans_composition with (let (z,_) := (atom_fresh (Metatheory.union (singleton x) (Metatheory.union (singleton x0) 
                                                                                                         (Metatheory.union (fv_nom t3) (Metatheory.union (fv_nom t0) (fv_nom t4)))))) in 
                                             n_app (n_abs z ({x := t3} swap x0 z t0)) ({x := t3} t4)).
           *** default_simp. apply refltrans_n_app_left. apply refl. apply m_subst_abs_neq.
               **** assumption.
               **** repeat apply notin_union_3; auto. default_simp.
           *** destruct (atom_fresh (Metatheory.union (singleton x) (Metatheory.union (singleton x0) 
                                                                       (Metatheory.union (fv_nom t3) (Metatheory.union (fv_nom t0) (fv_nom t4)))))). apply rtrans with ({x := t3} ({x0 := t4} t0)).
               **** apply step_redex. apply beta_aeq_step with (n_app (n_abs x1 ({x := t3} swap x0 x1 t0)) ({x := t3} t4))
                                                               ({x1 := {x := t3} t4} ({x := t3} swap x0 x1 t0)).
                    ***** apply aeq_refl.
                    ***** apply step_beta.
                    ***** pose proof m_subst_lemma as Hsubst. specialize (Hsubst (swap x0 x1 t0) t4 t3 x1 x). apply aeq_trans with ({x := t3} ({x1 := t4} swap x0 x1 t0)).
                    ****** apply aeq_sym. apply m_subst_lemma; auto.
                    ****** apply aeq_m_subst_out. apply aeq_m_subst_neq; auto. apply aeq_refl. rewrite swap_symmetric. apply aeq_refl.
               **** apply refltrans_refl.
      * apply refl. apply aeq_m_subst_out. assumption.
  - case (x0 == x).
    + intro Heq. subst. repeat rewrite m_subst_abs_eq. apply rtrans with (n_abs x t2).
      ** apply step_n_abs. assumption.
      ** apply refl. apply aeq_refl.
    + intro Hneq. apply refltrans_composition with (let (z,_) := (atom_fresh (Metatheory.union (singleton x) (Metatheory.union (singleton x0) 
                                                                                                                (Metatheory.union (fv_nom t1) (Metatheory.union (fv_nom t2) (fv_nom t3)))))) in 
                                                    (n_abs z ({x := t3} swap x0 z t1))).
      * default_simp. apply refl. apply m_subst_abs_neq.
        ** apply aux_not_equal. assumption.
        ** apply notin_union.
           *** repeat apply notin_union_2 in n. assumption.
           *** apply notin_union.
               **** simpl. apply notin_remove_2. apply notin_union_2 in n. apply notin_union_2 in n. apply notin_union_1 in n. assumption.
               **** apply notin_union_1 in n. assumption.
      * default_simp. apply refltrans_composition with (n_abs x1 ({x := t3} swap x0 x1 t2)).
        ** apply refltrans_n_abs. apply H. 
           *** rewrite swap_size_eq. reflexivity.
           *** rewrite swap_size_eq. reflexivity.
           *** apply ctx_beta_swap. assumption.
           *** apply pure_swap. assumption.
        ** apply refl. apply aeq_sym. apply m_subst_abs_neq.
           **** apply aux_not_equal. assumption.
           **** apply notin_union.
                ***** repeat apply notin_union_2 in n. assumption.
                ***** apply notin_union.
                ****** apply notin_union_2 in n. apply notin_union_2 in n. apply notin_union_2 in n. apply notin_union_1 in n. simpl. apply notin_remove_2. assumption.
                ****** apply notin_union_1 in n. assumption.
  - repeat rewrite m_subst_app. apply refltrans_n_app_left. apply IHHbeta. inversion Hpure. assumption.
  - repeat rewrite m_subst_app. apply refltrans_n_app_right. apply IHHbeta. inversion Hpure. assumption.
  - inversion Hpure.
  - inversion Hpure.
Qed.

Corollary refltrans_m_subst2_beta: forall t1 t2 t3 x,  pure t1 -> t1 -->>B t2 -> ({x := t3}t1) -->>B ({x := t3}t2).
Proof.
  intros t1 t2 t3 x Hpure Hbeta. induction Hbeta.
    - apply refl. apply aeq_m_subst_out. assumption.
    - apply refltrans_composition with ({x := t3} t2).
      + apply refltrans_m_subst2_ctx_beta; assumption.
      + apply IHHbeta. apply pure_beta_trans with t1; assumption. 
    - apply refltrans_composition with ({x := t3} t2).
      + apply refl. apply aeq_m_subst_out. assumption.
      + apply IHHbeta. apply aeq_pure in H; assumption.
Qed.

Corollary refltrans_m_subst_beta: forall t1 t2 t3 t4 x, pure t3 -> t1 -->>B t2 -> t3 -->>B t4 -> ({x := t1} t3) -->>B ({x := t2} t4).
Proof.
  intros t1 t2 t3 t4 x Hpure Hbeta1 Hbeta2. apply refltrans_composition with ({x := t2} t3).
    - apply refltrans_m_subst1. assumption.
    - apply refltrans_m_subst2_beta; assumption.
Qed.

Lemma refltrans_Bx_P_beta: forall t1 t2, t1 -->Bx t2 -> (P t1) -->>B (P t2).
Proof.
  intros t1 t2 H. induction H.
  - inversion H; subst. inversion H1; subst. apply refltrans_composition with (P(n_app (n_abs x t0) t3)).
    + apply refl. apply aeq_P. assumption.
    + apply rtrans with (P([x := t3] t0)).
      * simpl. apply step_redex. apply beta_aeq_step with (n_app (n_abs x (P t0)) (P t3)) ({x := P t3} P t0).
        ** apply aeq_refl.
        ** apply step_beta.
        ** apply aeq_refl.
      * apply refl. apply aeq_P. assumption.
  - simpl. apply refltrans_n_abs. assumption.
  - simpl. apply refltrans_n_app_left. assumption.
  - simpl. apply refltrans_n_app_right. assumption.
  - simpl. apply refltrans_m_subst2_beta.
    + apply pure_P. 
    + assumption.
  - simpl. apply refltrans_m_subst1. assumption.
Qed.    
(* end hide *)

(**

As expected, one step $\beta$-reduction can be simulated by the reflexive-transitive closure of the [-->lx] rule.

*)

Lemma refltrans_pure_beta: forall t1 t2, pure t1 -> t1 -->B t2 -> t1 -->>lx t2.
Proof.
  intros t1 t2 Hpure1 H. induction H.
    - inversion H; subst. inversion H1; subst. apply refltrans_composition with (n_app (n_abs x t0) t3).
      + apply refl. assumption.
      + apply refltrans_composition with ({x := t3} t0).
        * apply rtrans with ([x := t3] t0).
          ** apply b_rule. apply step_redex. apply betax_aeq_step with (n_app (n_abs x t0) t3) ([x := t3] t0); try apply aeq_refl. apply step_betax.
          ** apply refltrans_lx_pix. apply pure_pix. assert (Hpure3: pure (n_app (n_abs x t0) t3)).
            *** apply aeq_pure with t1; assumption.
            *** inversion Hpure3.  inversion H5. assumption. 
        * apply refl. assumption.
    - apply refltrans_n_abs_lx. inversion Hpure1. apply IHctx; assumption.
    - apply refltrans_n_app_left_lx. inversion Hpure1. apply IHctx; assumption.
    - apply refltrans_n_app_right_lx. inversion Hpure1. apply IHctx; assumption.
    - inversion Hpure1.
    - inversion Hpure1.
Qed.

Corollary refltrans_pure_beta_refltrans: forall t1 t2, pure t1 -> t1 -->>B t2 -> t1 -->>lx t2.
Proof.
  intros t1 t2 H H1. induction H1.
    - apply refl. assumption.
    - apply refltrans_composition with t2.
      + apply refltrans_pure_beta; try assumption.
      + apply IHrefltrans. pose proof pure_beta_trans. apply (pure_beta_trans _ t2) in H; assumption.
    - apply refltrans_composition with t2.
      + apply refl. assumption.
      + apply IHrefltrans. apply aeq_pure with t1; assumption.
Qed.

(* begin hide *)
Lemma fv_nom_B_n_app: forall t1 t2 x, x `notin` fv_nom (B t1) -> x `notin` fv_nom (B t2) -> x `notin` fv_nom (B (n_app t1 t2)).
Proof.
  induction t1 as [ y | y t1 IHt1 | t1 IHt1 t2 IHt2 | t1 IHt1 z t2  IHt2].
  - intros t2 x Hnotin Hnotin'. simpl in *. apply notin_union.
    + assumption.
    + assumption.
  - intros t2 x Hnotin Hnotin'. simpl in Hnotin. simpl B. apply notin_remove_1 in Hnotin. destruct Hnotin as [Heq | Hnotin].
    + subst. apply fv_nom_remove_eq. assumption.
    + apply fv_nom_remove.
        * assumption.
        * apply notin_remove_2. assumption.
  - intros t' x Hnotin Hnotin'. change (B (n_app (n_app t1 t2) t')) with (n_app (B (n_app t1 t2)) (B t')). change (fv_nom (n_app (B (n_app t1 t2)) (B t'))) with (fv_nom (B (n_app t1 t2)) `union` fv_nom (B t')). apply notin_union; assumption.
  - intros t' x Hnotin Hnotin'. simpl. apply notin_union.
    + apply notin_union.
      * simpl in Hnotin. apply notin_union_1 in Hnotin. assumption.
      * simpl in Hnotin. apply notin_union_2 in Hnotin. assumption.
    + assumption.
Qed.
(* end hide *)

(**

Since we are working modulo $\alpha$-equivalence, a straightforward instantiation of $A$ with [n_sexp] is insuficient. This is because the reflexive closure of [-->x] must encompass not only syntactic equality but also $\alpha$-equivalence. In fact, the proof that [-->lx] has the Z property (diagram (%\ref{lx:zprop}%)) is proved by the following two diagrams, since [-->lx] = [-->x] $\cup$ [-->Bx]:

%\begin{equation}\label{lx:zprop-proof}
 \xymatrix{ t_1 \ar[r]_{x} & t_2 \ar@{.>>}[dl]^{x} & & & t_1 \ar[r]_{Bx} & t_2 \ar@{.>>}[dl]^{lx}\\
P\ t_1 \ar@{.>>}[r]_{x} \ar@{.>>}[d]_{lx} & P\ t_2 & & & B(P\ t_1) \ar@{.>>}[r]_{lx} & B(P\ t_2) \\
 B(P\ t_1) \ar@{.>>}[r]_{lx} & B(P\ t_2) & & & & \\}
\end{equation}%

Note that the complete permutation $P$ replaces every explicit substitution in the input term $t$ with the corresponding metasubstitution in the output $P\ t$. Furthermore, the following lemma (denoted [pi_P]) demonstrates that applying the complete permutation to a term before and after an [-->x] step results in the same term, up to the renaming of bound variables: 

*)

Lemma pi_P: forall t1 t2, t1 -->x t2 -> (P t1) =a (P t2).
  (**
%\noindent {\bf Proof.}% The proof is by induction on the reduction $t_1 \to_x t_2$. The non trivial case is when $t_1 \to_{abs3} t_2$. In this case, $t_1 =_{\alpha} \esub{(\lambda_x.t_1')}{y}{t_2'} \to_{abs3} \lambda_z.\esub{(\swap{x}{z}{t_1'})}{y}{t_2'} =_{\alpha} t_2$, where $x \neq y$ and $z$ is a fresh variable. In this case, the proof is as follows:
%\begin{mathpar}
 \inferrule*[Right={($\alpha$-{\sf trans})}]{\inferrule*[Left={({\tt aeq\_P})}]{t_1 =_{\alpha} \esub{(\lambda_x.t_1')}{y}{t_2'}}{P\ t_1 =_{\alpha} P\ (\esub{(\lambda_x.t_1')}{y}{t_2'})} \and  \inferrule*[Right={($\alpha$-{\sf trans})}]{(\star) \and \inferrule*[Right={({\tt aeq\_P})}]{\lambda_z.\esub{(\swap{x}{z}{t_1'})}{y}{t_2'} =_{\alpha} t_2}{P\ (\lambda_z.\esub{(\swap{x}{z}{t_1'})}{y}{t_2'}) =_{\alpha} P\ t_2} }{P\ (\esub{(\lambda_x.t_1')}{y}{t_2'}) =_{\alpha} P\ t_2}}{P\ t_1 =_{\alpha} P\ t_2}
\end{mathpar}%
%\noindent% where $(\star)$ is given by
%\begin{mathpar}
 \inferrule*[Right={({\sf def-P})}]{\inferrule*[Right={({\sf aeq\_swap\_P})}]{\inferrule*[Right={({\sf m\_subst\_abs\_neq})}]{~}{\metasub{\lambda_x.(P\ t_1')}{y}{P\ t_2'} =_{\alpha}  \lambda_z.\metasub{(\swap{x}{z}{P\ t_1'})}{y}{P\ t_2'}}}{\metasub{\lambda_x.(P\ t_1')}{y}{P\ t_2'} =_{\alpha}  \lambda_z.\metasub{P\ (\swap{x}{z}{t_1'})}{y}{P\ t_2'}}} {P\ (\esub{(\lambda_x.t_1')}{y}{t_2'}) =_{\alpha} P\ (\lambda_z.\esub{(\swap{x}{z}{t_1'})}{y}{t_2'})}
\end{mathpar}%
 %\hfill%$\Box$
*)
Proof.
  intros t1 t2 H. induction H.
  - induction H. inversion H0; subst.
    + apply aeq_P in H. simpl in H. rewrite m_subst_var_eq in H. apply aeq_P in H1. apply aeq_trans with (P u'); assumption.
    + apply aeq_P in H. simpl in H. rewrite m_subst_var_neq in H.
      * apply aeq_P in H1. apply aeq_trans with (n_var x); assumption.
      * assumption.
    + apply aeq_P in H. apply aeq_P in H1. simpl in *. rewrite m_subst_abs_eq in H. apply aeq_trans with (n_abs y (P t1)); assumption.
    + apply aeq_P in H. apply aeq_P in H1. simpl in *. apply aeq_trans with ({y := P t2} n_abs x (P t1)).
        ** assumption.
        ** apply aeq_trans with (n_abs x ({y := P t2} P t1)).
           *** apply m_subst_n_abs_neq_notin.
               **** assumption.
               **** apply notin_P. assumption.
           *** assumption.
    + apply aeq_P in H. apply aeq_P in H1. simpl in *. apply aeq_trans with ({y := P t2} n_abs x (P t1)).
        ** assumption.
        ** apply aeq_trans with (n_abs z ({y := P t2} P (swap x z t1))).
           *** apply aeq_trans with (n_abs z ({y := P t2} (swap x z (P t1)))).
               **** apply m_subst_abs_neq.
                    ***** apply aux_not_equal; assumption.
                    ***** apply notin_union.
                    ****** apply notin_P; assumption.
                    ****** apply notin_union.
                    ******* simpl. apply notin_remove_2. apply notin_P; assumption.
                    ******* apply notin_singleton. apply aux_not_equal; assumption.
               **** apply aeq_abs_same. apply aeq_m_subst_out. apply aeq_sym. apply aeq_swap_P. 
           *** assumption.
    + apply aeq_P in H. apply aeq_P in H1. simpl in *. rewrite m_subst_app in H. apply aeq_trans with (n_app ({y := P t3} P t1) ({y := P t3} P t2)); assumption.
  - simpl. apply aeq_abs_same. assumption.
  - simpl. apply aeq_app.
    + assumption.
    + apply aeq_refl.
  - simpl. apply aeq_app.
    + apply aeq_refl.
    + assumption.
  - simpl. apply aeq_m_subst_eq.
    + assumption.
    + apply aeq_refl.
  - simpl. apply aeq_m_subst_eq.
    + apply aeq_refl.
    + assumption.
Qed.

(**

This simplifies the left diagram in (%\ref{lx:zprop-proof}%) as follows:

%\begin{equation}\label{lx:zprop-proof2}
 \xymatrix{ t_1 \ar[r]_{x} & t_2 \ar@{.>>}[dl]^{x}\\
P\ t_1 =_\alpha P\ t_2 \ar@{.>>}[d]_{lx} & \\
 B(P\ t_1) \ar@{.>>}[r]_{lx} & B(P\ t_2)\\}
\end{equation}%

*)

(* begin hide *)
Lemma pure_P_id: forall t, pure t -> P t = t.
Proof.
  induction t.
  - intros. simpl. reflexivity.
  - intros. simpl. inversion H. apply IHt in H1. rewrite H1. reflexivity.
  - intros. simpl. inversion H. apply IHt1 in H2; apply IHt2 in H3. rewrite H2; rewrite H3. reflexivity.
  - intros. inversion H.
Qed.
           
Lemma notin_B: forall t x, x `notin` (fv_nom t) -> x `notin` (fv_nom (B t)).
Proof.
  induction t as [ z | z t1 IHt1 | t1 IHt1 t2 IHt2 | t1 IHt1 z t2  IHt2].
  - intros x Hnotin. simpl in *. assumption.
  - intros x Hnotin. simpl in *. apply notin_remove_1 in Hnotin. destruct Hnotin as [Heq | Hnotin].
    + apply notin_remove_3. assumption.
    + apply notin_remove_2. apply IHt1. assumption.
  - intros x Hnotin. simpl in Hnotin. apply fv_nom_B_n_app.
    + apply IHt1. apply notin_union_1 in Hnotin. assumption.
    + apply IHt2. apply notin_union_2 in Hnotin. assumption.
  - intros x Hnotin. simpl in *. apply notin_union.
    + apply notin_union_1 in Hnotin. apply notin_remove_1 in Hnotin. destruct Hnotin as [Heq | Hnotin].
      * apply notin_remove_3. assumption.
      * apply notin_remove_2. apply IHt1. assumption.
    + apply IHt2. apply notin_union_2 in Hnotin. assumption.
Qed.    

Lemma aeq_swap_B: forall t x y, (swap x y (B t)) =a (B (swap x y t)).
Proof.
  induction t as [ z | z t1 IHt1 | t1 IHt1 t2 IHt2 | t1 IHt1 z t2  IHt2].
  - intros x y. simpl. apply aeq_refl.
  - intros x y. simpl. apply aeq_abs_same. apply IHt1.
  - intros x y. generalize dependent t1. intro t1. case t1.
    + intros x' IH. simpl in *. apply aeq_app. 
       * apply aeq_refl. 
       * apply IHt2. 
    + intros x' t IH. simpl B. apply aeq_trans with ({vswap x y x' := (swap x y (B t2))} (swap x y (B t))).
      * apply aeq_swap_m_subst.
      * apply aeq_m_subst_eq.
        ** simpl in IH. specialize (IH x y). inversion IH; subst.
           *** assumption.
           *** contradiction.
        ** apply IHt2.
    + intros t' t'' IH. change (swap x y (B (n_app (n_app t' t'') t2))) with (n_app (swap x y ((B(n_app t' t'')))) (swap x y ((B t2)))). change (B (swap x y (n_app (n_app t' t'') t2))) with (n_app (B (n_app (swap x y t') (swap x y t''))) (B (swap x y t2))). apply aeq_app.
      * apply IH.
      * apply IHt2.
    + intros t' x' t'' IH. change (swap x y (B (n_app ([x' := t''] t') t2))) with (n_app (swap x y (B ([x' := t''] t'))) (swap x y (B t2))). change (B (swap x y (n_app ([x' := t''] t') t2))) with (n_app (B (swap x y (([x' := t''] t')))) (B (swap x y (t2)))). apply aeq_app.
      * apply IH.
      * apply IHt2.
  - intros x y. simpl. apply aeq_sub_same.
    + apply IHt1.
    + apply IHt2.
Qed.
(* end hide *)

(**

Which in turn simplifies to

%\begin{equation}\label{lx:zprop-proof3}
 \xymatrix{ t_1 \ar[r]_{x} & t_2 \ar@{.>>}[dl]^{x}\\
P\ t_1 =_\alpha P\ t_2 \ar@{.>>}[d]_{lx} & \\
 B(P\ t_1) =_\alpha B(P\ t_2) & \\}
\end{equation}%

%\noindent% due to the lemma [aeq_B]:

 *)

Lemma aeq_B: forall t1 t2, t1 =a t2 -> (B t1) =a (B t2).
(**

%\noindent {\bf Proof}.% In this case, the proof is done by induction on the size of the term $t_1$. We developed a customized induction principle for this kind of proof:

<<
Lemma n_sexp_induction: forall P : n_sexp -> Prop,            (forall x, P (n_var x)) ->
              (forall t1 z, (forall t2, size t2 = size t1 -> P t2) -> P (n_abs z t1)) ->
                                      (forall t1 t2, P t1 -> P t2 -> P (n_app t1 t2)) ->
(forall t1 t3 z, P t3 -> (forall t2, size t2 = size t1 -> P t2) -> P (n_sub t1 z t3)) ->
                                                                         (forall t, P t).
>>

The non trivial case is when $t_1 = (\lambda_x.t_{11})\ t_{12}$ and $t_2 = (\lambda_y.t_{21})\ t_{22}$, for some terms $t_{11}, t_{12}, t_{21}$ and $t_{22}$ and variables $x$ and $y$. We need to prove that $B ((\lambda_x.t_{11})\ t_{12}) =_{\alpha} B ( (\lambda_y.t_{21})\ t_{22})$. If $x = y$ then we are done by the induction hypothesis, and if $x \neq y$ then 

%\begin{mathpar}
 \inferrule*[Right={({\sf def-B})}]{\inferrule*[Right={({\sf aeq\_m\_subst\_neq})}]{\inferrule*[Left={({\sf i.h.})}]{~}{B\ t_{12} =_{\alpha} B\ t_{22}} \and \inferrule*[Right={({\sf i.h.})}]{~}{B\ t_{11} =_{\alpha} \swap{x}{y}{(B\ t_{21})}}}{\metasub{(B\ t_{11})}{x}{B\ t_{12}} =_{\alpha} \metasub{(B\ t_{21})}{y}{B\ t_{22}}}}{B ((\lambda_x.t_{11})\ t_{12}) =_{\alpha} B ( (\lambda_y.t_{21})\ t_{22})}
\end{mathpar}%

Note that the induction hypothesis can be applied to the right branch, as the swap does not affect the size of terms, %\emph{i.e.}% $|\swap{x}{y}{(B\ t_{21})}| = |B\ t_{21}|$. %\hfill%$\Box$
*)
Proof.
  induction t1 using n_sexp_induction.
  - intros t2 H. inversion H. simpl. apply aeq_refl.
  - intros t2 H0. inversion H0.
    + subst. simpl. apply aeq_abs_same. apply H.
       * reflexivity.
       * assumption.
    + subst. simpl. apply aeq_abs_diff.
       * assumption.
       * apply notin_B. assumption.
       * apply (aeq_trans _ (B (swap y z t3))).
           ** apply H.
                *** reflexivity.
                *** assumption.
           ** apply aeq_sym. apply aeq_swap_B.
  - intros t2 H. destruct t1_1; subst. 
    + simpl. inversion H; subst. apply aeq_sym in H2. apply aeq_nvar_1 in H2. subst. simpl. apply aeq_app.
       * apply aeq_refl.
       *  apply IHt1_2. assumption.
    + inversion H; subst. apply aeq_n_abs in H2. destruct H2 as [y Habs]. destruct Habs as [t2_1 Habs]. rewrite Habs. simpl in *. case (x == y).
       * intro Heq. subst. apply aeq_m_subst_eq.
         ** inversion H; subst. apply IHt1_1 in H3. simpl in H3. inversion H3; subst.
            *** assumption.
            *** contradiction.
         ** apply IHt1_2. assumption.
       * intro Hneq. subst. inversion H; subst. inversion H3; subst. 
         **  contradiction.
         ** apply aeq_m_subst_neq.
            *** apply IHt1_2. assumption.
            *** assumption.
            *** apply notin_B. assumption.
            *** apply IHt1_1 in H3. simpl in H3. inversion H3; subst.
                **** contradiction.
                **** rewrite (swap_symmetric _ x y). assumption.
    + inversion H; subst. change (B (n_app (n_app t1_1_1 t1_1_2) t1_2)) with (n_app (B (n_app t1_1_1 t1_1_2)) (B t1_2)). apply aeq_n_app in H2. destruct H2 as [t11' Happ]. destruct Happ as [t12' Happ]. subst. change (B (n_app (n_app t11' t12') t2')) with (n_app (B (n_app t11' t12')) (B t2')). apply aeq_app.
      * apply IHt1_1. inversion H; subst. assumption.
      * apply IHt1_2. assumption.
    + inversion H;subst. inversion H2; subst.
       * simpl. apply aeq_app.
           ** simpl in IHt1_1. apply IHt1_1 in H2. simpl in H2. assumption.
           ** apply IHt1_2. assumption.
       * simpl. apply aeq_app.
           ** apply IHt1_1 in H2. simpl in H2. assumption.
           ** apply IHt1_2. assumption.
  - intros t2 H'. inversion H'; subst.
    + simpl. apply aeq_sub_same.
       * apply H.
         ** reflexivity.
         ** assumption.
       * apply IHt1_1. assumption.
    + simpl. apply aeq_sub_diff.
       * apply IHt1_1. assumption.
       * assumption.
       * apply notin_B. assumption.
       * rewrite <- (swap_id t1_1 z) in H7. apply H in H7.
           ** rewrite swap_id in H7. apply (aeq_trans _ (B (swap y z t1'))).
                *** assumption.
                *** apply aeq_sym. apply aeq_swap_B.
           ** rewrite swap_id. reflexivity.
Qed.

(**

One challenging task in this formalization was the proof of the next lemma stating that the metasubstitution of complete development of its components reduces (via $\beta$-reduction) to the complete development of the metasubstitution.

*)
Lemma refltrans_m_subst_B_beta: forall t1 t2 x, pure t1 -> pure t2 -> ({x := B t2} B t1) -->>B (B ({x := t2} t1)).
Proof.
  (**
%\noindent {\bf Proof}.% The proof is by induction on the size of the term $t_1$. This proof also uses a customized induction principle given by
<<
n_sexp_size_induction : forall P: n_sexp -> Prop,
                                 (forall x : atom, P (n_var x)) ->
(forall (t1: n_sexp) (z: atom), (forall t1': n_sexp, size t1' <
                 size (n_abs z t1) -> P t1') -> P (n_abs z t1)) ->
(forall t1 t2: n_sexp, (forall t1': n_sexp, size t1' <
               size (n_app t1 t2) -> P t1') -> P (n_app t1 t2)) ->
(forall (t1 t2: n_sexp) (z: atom), (forall t1': n_sexp, size t1' <
             size ([z := t2] t1) -> P t1') -> P ([z := t2] t1)) ->
                                            forall t : n_sexp, P t
>>

The interesting case is the application case. If $t_1 = t_{11}\ t_{12}$ then we need to prove that %\begin{center}$\metasub{(B (t_{11}\ t_{12}))}{x}{B\ t_2} \tto_{\beta} B (\metasub{(t_{11}\ t_{12})}{x}{t_2})$\end{center}% We proceed by case analysis on the structure of $t_{11}$. If $t_{11}$ is the variable $x$ then our goal is %\begin{center}$(B\ t_2)\ (\metasub{(B t_{12})}{x}{B\ t_2} \tto_{\beta} B\ (t_2\ (\metasub{t_{12}}{x}{t_2}))$\end{center}% and in turn, we proceed by case analysis on the structure of $t_2$. The non-trivial case, again is when $t_2 = \lambda_y.t_2'$:
%\begin{mathpar}
\inferrule*[Right={(\sf def-B)}] {\inferrule*[Right={(\sf compat)}] {\inferrule*[Right={(\sf i.h.)}]{~} {\metasub{(B t_{12})}{x}{B\ (\lambda_y.t_2')} \tto_{\beta} B( \metasub{t_{12}}{x}{\lambda_y.t_2'})}} {\inferrule*[Right={($\beta$)}]{\metasub{(B\ t_2')}{y}{(\metasub{(B t_{12})}{x}{B\ (\lambda_y.t_2')})} \tto_{\beta}  \metasub{(B\ t_2')}{y}{(B(\metasub{t_{12}}{x}{(\lambda_y.t_2')}))}} {(\lambda_y.B\ t_2')\ (\metasub{(B t_{12})}{x}{B\ (\lambda_y.t_2')}) \tto_{\beta}  \metasub{(B\ t_2')}{y}{(B(\metasub{t_{12}}{x}{(\lambda_y.t_2')}))}}}} {(B\ (\lambda_y.t_2'))\ (\metasub{(B t_{12})}{x}{B\ (\lambda_y.t_2')} \tto_{\beta} B\ ((\lambda_y.t_2')\ (\metasub{t_{12}}{x}{(\lambda_y.t_2')})))}
\end{mathpar}%
%\noindent% where the %{\sf (compat)}% rule is applied in a general sense, as it serves as a structural compatibility rule in various proofs. Note that all compatibility rules can be found in the source files of the formalization.

Another non-trivial case occurs when $t_{11} = \lambda_y.t_{11}'$, leading to the goal  %\begin{center}$\metasub{(B ((\lambda_y.t_{11}')\ t_{12}))}{x}{B\ t_2} \tto_{\beta} B (\metasub{((\lambda_y.t_{11}')\ t_{12})}{x}{t_2})$\end{center}%

%\noindent% whose derivation is given by

%\begin{mathpar}
\inferrule*[Right={(\sf def-B)}]{\metasub{(\metasub{(B\ t_{11}')}{y}{B\ t_{12}})}{x}{B\ t_2} \tto_{\beta} B (\metasub{((\lambda_y.t_{11}')\ t_{12})}{x}{t_2})}{\metasub{(B ((\lambda_y.t_{11}')\ t_{12}))}{x}{B\ t_2} \tto_{\beta} B (\metasub{((\lambda_y.t_{11}')\ t_{12})}{x}{t_2})}
\end{mathpar}%

Then we have two cases, either $x = y$ or $x \neq y$:

%\begin{mathpar}
\inferrule*[Right={(\sf def-B)}]{\inferrule*[Right={($x = y$)}]{ \inferrule*[Right={(\sf def-B)}] { \inferrule*[Right={(\sf compat)}] { \inferrule*[Right={(\sf i.h.)}]{~}{\metasub{(B\ t_{12})}{x}{B\ t_2} \tto_{\beta} B \metasub{t_{12}}{x}{t_2}}} {\metasub{(B\ t_{11}')}{y}{(\metasub{(B\ t_{12})}{x}{B\ t_2})} \tto_{\beta} \metasub{(B\ t_{11}')}{y}{B (\metasub{t_{12}}{x}{t_2})}}} {\metasub{(B\ t_{11}')}{y}{(\metasub{(B\ t_{12})}{x}{B\ t_2})} \tto_{\beta} B ((\lambda_y.t_{11}')\ \metasub{t_{12}}{x}{t_2})}} {\metasub{(\metasub{(B\ t_{11}')}{y}{B\ t_{12}})}{x}{B\ t_2} \tto_{\beta} B (\metasub{((\lambda_y.t_{11}')\ t_{12})}{x}{t_2})}} {\metasub{(B ((\lambda_y.t_{11}')\ t_{12}))}{x}{B\ t_2} \tto_{\beta} B (\metasub{((\lambda_y.t_{11}')\ t_{12})}{x}{t_2})}
\end{mathpar}%

%\begin{mathpar}
\inferrule*[Right={(\sf def-B)}]{  \inferrule*[Right={($x \neq y$)}]{\inferrule*[Right={(\sf def-B)}]{ \inferrule{(\star)} {\metasub{(\metasub{(B\ t_{11}')}{y}{B\ t_{12}})}{x}{B\ t_2} \tto_{\beta} \metasub{(B(\metasub{\swap{z}{y}{t_{11}'}}{x}{t_2}))}{z}{B(\metasub{t_{12}}{x}{t_2})}}}{\metasub{(\metasub{(B\ t_{11}')}{y}{B\ t_{12}})}{x}{B\ t_2} \tto_{\beta} B ((\lambda_z.(\metasub{\swap{z}{y}{t_{11}'}}{x}{t_2}))\ (\metasub{t_{12}}{x}{t_2}))}} {\metasub{(\metasub{(B\ t_{11}')}{y}{B\ t_{12}})}{x}{B\ t_2} \tto_{\beta} B (\metasub{((\lambda_y.t_{11}')\ t_{12})}{x}{t_2})}} {\metasub{(B ((\lambda_y.t_{11}')\ t_{12}))}{x}{B\ t_2} \tto_{\beta} B (\metasub{((\lambda_y.t_{11}')\ t_{12})}{x}{t_2})}
\end{mathpar}%

%\noindent% where $(\star)$ is obtained by decomposing the reduction %\begin{center}$\metasub{(\metasub{(B\ t_{11}')}{y}{B\ t_{12}})}{x}{B\ t_2} \tto_{\beta} \metasub{(B(\metasub{\swap{z}{y}{t_{11}'}}{x}{t_2}))}{z}{B(\metasub{t_{12}}{x}{t_2})}$\end{center}% using $\metasub{(\metasub{(\swap{z}{y}{(B\ t_{11}')})}{x}{B\ t_2})}{z}{\metasub{(B\ t_{12})}{x}{B\ t_2}}$ as the intermediare term, and each subreduction is solved as follows

%\begin{mathpar}
\inferrule*[Right={({\sf ren})}]{ \inferrule*[Right={({\sf refl})}]{ \inferrule*[Right={({\sf SL})}]{~} {\metasub{(\metasub{(\swap{z}{y}{B\ t_{11}'})}{z}{B\ t_{12}})}{x}{B\ t_2} =_{\alpha} \metasub{(\metasub{(\swap{z}{y}{(B\ t_{11}')})}{x}{B\ t_2})}{z}{\metasub{(B\ t_{12})}{x}{B\ t_2}}}} {\metasub{(\metasub{(\swap{z}{y}{B\ t_{11}'})}{z}{B\ t_{12}})}{x}{B\ t_2} \tto_{\beta} \metasub{(\metasub{(\swap{z}{y}{(B\ t_{11}')})}{x}{B\ t_2})}{z}{\metasub{(B\ t_{12})}{x}{B\ t_2}}}}{\metasub{(\metasub{(B\ t_{11}')}{y}{B\ t_{12}})}{x}{B\ t_2} \tto_{\beta} \metasub{(\metasub{(\swap{z}{y}{(B\ t_{11}')})}{x}{B\ t_2})}{z}{\metasub{(B\ t_{12})}{x}{B\ t_2}}}\end{mathpar}%

%\noindent% where the rule %({\sf ren})% denotes a renaming of bound variables, the rule %({\sf SL})% denotes the Substitution Lemma ([m_subst_lemma]) above (see Section 2) and

%\begin{mathpar}
\inferrule{\inferrule*[Left={(\sf i.h.)}]{~}{\metasub{(\swap{z}{y}{(B\ t_{11}')})}{x}{B\ t_2} \tto_{\beta} B(\metasub{\swap{z}{y}{t_{11}'}}{x}{t_2})} \and \inferrule*[Right={(\sf i.h.)}]{~}{\metasub{(B\ t_{12})}{x}{B\ t_2} \tto_{\beta} B(\metasub{t_{12}}{x}{t_2})}} {\metasub{(\metasub{(\swap{z}{y}{(B\ t_{11}')})}{x}{B\ t_2})}{z}{\metasub{(B\ t_{12})}{x}{B\ t_2}} \tto_{\beta} \metasub{(B(\metasub{\swap{z}{y}{t_{11}'}}{x}{t_2}))}{z}{B(\metasub{t_{12}}{x}{t_2})}}\end{mathpar}%

*)  

  intros t1 t2 x H H0. induction t1 using n_sexp_size_induction.
  - simpl. destruct (x0 == x).
    + subst. repeat rewrite m_subst_var_eq. apply refltrans_refl.
    + repeat rewrite m_subst_var_neq; try assumption. simpl. apply refltrans_refl.
  - simpl. destruct (x == z).
    + subst. repeat rewrite m_subst_abs_eq. simpl. apply refltrans_refl.
    + apply refltrans_composition with (let (z',_) := (atom_fresh (Metatheory.union (singleton z) (Metatheory.union (singleton x) 
                                                                                                     (Metatheory.union (fv_nom t2) (fv_nom t1))))) in (n_abs z' ({x := (B t2)} (swap z z' (B t1))))).
      * destruct (atom_fresh (Metatheory.union (singleton z) (Metatheory.union (singleton x) (Metatheory.union (fv_nom t2) (fv_nom t1))))).
        apply refl. apply m_subst_abs_neq.
        ** assumption.
        ** apply notin_union.
           *** apply notin_B. apply notin_union_2 in n0. apply notin_union_2 in n0. apply notin_union_1 in n0. assumption.
           *** apply notin_union.
               **** simpl. apply notin_remove_2. repeat apply notin_union_2 in n0. apply notin_B. assumption.
               **** apply notin_union_2 in n0. apply notin_union_1 in n0. assumption.
      * destruct (atom_fresh (Metatheory.union (singleton z)
                                (Metatheory.union (singleton x) (Metatheory.union (fv_nom t2) (fv_nom t1))))). default_simp.
        apply refltrans_composition with (n_abs x0 ({x := B t2} B (swap z x0 t1))).
        ** apply refltrans_n_abs. apply refl. apply aeq_m_subst_out. apply aeq_swap_B.
        ** apply refltrans_composition with (n_abs x0 (B ({x := t2} swap z x0 t1))).
           *** apply refltrans_n_abs. apply H1.
               **** rewrite swap_size_eq. lia.
               **** apply pure_swap. assumption.
           *** pose proof m_subst_abs_neq. simpl in *. apply refltrans_composition with (B (n_abs x0 ({x := t2} swap z x0 t1))).
               **** simpl. apply refltrans_refl.
               **** apply refl. apply aeq_B. apply aeq_sym. apply H. 
                    ***** assumption.
                    ***** auto.
  - rewrite m_subst_app. induction t1_1.
    + destruct (x0 == x).
      * subst. simpl ({x := B t2} B (n_app (n_var x) t1_2)). rewrite m_subst_app. repeat rewrite m_subst_var_eq. generalize dependent t2. intro t2. destruct t2; intros H0 H1.
        ** simpl. apply refltrans_n_app_right. change ({x := n_var x0} B t1_2)  with ({x := (B (n_var x0))} B t1_2). apply H1.
           *** simpl. lia.
           *** inversion H. assumption.
        ** simpl. apply rtrans with ({x0 := ({x := n_abs x0 (B t2)} B t1_2)} (B t2)).
           *** apply step_redex. apply beta_aeq_step with (n_app (n_abs x0 (B t2)) ({x := n_abs x0 (B t2)} B t1_2))
                                                          ({x0 := {x := n_abs x0 (B t2)} B t1_2} B t2). 
               **** apply aeq_refl.
               **** apply step_beta.
               **** apply aeq_refl.
           *** change (n_abs x0 (B t2)) with (B(n_abs x0 t2)). apply refltrans_m_subst1. apply H1.
               **** simpl. lia.
               **** inversion H. assumption.
        ** change (B (n_app (n_app t2_1 t2_2) ({x := n_app t2_1 t2_2} t1_2))) with (n_app (B(n_app t2_1 t2_2)) (B({x := n_app t2_1 t2_2} t1_2))). 
           apply refltrans_n_app_right. apply H1.
           *** simpl. lia.
           *** inversion H. assumption.
        ** inversion H0.
      * rewrite m_subst_var_neq.
        ** simpl. rewrite m_subst_app. rewrite m_subst_var_neq.
           *** apply refltrans_n_app_right. apply H1.
               **** simpl. lia.
               **** inversion H. assumption.
           *** assumption.
        ** assumption.
    + simpl (B (n_app (n_abs x0 t1_1) t1_2)). destruct (x == x0).
      * subst. apply refltrans_composition with (B (n_app (n_abs x0 t1_1) ({x0 := t2} t1_2))).
        ** simpl. apply refltrans_composition with ({x0 := ({x0 := (B t2)} (B t1_2))} B t1_1).
           *** apply refltrans_composition with ({x0 := B t2} ({x0 := B t1_2} B t1_1)).
               **** apply refltrans_refl.
               **** apply refl. apply aeq_double_m_subst.
           *** apply refltrans_m_subst1. apply H1.
               **** simpl. lia.
               **** inversion H. assumption.
        ** apply refl. apply aeq_B. apply aeq_app; try apply aeq_refl. rewrite m_subst_abs. rewrite eq_dec_refl. apply aeq_refl.
      * apply refltrans_composition with (let (z, _) := atom_fresh
                                                          (Metatheory.union (fv_nom t2) (Metatheory.union (fv_nom (n_abs x0 t1_1)) (singleton x))) in
                                          (B (n_app (n_abs z ({x := t2} swap x0 z t1_1)) ({x := t2} t1_2)))).
        ** destruct (atom_fresh (Metatheory.union (fv_nom t2) (Metatheory.union (fv_nom (n_abs x0 t1_1)) (singleton x)))). simpl. 
           apply refltrans_composition with ({x1 := ({x := B t2} B t1_2)} ({x := B t2} swap x0 x1 (B t1_1))).
           *** apply refltrans_composition with ({x := B t2} ({x1 := B t1_2} swap x0 x1 (B t1_1))).
               **** apply refltrans_m_subst2_beta.
                    ***** inversion H. inversion H4. apply pure_m_subst; apply pure_B; assumption.
                    ***** apply refl. apply aeq_sym. destruct (x0 == x1).
                    ****** subst. rewrite swap_id. apply aeq_refl. 
                    ****** apply aeq_m_subst_neq.
                    ******* apply aeq_refl.
                    ******* apply aux_not_equal. assumption.
                    ******* apply notin_union_2 in n0. apply notin_union_1 in n0. simpl in n0. apply notin_remove_1 in n0. destruct n0.
                    ******** contradiction.
                    ******** apply notin_B. assumption.
                    ******* rewrite swap_symmetric. apply aeq_refl.
               **** apply refl. apply m_subst_lemma.
                    ***** repeat apply notin_union_2 in n0. apply notin_singleton_1 in n0. apply aux_not_equal. assumption.
                    ***** apply notin_union_1 in n0. apply notin_B. assumption.
           *** apply refltrans_m_subst_beta.
               **** apply pure_m_subst.
                    ***** apply pure_swap. inversion H. inversion H4. apply pure_B. assumption.
                    ***** apply pure_B. assumption.
               **** inversion H. inversion H4. apply H1; simpl; try lia; assumption. 
               **** apply refltrans_composition with ({x := B t2} B (swap x0 x1 t1_1)).
                    ***** apply refl. apply aeq_m_subst_out. apply aeq_swap_B.
                    ***** apply H1.
                    ****** simpl. rewrite swap_size_eq. lia.
                    ****** apply pure_swap. inversion H. inversion H4. assumption.
        ** destruct (atom_fresh (Metatheory.union (fv_nom t2) (Metatheory.union (fv_nom (n_abs x0 t1_1)) (singleton x)))). apply refl. apply aeq_B. apply aeq_app.
           *** apply aeq_sym. apply m_subst_abs_neq; assumption.
           *** apply aeq_refl.
    + repeat rewrite m_subst_app. change (B (n_app (n_app t1_1_1 t1_1_2) t1_2)) with (n_app (B (n_app t1_1_1 t1_1_2)) (B t1_2)). rewrite m_subst_app.
      change (B (n_app (n_app ({x := t2} t1_1_1) ({x := t2} t1_1_2)) ({x := t2} t1_2))) with ((n_app (B (n_app ({x := t2} t1_1_1) ({x := t2} t1_1_2))) (B ({x := t2} t1_2)))).
      apply refltrans_n_app.
      * specialize (H1 (n_app t1_1_1 t1_1_2)). apply refltrans_composition with (B ({x := t2} n_app t1_1_1 t1_1_2)).
        ** apply H1.
           *** simpl. lia.
           *** inversion H. assumption.
        ** rewrite m_subst_app. apply refltrans_refl. 
      * apply H1.
        ** simpl. lia.
        ** inversion H. assumption.
    + inversion H. inversion H4.
  - inversion H.
Qed.
(* begin hide *)
Lemma refltrans_n_app_B_beta: forall t1 t2, (n_app (B t1) (B t2)) -->>B (B (n_app t1 t2)).
Proof.
  induction t1 as [ x | x t1 IHt1 | t1 IHt1 t2 IHt2 | t1 IHt1 x t2  IHt2].
  - intro t2. simpl. apply refltrans_n_app_right. apply refl. apply aeq_refl.
  - intro t2. simpl. apply rtrans with ({x := B t2} B t1).
    + apply step_redex. apply beta_aeq_step with (n_app (n_abs x (B t1)) (B t2)) ({x := B t2} B t1).
      * apply aeq_refl.
      * apply step_beta.
      * apply aeq_refl.
    + apply refl. apply aeq_refl.
  - intro t'. change (B (n_app (n_app t1 t2) t')) with (n_app (B (n_app t1 t2)) (B t')). apply refltrans_n_app_left. apply refl. apply aeq_refl.
  - intro t'. simpl. apply refl. apply aeq_refl.
Qed.
(* end hide *)

(**

In general, proofs involving the complete development [B] are challenging. The following lemma presents another example of a complex proof. Once again, the difficult case arises when [B] receives an application as an argument, though we will leave this proof withour further commentary.

*)
Lemma beta_implies_refltrans_B: forall t1 t2, pure t1 -> t1 -->B t2 -> (B t1) -->>B (B t2). 
Proof.
  intros t1 t2 Hpure Hbeta. induction Hbeta.
  - inversion H; subst. inversion H1; subst. apply refltrans_composition with (B (n_app (n_abs x t0) t3)).
    + apply refl. apply aeq_B. assumption.
    + simpl. apply refltrans_composition with (B ({x := t3} t0)).
      * assert (Hpure2: pure(n_app (n_abs x t0) t3)). 
        ** apply aeq_pure with t1; assumption.
        ** inversion Hpure2. inversion H5. apply refltrans_m_subst_B_beta; assumption.
      * apply refl. apply aeq_B. assumption.
  - simpl. apply refltrans_n_abs. apply IHHbeta. inversion Hpure; subst. assumption.
  - inversion Hbeta; subst.
    + inversion H; subst. inversion H1; subst. apply refltrans_composition with (B (n_app (n_app (n_abs x t0) t3) t2)).
      * apply refl. apply aeq_B. apply aeq_app.
        ** assumption.
        ** apply aeq_refl.
      * apply refltrans_composition with (B (n_app ({x := t3} t0) t2)).
        ** change (B (n_app (n_app (n_abs x t0) t3) t2) ) with (n_app (B (n_app (n_abs x t0) t3)) (B t2)). simpl (B (n_app (n_abs x t0) t3)). apply refltrans_composition with (n_app (B ({x := t3} t0)) (B t2)).
           *** apply refltrans_n_app.
               **** assert (Hpure2: pure(n_app (n_abs x t0) t3)). 
                    ***** inversion Hpure. apply aeq_pure with t1; assumption.
                    ***** inversion Hpure2. inversion H5. apply refltrans_m_subst_B_beta; assumption.
               **** apply refl. apply aeq_refl.
           *** apply refltrans_n_app_B_beta.
        ** apply refl. apply aeq_B. apply aeq_app.
           *** assumption.
           *** apply aeq_refl.
    + inversion Hpure; subst. apply IHHbeta in H2. simpl in *. apply refltrans_m_subst2_beta.
      * apply pure_B. inversion Hpure; subst. inversion H4; subst. assumption.
      * clear IHHbeta Hpure H H3. replace (B t3) with (swap x x (B t3)).
        ** apply refltrans_n_abs_step_beta. assumption.
        ** rewrite swap_id. reflexivity.
    + change (B (n_app (n_app t0 t3) t2)) with (n_app (B (n_app t0 t3)) (B t2)). change (B (n_app (n_app t1'0 t3) t2)) with (n_app (B (n_app t1'0 t3)) (B t2)). apply refltrans_n_app.
      * apply IHHbeta. inversion Hpure; subst. assumption.
      * apply refl. apply aeq_refl.
    + change (B (n_app (n_app t0 t3) t2)) with (n_app (B (n_app t0 t3)) (B t2)). change (B (n_app (n_app t0 t2') t2)) with (n_app (B (n_app t0 t2')) (B t2)). apply refltrans_n_app.
      * apply IHHbeta. inversion Hpure; subst. assumption.
      * apply refl. apply aeq_refl.
    + inversion Hpure; subst. inversion H2.
    + inversion Hpure; subst. inversion H2.
  - generalize dependent t2'. generalize dependent t2. case t1.
    + intros x t2 Hpure t2' Hbeta IH. simpl. apply refltrans_n_app.
      * apply refl. apply aeq_refl.
      * apply IH. inversion Hpure; subst. assumption.
    + intros x t t2 Hpure t2' Hbeta IH. simpl. apply refltrans_m_subst1. apply IH. inversion Hpure; subst. assumption.
    + intros t0 t2 t3 Hpure t2' Hbeta IH. change (B (n_app (n_app t0 t2) t3)) with (n_app (B (n_app t0 t2)) (B t3)). change (B (n_app (n_app t0 t2) t2')) with (n_app (B (n_app t0 t2)) (B t2')). apply refltrans_n_app.
      * apply refl. apply aeq_refl.
      * apply IH. inversion Hpure; subst. assumption.
    + intros t0 x t2 t3 Hpure t2' Hbeta IH. inversion Hpure; subst. inversion H1.
  - inversion Hpure.
  - inversion Hpure.
Qed.
    
Corollary refltrans_beta_B: forall t1 t2, pure t1 -> t1 -->>B t2 -> B t1 -->>B B t2.
Proof.
  intros t1 t2 Hpure Hbeta. induction Hbeta.
  - apply refl. apply aeq_B. assumption.
  - apply refltrans_composition with (B t2).
    + apply beta_implies_refltrans_B; assumption.
    + apply IHHbeta. apply pure_beta_trans with t1; assumption.
  - apply refltrans_composition with (B t2).
    + apply refl. apply aeq_B. assumption.
    + apply IHHbeta. apply aeq_pure in H; assumption.
Qed.

(**

The proof of (%\ref{lx:zprop-proof3}%) is concluded by applying lemma [refltrans_P] and lemma [pure_refltrans_B].

 *)

Lemma refltrans_P: forall t, t -->>x (P t).
Proof.
  induction t.
    - simpl. apply refltrans_refl.
    - simpl. apply refltrans_n_abs. assumption.
    - simpl. apply refltrans_n_app;assumption.
    - simpl. apply refltrans_composition with ([x :=  t2] P t1).
      + apply refltrans_n_sub_out. assumption.
      + apply refltrans_composition with ([x := P t2] P t1).
        * apply refltrans_n_sub_in. assumption.
        * apply pure_pix. apply pure_P.
Qed.

Lemma pure_refltrans_B: forall t, pure t ->  t -->>lx (B t).
Proof.
  induction t using n_sexp_size_induction.
    - intro Hpure. simpl. apply refltrans_refl.
    - intro Hpure. simpl. apply refltrans_n_abs_lx. apply H.
      + simpl. lia.
      + inversion Hpure; subst. assumption.
    - intro Hpure. inversion Hpure; subst. destruct t1 eqn:Ht1.
      + simpl. apply refltrans_n_app_right_lx. apply H.
        * simpl. lia.
        * assumption.
      + apply refltrans_composition with (n_app (B (n_abs x n)) t2).
        * apply refltrans_n_app_left_lx. apply H.
          ** simpl. lia.
          ** assumption.
        * simpl. apply refltrans_composition with  (n_sub (B n) x t2).
          ** apply refltrans_lx_betax. apply rtrans with ([x := t2] B n); try apply refltrans_refl. apply step_redex. 
             apply betax_aeq_step with (n_app (n_abs x (B n)) t2) ([x := t2] B n).
            *** apply aeq_refl.
            *** simpl. apply step_betax.
            *** apply aeq_refl.
          ** apply refltrans_composition with ({x := t2} B n).
            *** apply refltrans_lx_pix. apply pure_pix. apply pure_B. inversion H2; subst. assumption.
            *** apply refltrans_m_subst1_lx. apply H.
              **** simpl. lia.
              **** assumption.
      + change (B (n_app (n_app n1 n2) t2)) with (n_app (B (n_app n1 n2)) (B t2)). apply refltrans_n_app_lx.
        * apply H.
          ** simpl. lia.
          ** assumption.
        * apply H.
          ** simpl. lia.
          ** assumption.
      + inversion H2. 
    - intro Hpure. inversion Hpure.
Qed.
(* begin hide *)
Lemma pure_refltrans_B_beta: forall t, pure t -> t -->>B (B t).
Proof.
  intros t H. induction t using n_sexp_size_induction.
    - simpl. apply refltrans_refl.
    - simpl. apply refltrans_n_abs. apply H0.
      + simpl. lia.
      + inversion H. assumption.
    - simpl B. destruct t1.
      + simpl. apply refltrans_n_app_right. apply H0.
        * simpl. lia.
        * inversion H. assumption.
      + apply rtrans with ({x := t2} t1).
        * apply step_redex. apply beta_aeq_step with (n_app (n_abs x t1) t2) ({x := t2} t1).
          ** apply aeq_refl.
          ** apply step_beta.
          ** apply aeq_refl.
        * apply refltrans_m_subst_beta.
          ** inversion H. inversion H3. assumption.
          ** apply H0.
            *** simpl. lia.
            *** inversion H. inversion H3. assumption.
          ** apply H0.
            *** simpl. lia.
            *** inversion H. inversion H3. assumption.
      + apply refltrans_n_app.
        * apply H0.
          ** simpl. lia.
          ** inversion H. assumption.
        * apply H0.
          ** simpl. lia.
          ** inversion H. assumption.
      + inversion H. inversion H3.
    - inversion H.
Qed. 

Lemma refltrans_m_subst_B_lx: forall t1 t2 x, pure t1 -> pure t2 -> ({x := B t2} B t1) -->>lx (B ({x := t2} t1)).
Proof.
  intros t1 t2 x H1 H2. apply refltrans_pure_beta_refltrans.
    - apply pure_m_subst; apply pure_B; assumption.
    - apply refltrans_m_subst_B_beta; assumption.
Qed. 

Lemma refltrans_n_app_B_lx: forall t1 t2, pure t1 -> n_app (B t1) (B t2) -->>lx (B (n_app t1 t2)).
Proof.
  induction t1.
  - intros t2 Hpure. simpl. apply refltrans_n_app_right_lx. apply refl. apply aeq_refl.
  - intros t2 Hpure. simpl. apply refltrans_composition with ([x := B t2] B t1).
    + apply rtrans with ([x := B t2] B t1).
      * apply b_rule. apply step_redex. apply betax_aeq_step with (n_app (n_abs x (B t1)) (B t2)) ([x := B t2] B t1).
        ** apply aeq_refl.
        ** apply step_betax.
        ** apply aeq_refl.
      * apply refl. apply aeq_refl.
    + apply pure_pix_2. apply pure_B. simpl in Hpure. inversion Hpure; subst. assumption.
  - intros t2 Hpure. inversion Hpure; subst; clear Hpure. change (B (n_app (n_app t1_1 t1_2) t2)) with (n_app (B (n_app t1_1 t1_2)) (B t2)). apply refl. apply aeq_refl.
  - intros t2 Hpure. inversion Hpure.
Qed.

Lemma refltrans_P_beta: forall t1 t2, t1 -->lx t2 -> (P t1) -->>B (P t2).
Proof.
  intros t1 t2 H. induction H.
  - apply refltrans_Bx_P_beta. assumption.
  - apply pi_P in H. apply refl. assumption.
Qed.
(* end hide *)
(**

The second diagram in (%\ref{lx:zprop-proof}%) is proved by the following two lemmas:

*)

Lemma refltrans_lx_P2: forall t1 t2, t1 -->Bx t2 -> t2 -->>lx (B(P t1)).
(**

%\noindent {\bf Proof.}% The proof is by induction on $t_1 \to_{Bx} t_2$. The interesting cases are when
%\begin{center}$t_1 = \esub{t_{11}}{x}{t_{12}} \to_{Bx} \esub{t_{11}'}{x}{t_{12}} = t_2$, with $t_{11} \to_{Bx} t_{11}'$\end{center}% and
%\begin{center}$t_1 = \esub{t_{11}}{x}{t_{12}} \to_{Bx} \esub{t_{11}}{x}{t_{12}'} = t_2$, with $t_{12} \to_{Bx} t_{12}'$.\end{center}%

Both cases have similar proofs, therefore we consider only the first reduction. We proceed as follows:

%\begin{mathpar}
\inferrule*[Right={({\sf def-P})}]{ \inferrule*[Right={({\sf trans})}]{ \inferrule*[Left={({\sf def-B})}]{ \inferrule*[Left={({\sf compat})}] { \inferrule*[Right={({\sf i.h.})}]{~} {t_{11}' \tto_{lx} B (P\ t_{11})} \and \inferrule{(\star)}{t_{12} \tto_{lx} B (P\ t_{12})}} {\esub{t_{11}'}{x}{t_{12}} \tto_{lx} \esub{B (P\ t_{11})}{x}{B( P\ t_{12})}}} {\esub{t_{11}'}{x}{t_{12}} \tto_{lx} B(\esub{(P\ t_{11})}{x}{P\ t_{12}})} \and \inferrule{(\star\star)} {B(\esub{(P\ t_{11})}{x}{P\ t_{12}}) \tto_{lx} B(\metasub{(P\ t_{11})}{x}{P\ t_{12}})}} {\esub{t_{11}'}{x}{t_{12}} \tto_{lx} B(\metasub{(P\ t_{11})}{x}{P\ t_{12}})}} {\esub{t_{11}'}{x}{t_{12}} \tto_{lx} B(P(\esub{t_{11}}{x}{t_{12}}))}
\end{mathpar}%

%\noindent% where $(\star)$ is easily proved by lemmas [refltrans_P], [pure_P] and [pure_refltrans_B], and $(\star\star)$ is proved as follows:

%\begin{mathpar}
 \inferrule*[Right={({\sf def-B})}] { \inferrule*[Right={({\sf trans})}] { \inferrule{(\star\star\star)}{\esub{(B(P\ t_{11}))}{x}{B(P\ t_{12})} \tto_{lx} \metasub{(B(P\ t_{11}))}{x}{B(P\ t_{12})}} \and (\star\star\star\star) } {\esub{(B((P\ t_{11})))}{x}{B(P\ t_{12})} \tto_{lx} B(\metasub{(P\ t_{11})}{x}{P\ t_{12}}) }} {B(\esub{(P\ t_{11})}{x}{P\ t_{12}}) \tto_{lx} B(\metasub{(P\ t_{11})}{x}{P\ t_{12}})}
\end{mathpar}%

%\noindent% where $(\star\star\star)$ is proved by lemma [pure_pix] since $\to_x \subseteq \to_{lx}$, and $(\star\star\star\star)$ is given by the reduction

%\begin{equation}\label{red:lx}\metasub{(B((P\ t_{11})))}{x}{B(P\ t_{12})}  \tto_{lx}  B(\metasub{(P\ t_{11})}{x}{P\ t_{12}})\end{equation}%

Since the terms $(P\ t_{11})$ and $(P\ t_{12})$ are pure, the reduction (%\ref{red:lx}%) can be done with $\to_\beta$, that is, it can be translated to  

%\begin{center}$\metasub{(B((P\ t_{11})))}{x}{B(P\ t_{12})}  \tto_{lx}  B(\metasub{(P\ t_{11})}{x}{P\ t_{12}})$\end{center}%

%\noindent% and we are done by lemma [refltrans_m_subst_B_beta]. %\hfill%$\Box$

*)
Proof. 
  intros t1 t2 H. induction H.
  - inversion H; subst. inversion H1; subst. apply refltrans_composition with ([x := t3] t0).
    + apply refl. apply aeq_sym. assumption.
    + apply refltrans_composition with (B (P (n_app (n_abs x t0) t3))).
      * simpl. apply refltrans_composition with ([x := (B (P t3))] (B (P t0))).
        ** apply refltrans_n_sub_lx.
           *** apply refltrans_composition with (P t3).
               **** apply refltrans_lx_pix. apply refltrans_P.
               **** apply pure_refltrans_B. apply pure_P.
           *** apply refltrans_composition with (P t0).
               **** apply refltrans_lx_pix. apply refltrans_P.
               **** apply pure_refltrans_B. apply pure_P.
        ** apply pure_pix_2. apply pure_B. apply pure_P.
      * apply refl. apply aeq_B. apply aeq_P. apply aeq_sym. assumption.
  - simpl. apply refltrans_n_abs_lx. apply IHctx.
  - apply refltrans_composition with (n_app (B (P t1)) (B (P t2))).
    + apply refltrans_n_app_lx.
      * assumption.
      * apply refltrans_composition with (P t2).
        ** apply refltrans_lx_pix. apply refltrans_P.
        ** apply pure_refltrans_B. apply pure_P.
    + apply refltrans_n_app_B_lx. apply pure_P.
  - simpl P. apply refltrans_composition with (n_app (B (P t1)) (B (P t2))).
    * apply refltrans_n_app_lx.
      ** apply refltrans_composition with (P t1).
         *** apply refltrans_lx_pix. apply refltrans_P.
         *** apply pure_refltrans_B. apply pure_P.
      ** assumption.
    * apply refltrans_n_app_B_lx. apply pure_P.
  - simpl. apply refltrans_composition with (B([x := (P t2)] (P t1))).
    + simpl. apply refltrans_n_sub_lx.
      * apply refltrans_composition with (P t2).
        ** apply refltrans_lx_pix. apply refltrans_P.
        ** apply pure_refltrans_B. apply pure_P.
      * apply IHctx. 
    + simpl. apply refltrans_composition with ({x := B (P t2)} B (P t1)).
      * apply refltrans_lx_pix. apply pure_pix. apply pure_B. apply pure_P.
      * apply refltrans_m_subst_B_lx; apply pure_P.
  - apply refltrans_composition with (([x := (B (P t2))] (B (P t1)))).
    + apply refltrans_n_sub_lx.
      * assumption.
      * apply refltrans_composition with (P t1).
        ** apply refltrans_lx_pix. apply refltrans_P.
        ** apply pure_refltrans_B. apply pure_P.
    + simpl. apply refltrans_composition with ({x := (B (P t2))} (B (P t1))).
      * apply refltrans_lx_pix. apply pure_pix. apply pure_B. apply pure_P.
      * apply refltrans_m_subst_B_lx; apply pure_P.
Qed.  

Lemma refltrans_lx_B_P: forall t1 t2, t1 -->Bx t2 -> (B (P t1)) -->>lx (B (P t2)).
Proof. 
 intros t1 t2 H. apply refltrans_pure_beta_refltrans. 
    - apply pure_B. apply pure_P.
    - apply refltrans_Bx_P_beta in H. apply refltrans_beta_B.
      + apply pure_P.
      + assumption.
Qed.  

(**
%\noindent {\bf Proof}.% Similar to the reasoning in the previous lemma, the reduction $(B (P t_1)) \tto_{lx} (B (P t_2))$ can be translated to $(B (P t_1)) \tto_{\beta} (B (P t_2))$, since both $(P\ t_1)$ and $(P\ t_2)$ are pure terms. We leave the details to the interested reader explore in the source code of the formalization. %\hfill%$\Box$


TODO
- citar Metalib
- criar repo e inserir link no documento
- proofs close to paper and pencil approach
- Adaptações em ZtoConfl

*)

(* begin hide *)
Lemma lambda_x_Z_comp_aeq: Z_comp_aeq betapi.
Proof.
  unfold Z_comp_aeq. exists pix_ctx, betax_ctx, P, B. split.
  - intros t1 t2; split.
    + intro H. apply union_or. apply or_comm. apply ctx_betax_beta_pix. assumption.
    + intro H. apply ctx_betax_beta_pix. apply or_comm. apply union_or. assumption.
  - split. 
    + intros t1 t2 H. split.
      * apply pi_P. assumption.
      * unfold comp. apply pi_P in H. apply aeq_B. assumption. 
    + split.
      * intros t1 t2 H. unfold comp. apply aeq_B. apply aeq_P. assumption.
      * split.
        ** intro t. apply refltrans_P.
        ** split.
        *** intros t1 t2 H. rewrite H. apply pure_refltrans_B. apply pure_P.
        *** unfold f_is_weak_Z. unfold comp. intros t1 t2 H. split.
            **** apply refltrans_lx_P2. assumption.
            **** apply refltrans_lx_B_P. assumption.
Qed.
  
Theorem lambda_x_is_confluent: Confl betapi.
Proof.
  apply Z_prop_aeq_implies_Confl.
  apply Z_comp_aeq_implies_Z_prop_aeq.
  apply lambda_x_Z_comp_aeq.
Qed.

(* end hide *)

