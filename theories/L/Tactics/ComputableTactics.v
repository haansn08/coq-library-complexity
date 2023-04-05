Require Export Undecidability.L.Tactics.ComputableTactics.
From Undecidability.L.Tactics Require Import Lbeta Lproc Lsimpl.
Require Import Complexity.L.Tactics.ComputableTime.

Require Import MetaCoq.Template.All.

Ltac cstep' extractSimp:=
  let x := fresh "x" in
  once lazymatch goal with
  | |- computes _ _ (match ?x with _ => _ end)=>
    let eq := fresh "eq" in destruct x eqn:eq
  | |- computes (TyArr ?tt1 ?tt2) ?f ?intF=>
    let fRep := constr:(ltac:(quote_term f (fun x => exact x))) in
    once lazymatch fRep with
      (* a potentially recursive step *)
      Ast.tFix (_::_::_) => fail 1000 "mutual recursion not supported"
    | Ast.tFix [BasicAst.mkdef _ _ _(*<-dtype*) _(*<-dbody*) ?recArg(*<-recArg*)] 0 =>
      (let P := fresh "P" in
      Intern.recRem P;
      eapply computesExpStart;[solve [Lproc]|];
      let n:= (eval cbn in (S recArg)) in
      let rec step n:=
          (once lazymatch n with
           |  S ?n =>
              eexists;
              eapply computesExpStep;[try recStep P;extractSimp;Intern.shelveIfUnsolved "pos5"|Lproc;Intern.shelveIfUnsolved "pos6"|];
              (*simple notypeclasses refine (_:computes (_ ~> _) _ _ (fun x xInt xNorm => (_,_)));try exact tt;shelve_unifiable;*)
              let x := fresh "x" in  
              let xInt := fresh x "Int" in
              let xInts := fresh x "Ints" in
              intros x xInt xInts;
              change xInt with (@ext _ _ x (Build_computable xInts));
              once lazymatch type of xInts with
                computes (@TyB _ ?reg) _ _ =>
                rewrite (ext_is_enc (Build_computable xInts)) in *;
                clear xInt xInts;assert (xInt:True) by constructor; assert (xInts:True) by constructor
              | computes (TyArr _ _) _ _ => idtac
              end;
              step n;
              revert x xInt xInts
           | 0 => idtac
           end) in
      step n;
        let IH := fresh "IH" P in
        Intern.ugly_fix_fix IH recArg;
          let rec loop n := (* destruct the struct-recursive argument*)
              once lazymatch n with
                0 => intros [] ? ?
              | S ?n' => intros ? ? ?;loop n'
              end in
          loop recArg;
          eexists;
          (split;[try Intern.recStepNew P;extractSimp;Intern.shelveIfUnsolved "pos7"|]))

    (* a non-recursive function *)
    | _=>
      let xInt := fresh x "Int" in
      let xNorm := fresh x "Norm" in
      let xInts := fresh x "Ints" in
      let vProc := fresh "vProc" in
      (*simple notypeclasses refine (_:computes (tt1 ~> tt2) _ _ (fun x xInt xNorm => (_,_)));try exact tt;shelve_unifiable;*)
      eapply computesTyArr;[try Lproc;Intern.shelveIfUnsolved "pos1"|idtac];
      intros x xInt xInts;
      change xInt with (@ext _ _ x (Build_computable xInts));
      once lazymatch tt1 with
        TyB _ => rewrite (ext_is_enc (Build_computable xInts)) in *;
                clear xInt xInts;assert (xInt:True) by constructor; assert (xInts:True) by constructor
      | _ => idtac
      end;
      eexists;split;[extractSimp;Intern.shelveIfUnsolved "pos2" | intros vProc]
    end

  | |- computes (TyB _) _ ?t=> has_no_evar t;apply computesTyB

  | |- computes _ _ (@ext _ _)=> apply extCorrect


  (* with time bounds: *)
  | H : Lock _ |- computesTime _ _ (match ?x with _ => _ end) _=>
    let t := type of x in
    unlock H;revert H;(refine (_: ((fun z:t => ltac:(destruct z):Prop) x) -> _);intros H;lock H);
    let eq := fresh "eq" in destruct x eqn:eq
  | H:Lock _ |- computesTime (TyArr ?tt1 ?tt2) ?f ?intF ?T=>
    let fRep := constr:(ltac:(quote_term f (fun x => exact x))) in
    once lazymatch fRep with
      Ast.tFix (_::_::_) => fail 1000 "mutual recursion not supported"
    | Ast.tFix [BasicAst.mkdef _ _ _(*<-dtype*) _(*<-dbody*) ?recArg(*<-recArg*)] 0 =>
      let P := fresh "P" in
      let H' := fresh H "'" in
      Intern.recRem P;
      eapply computesTimeExpStart;[solve [Lproc]|];
      let n:= (eval cbn in (S recArg)) in
      let rec step n:=
          (once lazymatch n with
           |  S ?n' =>
              eexists;
              let x := fresh "x" in  
              let xInt := fresh x "Int" in
              let xT := fresh x "T" in
              let xInts := fresh x "Ints" in
              (refine (computesTimeExpStep (fT:=fun x xT => _) _ _ _ _) ;
               [|try Intern.recStepNew P;extractSimp;Intern.shelveIfUnsolved "pos8"|Lproc;Intern.shelveIfUnsolved "pos9"|]);
              [try reflexivity;Intern.is_assumed_add|];Intern.clean_assumed;
              (*simple notypeclasses refine (_:computes (_ ~> _) _ _ (fun x xInt xNorm => (_,_)));try exact tt;shelve_unifiable;*) 
              intros x xInt xT; Intern.intro_to_assumed x;Intern.intro_to_assumed xT;intro xInts;
              change xInt with (@extT _ _ x _ (Build_computableTime xInts));
              once lazymatch type of xInts with
                computesTime (@TyB _ ?reg) _ _ _=>
                rewrite (extT_is_enc (Build_computableTime xInts)) in *;
                destruct xT;
                clear xInt xInts;assert (xInt:True) by constructor; assert (xInts:True) by constructor; assert (xT:True) by constructor
              | computesTime (TyArr _ _) _ _ _=> idtac
              end;
              step n';
              revert x xInt xT xInts
           | 0 => idtac
           end) in
      step n;
        
      let IH := fresh "IH" P in
      Intern.ugly_fix_fix2 IH recArg;
        let rec loop n := (* destruct the struct-recursive argument*)
            (Intern.clean_assumed;
             let x := fresh "x" in
             let xT := fresh x "T" in
             intros x ? xT ? ;
             let tx := type of x in
             let txT := type of xT in
             unlock H; revert H;refine (_ : (forall (x:_) (xT:_) , (_ :Prop)) -> _ );
             intros H;specialize (H x xT);lock H;
             once lazymatch n with
               0 => unlock H;revert H;(refine (_: ((fun z:tx => ltac:(destruct z):Prop) x) -> _);intros H;lock H);
                   eexists (ltac:(destruct x));destruct x;(split;unlock H;
                   [
                     once lazymatch goal with
                       |- evalLe ?k _ _ =>
                       refine (le_evalLe_proper _ eq_refl eq_refl _);[refine (proj1 H);shelve|apply proj2 in H;lock H];
                       try Intern.recStepNew P;extractSimp;Intern.shelveIfUnsolved "pos10"
                     end
                    |apply proj2 in H;lock H])
             | S ?n' => loop n'
             end ) in
        loop recArg
    (* non-recursive function*)
    |  _ =>
      let xInt := fresh x "Int" in
      let xNorm := fresh x "Norm" in
      let xInts := fresh x "Time" in
      let xInts := fresh x "Ints" in
      let xT := fresh x "T" in
      let vProc := fresh "vProc" in
      (*simple notypeclasses refine (_:computes (tt1 ~> tt2) _ _ (fun x xInt xNorm => (_,_)));try exact tt;shelve_unifiable;*)
      eapply computesTimeTyArr_helper with (time := fun x xT => _);[try Lproc;Intern.shelveIfUnsolved "pos3"|];
      intros x xT;Intern.intro_to_assumed x;Intern.intro_to_assumed xT;
      Intern.split_assumed;[now Intern.is_assumed|];
      intros xInt xInts;
      change xInt with (@extT _ _ x _ (Build_computableTime xInts));
      once lazymatch tt1 with
        TyB _ => rewrite (extT_is_enc (Build_computableTime xInts)) in *;
                clear xInt xInts;assert (xInt:True) by constructor; assert (xInts:True) by constructor
      | _ => idtac
      end;
      eexists;split;[extractSimp;Intern.shelveIfUnsolved "pos4"| intros vProc]
    end
  (* complexity: *)

  | H : Lock _ |- computesTime (TyB _) _ ?t ?tt=> has_no_evar t;Intern.close_assumed; destruct tt;apply computesTimeTyB
  | H : Lock _ |-computesTime _ _ (@extT _ _) _ => apply extTCorrect

  | |- computesTime _ _ _ _ =>
    match goal with
    |  H : Lock _ |- _ => fail 1
    | |- _ => 
      refine (computesTimeIfStart (P:= fun fT => _) _ _);
      [let H := fresh "H" in
       let fT := fresh "fT" in
       intros fT H; lock H|] (* introduce the assumptions for the recurence equations to be collected *)
    end
  end.

Ltac cstep := cstep' Intern.extractSimple.

Ltac infer_instancesT :=
  repeat match goal with
         | [ |- context [ int_ext ?t ] ] => first [change (int_ext t) with (extT t) | fail 3 "Could not fold extT-instance for " t]
         | [ |- context [ ext ?t ] ] => first [change (ext t) with (extT t) | fail 3 "Could not fold extT-instance for " t]
         end.

Ltac computable_using_noProof Lter:=
  once lazymatch goal with
  | [ |- computable ?t ] => Undecidability.L.Tactics.ComputableTactics.Intern.computable_using_noProof Lter
  | [ |- computableTime ?t _] =>
    eexists Lter;unfold Lter;try clear Lter;
    let t' := (eval hnf in t) in
    let h := Undecidability.L.Tactics.ComputableTactics.Intern.visibleHead t' in
    try unfold h; Undecidability.L.Tactics.ComputableTactics.Intern.computable_prepare t; infer_instancesT
  end.

Tactic Notation "computable" "using" open_constr(Lter) :=
  computable_using_noProof Lter;repeat cstep.

Tactic Notation "extract" "constructor":=
  let term := fresh "used_term" in
        once lazymatch goal with
        | [ |- computable ?t ] => extract constructor
        | [ |- computableTime ?t _] =>
          run_template_program (tmExtractConstr' None t)
                               (fun e =>  pose (term:= ( e : extracted t)); computable using term)
   end.

(* solverec *)
Local Ltac solverecTry := cbn [timeComplexity] in *;
                          (repeat (intros; intuition idtac;
                                   repeat match goal with
                                          | t:unit |- _ =>
                                            destruct t
                                          end;
                                   try (let H:= fresh "H" in destruct _ eqn:H);cbn -[mult plus];try ring_simplify);try lia).
Ltac solverec :=   try abstract (solverecTry);solverecTry.
