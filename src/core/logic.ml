(*
 * module Logic
 * author: Costin Badescu
 *)

module S = Substitution.LF
open Printf
open Syntax.Int


module Options = struct

  (* Enable the logic programming engine. *)
  let enableLogic = ref true

  (*
   * Control verbosity level:
   *   0 => No output.
   *   1 => Query and success notification.
   *   2 => + Error messages.
   *   3 => + Solutions and proof terms.
   *   4 => + LF signature.
   *)
  let chatter = ref 3

  (* Ask before giving more solutions (à la Prolog). *)
  let askSolution = ref false

  (* Type check the proof terms. *)
  let checkProofs = ref false

end


(*
 * Naming conventions:
 * 
 *   g : goal
 * Goal.
 *   r : res
 * Residual goal.
 *   cPsi : LF.dctx
 * Universal typing context.
 *   tD : typ_decl
 * LF type declaration.
 *   dPool : dPool
 * Pool of dynamic assumptions.
 *   cG : conjunction
 * Conjunction of goals.
 *   eV : LF.dctx
 * Context with TypDecl's of existential variables belonging to a clause.
 *   dCl : clause
 * Dynamic clause.
 *   sCl : clause
 * Clause from LF signature.
 *   cS : int
 * Constant shift for BVar indices bound to existential variables.
 *   dS : int
 * Dynamic shift for indices of variables in dynamic clauses.
 *   dR : int
 * Range of de Bruijn indices in the dynamic scope.
 *)


type goal =                             (* Goals            *)
  | Atom of LF.typ                      (* g ::= A          *)
  | Impl of (res * LF.typ_decl) * goal  (*     | r => g'    *)
  | All  of LF.typ_decl * goal          (*     | ∀x:A. g'   *)

and res =                               (* Residual Goals   *)
  | Head   of LF.typ                    (* r ::= A          *)
  | And    of goal * res                (*     | g ∧ r'     *)
  | Exists of LF.typ_decl * res         (*     | ∃x:T. r'   *)

type conjunction =                      (* Subgoals         *)
  | True                                (* cG ::= True      *)
  | Conjunct of conjunction * goal      (*      | cG' ∧ g   *)

type bound = int option                 (* b ::= '*' | nat  *)

and query = (goal * LF.sub)             (* q ::= (g, s)     *)

type clause =                    (* Horn Clause ::= eV |- A :- cG   *)
    { tHead    : LF.typ          (* Head A : LF.Atom                *)
    ; eVars    : LF.dctx         (* Context eV : EV's bound in A/cG *)
    ; subGoals : conjunction }   (* Subgoals cG : solv. cG => A     *)

module Shift : sig

  val atom : LF.typ -> (int * int * int) -> LF.typ

end = struct

  (* NB.
   *
   * Only BVar's in LF.Atom's are affected.
   * Enclosed substitutions are not shifted.
   * 
   * i: De Bruijn index.
   * k: Shifting measure.
   * 
   * Algorithm:
   * 
   * BV bound by λ remain invariant.
   *  - i < lR |- BV(i) -> BV(i)
   * 
   * BV bound by a dynamic scope are shifted by dS.
   *  - lR < i <= dR |- BV(i) -> BV(i + dS)
   * 
   * BV bound to EV are shifted by k.
   *  - i > lR && i > dR |- BV(i) -> BV(i + k)
   *
   * 
   * Notations:
   * 
   * tA : LF type
   * tS : LF spine
   * tN : LF normal
   * tH : LF head
   *)

  let lR = ref 0               (* Range of Lambda Scope  *)
  let dR = ref 0               (* Range of Dynamic Scope *)
  let dS = ref 0               (* Dynamic Shift          *)

  (* val typ : LF.typ -> int -> LF.typ *)
  let rec typ tA k  =
    match tA with
      | LF.Atom (l, c, tS) ->
	LF.Atom (l, c, spine tS k)

      | x -> x

  (* val spine : LF.spine -> int -> spine *)
  and spine tS k  =
    match tS with
      | LF.App (tN, tS) ->
	LF.App (normal tN k, spine tS k)

      | LF.SClo (tS, s) ->
	LF.SClo (spine tS k, s)

      | LF.Nil -> LF.Nil

  (* val normal : LF.normal -> int -> LF.normal *)
  and normal tN k =
    match tN with
      | LF.Lam (l, n, tN') ->
	(
          incr lR;
          let tM = LF.Lam (l, n, normal tN' k) in
          decr lR;
	  tM
	)
    | LF.Root (l, tH, tS) ->
      LF.Root (l, head tH k, spine tS k)

    | LF.Clo (tN, s) ->
      LF.Clo (normal tN k, s)

    | LF.Tuple (l, tP) ->
      LF.Tuple (l, tuple tP k)

  (* val head : LF.head -> int -> LF.head *)
  and head tH k =
    match tH with
      | LF.BVar (i) ->
	if i > !lR && i > !dR then
          LF.BVar (i + k)
	else if i > !lR && i <= !dR then
          LF.BVar (i + !dS)
	else
          LF.BVar (i)

      | LF.AnnH (tH, tM) ->
	LF.AnnH (head tH k, tM)

      | LF.Proj (tH, n) ->
	LF.Proj (head tH k, n)

      | x -> x

  (* val tuple : LF.tuple -> int -> LF.tuple *)
  and tuple tP k =
    match tP with
      | LF.Last (tN) ->
	LF.Last (normal tN k)

      | LF.Cons (tN, tP') ->
	LF.Cons (normal tN k, tuple tP' k)

  (* val atom : LF.typ -> int * int * int -> LF.typ *)
  let atom tA (cS, dS', dR') =
    dR := dR';
    dS := dS';
    typ tA cS

end


module Convert = struct

  (* val typToClause' LF.dctx -> conjunction -> LF.typ -> int * int * int -> clause
   *
   * typToClause' eV cG M (cS, dS, dR) = clause
   * Invariants:
   *   If BV(i) is free in M, then BV(i) is bound in (eV |- M).
   *   If M = PiTyp (x:A, No), then M ~ g.
   *)
  let rec typToClause' eV cG tM (cS, dS, dR) =
    match tM with
      | LF.PiTyp ((tD, LF.Maybe), tM') ->
	typToClause' (LF.DDec (eV, tD)) cG tM' (cS, dS, dR)
	  
      | LF.PiTyp ((LF.TypDecl(_, tA), LF.No), tB) ->
	typToClause' eV (Conjunct (cG, typToGoal tA (cS, dS, dR)))
          tB (cS + 1, dS, dR)
	  
      | LF.Atom (_) as tA ->
	{ tHead    = (Shift.atom tA (-cS, -dS, dR))
	; eVars    = eV
	; subGoals = cG }

  (* val typToGoal LF.typ -> int * int * int -> goal *)
  and typToGoal tM (cS, dS, dR) =
    match tM with
      | LF.PiTyp ((tD, LF.Maybe), tM') ->
	All (tD, typToGoal tM' (cS, dS, dR + 1))

      | LF.PiTyp ((LF.TypDecl (x, tA) as tD, LF.No), tB) ->
	Impl ((typToRes tA (cS, dS, dR), tD),
	      typToGoal tB (cS, dS, dR + 1))

      | LF.Atom (_) as tA ->
	Atom (Shift.atom tA (-cS, -dS, dR))
	  
  (* val typToRes LF.typ -> int * int * int -> res *)
  and typToRes tM (cS, dS, dR) =
    match tM with
      | LF.PiTyp ((tD, LF.Maybe), tM') ->
	Exists (tD, typToRes tM' (cS, dS, dR + 1))

      | LF.PiTyp ((LF.TypDecl (_, tA), LF.No), tB) ->
	And (typToGoal tA (cS, dS, dR), typToRes tB
          (cS + 1, dS + 1, dR + 1))

      | LF.Atom (_) as tA ->
	Head (Shift.atom tA (-cS, -dS, dR))

  (* val resToClause' : LF.dctx -> LF.conjunction -> res * LF.sub -> clause *)
  let rec resToClause' eV cG (r, s) =
    match r with
      | Exists (tD, r') ->
	resToClause' (LF.DDec (eV, tD)) cG (r', S.dot1 s)

      | And (g, r') ->
	resToClause' eV (Conjunct (cG, g)) (r', s)

      | Head (tA) ->
	let (tA', _) = Whnf.whnfTyp (tA, s) in
	{ tHead    = tA'
	; eVars    = eV
	; subGoals = cG }

  (* val resToClause : res * LF.sub -> clause *)
  let resToClause (r, s) =
    resToClause' LF.Null True (r, s)

  (* val typToClause : LF.typ -> clause *)
  let typToClause tM =
    typToClause' LF.Null True tM (0, 0, 0)
      
  (* val etaExpand : LF.dctx -> LF.tclo -> LF.normal
   *  LF.tclo = LF.typ * LF.sub
   *
   * etaExpand Psi (A, s) = normal
   * Invariants:
   *   Psi |- s : Phi
   *   Phi |- A : LF.typ
   * 
   * Effects:
   *   None.
   *)
  let rec etaExpand cPsi sA =
    let (tA, s) = Whnf.whnfTyp sA in
    match tA with
      | LF.Atom (_) as tA ->
        let u = Whnf.newMVar None (cPsi, LF.TClo (tA, s)) LF.Maybe in
        LF.Root (Syntax.Loc.ghost, LF.MVar (u, S.id), LF.Nil)
	  
      | LF.PiTyp ((LF.TypDecl (x, tA) as tD, _), tB) ->
        LF.Lam (Syntax.Loc.ghost, x, etaExpand
          (LF.DDec (cPsi, S.decSub tD s)) (tB, S.dot1 s))

  (* val dctxToSub : LF.dctx -> LF.dctx * LF.sub -> (LF.spine -> LF.spine)
   *                 -> (LF.sub * (LF.spine -> LF.spine))
   *
   * dctxToSub Psi (eV, s) fS = sub * (spine -> spine)
   * Invariants:
   *   eV = Null | ((Null, Dec (x, M)), ...)
   *   Psi |- s : Phi
   *   Phi |- M
   *   fS : spine -> spine
   * 
   * Effects:
   *   None.
   * 
   * Create MVars for all the TypDecl's in eV. Accumulate them
   * in a substitution, performing eta-expansion if necessary,
   * and add them to the spine of a proof-term through fS.
   *)
  let rec dctxToSub cPsi (eV, s) fS =
    match eV with
      | LF.DDec (eV', LF.TypDecl (_, tM)) ->
	let (s', fS') = dctxToSub cPsi (eV', s) fS in
	let tM' = etaExpand cPsi (tM, s') in
	(LF.Dot (LF.Obj tM', s'), (fun tS -> fS' (LF.App (tM', tS))))
	  
      | LF.Null -> (s, fS)
	
      | LF.CtxVar (_) ->
	invalid_arg "Logic.Convert.dctxToSub: Match conflict with LF.CtxVar (_)."
	  
  (* val typToQuery : LF.typ * int -> (query * LF.typ * LF.sub * Index.inst list)
   *  Index.inst = Id.name * LF.normal
   * 
   * typToQuery (M, i)  = ((g, s), xs)
   * Transform a reconstructed LF.typ into a query, accumulating all
   * the abstracted existential variables into a substitution while
   * storing the MVars into a list `xs' for immediate access.
   *)
  let typToQuery (tA, i) =
    let rec typToQuery' (tA, i) s xs =
      match tA with
	| LF.PiTyp ((LF.TypDecl (x, tA), LF.Maybe), tB) when i > 0 ->
          let tN' = etaExpand LF.Null (tA, s) in
          typToQuery' (tB, i - 1) (LF.Dot (LF.Obj tN', s))
            ((x, tN') :: xs)
	
	| _ -> ((typToGoal tA (0, 0, 0), s), tA, s, xs)
    in
    typToQuery' (tA, i) S.id []

  (* val solToSub : Index.inst list -> LF.sub
   *  Index.inst = Id.name * LF.normal
   *)
  let rec solToSub xs =
    match xs with
      | [] -> S.id
      | (x, tN) :: xs -> LF.Dot (LF.Obj tN, solToSub xs)

end


module Index = struct

  open Store

  let types = Hashtbl.create 0          (* typConst Hashtbl.t          *)

  type inst = (Id.name * LF.normal)     (* I ::= (x, MVar)             *)

  and sgnQuery =
      { query     : query               (* Query ::= (g, s)            *)
      ; typ       : LF.typ              (* Query as LF.typ.            *)
      ; skinnyTyp : LF.typ              (* Query stripped of E-vars.   *)
      ; optName   : Id.name option      (* Opt. name of proof term.    *)
      ; expected  : bound               (* Expected no. of solutions.  *)
      ; tries     : bound               (* No. of tries to find soln.  *)
      ; instMVars : inst list }         (* MVar instantiations.        *)
	
  (*type sgnClause = Id.cid_term * clause*)

  let queries = DynArray.create ()      (* sgnQuery DynArray.t         *)

  let querySub = ref S.id

  (* val addTyp : Id.cid_typ -> sgnClause DynArray.t
   *  sgnClause = Id.cid_term * clause
   * 
   * addTyp c = sgnClause DynArray.t
   * Create a new entry for a type constant, c, in the `types' table and
   * return it's mapping, i.e. an empty DynArray.
   *)
  let addTyp cidTyp =
    let sgnClauseArray = DynArray.create () in
    Hashtbl.add types cidTyp sgnClauseArray;
    sgnClauseArray

  (* val addSgnClause : sgnClause DynArray.t -> sgnClause -> unit
   *
   * addSgnClause tC, sCl = ()
   * Add a new sgnClause, sCl, to the DynArray tC.
   *)
  let addSgnClause typConst sgnClause =
    DynArray.add typConst sgnClause

  (* val addSgnQuery : Id.name option * LF.typ * LF.typ * query * inst list * bound * bound -> unit
   *
   * addSgnQuery (p, (g, s), xs, e, t)  = ()
   * Add a new sgnQuery to the `queries' DynArray.
   *)
  let addSgnQuery (p, a, a', q, xs, e, t) =
    DynArray.add queries
      { query     = q
      ; typ       = a
      ; skinnyTyp = a'
      ; optName   = p
      ; expected  = e
      ; tries     = t
      ; instMVars = xs }

  (* val compileSgnClause : Id.cid_term -> Id.cid_term
   *
   * compileSgnClause c = (c, sCl)
   * Retrieve LF.typ for term constant c, clausify it into sCl and
   * return an sgnClause (c, sCl).
   *)
  let compileSgnClause cidTerm =
    let termEntry = Cid.Term.get cidTerm in
    let tM = termEntry.Cid.Term.typ in
    (cidTerm, Convert.typToClause tM)

  (* val termName : Id.cid_term -> Id.name
   * 
   * termName c = Id.name
   * Get the string representation of term constant c.
   *)
  let termName cidTerm =
    (Cid.Term.get cidTerm).Cid.Term.name

  (* val storeTypeConst : Id.cid_typ -> unit
   *
   * storeTypConst c = ()
   * Add a new entry in `types' for type constant c and fill the DynArray
   * with the clauses corresponding to the term constants associated with c.
   * The revIter function serves to preserve the order of term constants
   * intrinsic to the Beluga source file, since the constructors for c are
   * listed in reverse order.
   *)
  let storeTypConst cidTyp =
    let typEntry = Cid.Typ.get cidTyp in
    let typConstr = !(typEntry.Cid.Typ.constructors) in
    let typConst = addTyp cidTyp in
    let regSgnClause cidTerm =
      addSgnClause typConst (compileSgnClause cidTerm) in
    let rec revIter f l = match l with
      | [] -> ()
      | h :: l' -> revIter f l' ; f h
    in revIter regSgnClause typConstr

  (* val Id.name option * (LF.typ * int) * bound * bound -> unit
   * 
   * storeQuery (p, (M, i), e, t) = ()
   * Invariants:
   *   i = count of abstracted EVars in M
   *)
  let storeQuery (p, (tM, i), e, t) =
    let (q, tM', s, xs) = Convert.typToQuery (tM, i) in
    querySub := s;
    addSgnQuery (p, tM, tM', q, xs, e, t)

  (* val robStore : unit -> unit
   *
   * robStore () = ()
   * Store all type constants in the `types' table.
   *)
  let robStore () =
    try
      List.iter storeTypConst !(DynArray.get Cid.Typ.entry_list !(Modules.current))
    with _ -> ()

  (* val iterSClauses : (Id.cid_term * clause -> unit) -> Id.cid_typ -> unit
   *
   * iterSClauses f c = ()
   * Iterate over all signature clauses associated with c.
   *)
  let iterSClauses f cidTyp =
    DynArray.iter f (Hashtbl.find types cidTyp)

  let iterAllSClauses f =
    Hashtbl.iter (fun k v -> DynArray.iter f v) types

  let iterQueries f =
    DynArray.iter (fun q -> f q) queries

  (* clearIndex () = ()
     Empty the local storage.
  *)
  let clearIndex () = DynArray.clear queries ; Hashtbl.clear types


  let singleQuery (p, (tM, i), e, t) f =
    let (q, tM', s, xs) = (Convert.typToQuery (tM, i)) in
    ignore (querySub := s) ;
    robStore();
    let bchatter = !Options.chatter in
    Options.chatter := 0;
    let sgnQ = { query = q ;
        typ = tM ;
        skinnyTyp = tM' ;
        optName = p ;
        expected = e ;
        tries = t ;
        instMVars = xs } in
    f sgnQ;
    Options.chatter := bchatter;
   Hashtbl.clear types


end


module Printer = struct

  module P = Pretty.Int.DefaultPrinter
  open Index

  let dctxToString cPsi =
    P.dctxToString LF.Empty cPsi

  let typToString cPsi sM =
    P.typToString LF.Empty cPsi sM

  let normalToString cPsi sM =
    P.normalToString LF.Empty cPsi sM

  let declToString cPsi (tD, s) = match tD with
    | LF.TypDeclOpt x ->
      Id.string_of_name x ^ ":_"
    | LF.TypDecl (x, tM) ->
      Id.string_of_name x ^ ":" ^ typToString cPsi (tM, s)

  (* goalToString Psi (g, s) = string
     Invariants:
       Psi |- s : Phi
       Phi |- g : goal
       Psi |- g[s] : goal

     Effects:
       None.
  *)
  let rec goalToString cPsi (g, s) = match g with
    | Atom (tA) ->
      typToString cPsi (tA, s)
    | Impl ((r, tD), g') -> sprintf "%s -> %s"
      (resToString cPsi (r, s))
      (goalToString (LF.DDec (cPsi, S.decSub tD s)) (g', S.dot1 s))
    | All (tD, g') -> sprintf "[∀%s. %s]"
      (declToString cPsi (tD, s))
      (goalToString (LF.DDec (cPsi, S.decSub tD s)) (g', S.dot1 s))

  (* resToString cPsi (r, s) = string
     Invariants:
       Psi |- s: Phi
       Phi |- r : res
       Psi |- r[s] : res

     Effects:
       None.
  *)
  and resToString cPsi (r, s) = match r with
    | Head (tH) ->
      typToString cPsi (tH, s)
    | And (g, r') -> sprintf "%s -> %s"
      (goalToString cPsi (g, s)) (resToString cPsi (r', s))
    | Exists (LF.TypDecl (_, tM) as tD, r') ->
      let tM' = Convert.etaExpand cPsi (tM, s)
      in sprintf "[∃%s. %s]"
      (declToString cPsi (tD, s))
      (resToString cPsi (r', LF.Dot (LF.Obj tM', s)))

  let rec subGoalsToString cD (cG, s) = match cG with
    | True -> ""
    | Conjunct (cG', g) -> sprintf "  <- %s\n%s"
      (goalToString cD (g, s)) (subGoalsToString cD (cG', s))

  (* sgnClauseToString (c, sCl) = string
     String representation of signature clause.
  *)
  and sgnClauseToString (cidTerm, sCl) =
    sprintf "%s: %s\n%s"
      (Id.string_of_name (termName cidTerm))
      (typToString sCl.eVars (sCl.tHead, S.id))
      (subGoalsToString sCl.eVars (sCl.subGoals, S.id))

  let boundToString b = match b with
    | Some i -> string_of_int i
    | None -> "*"

  let sgnQueryToString q =
    sprintf "%%query %s %s\n\n%s"
      (boundToString q.expected)
      (boundToString q.tries)
      (typToString LF.Null (q.typ, S.id))

  (* instToString xs = string
     Return string representation of existential variable
     instantiations in the query.
  *)
  let rec instToString xs = match xs with
    | ((x, tM) :: []) -> sprintf "%s = %s."
      (Id.string_of_name x)
      (normalToString LF.Null (tM, S.id))
    | ((x, tM) :: ys) -> sprintf "%s = %s;\n%s"
      (Id.string_of_name x)
      (normalToString LF.Null (tM, S.id))
      (instToString ys)
    | [] -> "Empty substitution."

  let printQuery q =
    printf "%s.\n\n" (sgnQueryToString q)

  let printSignature () =
    iterAllSClauses (fun w -> printf "%s\n" (sgnClauseToString w))

end


module Solver = struct

  module U = Unify.StdTrail
  module C = Convert
  module P = Printer
  module I = Index

  (* Dynamic Assumptions *)
  type dPool =                           (* dP ::=                  *)
    | Empty                              (*      | Empty            *)
    | DynCl of (dPool * (clause * int))  (*      | (dP', (dCl, k))  *)

  (* unify Psi (A, s) (B, s') sc = ()
     Invariants:
       sc : unit -> unit

     Effects:
       Instatiation of MVars in s and s'.
       Any effect of (sc ()).
  *)
  let unify cPsi sA sB sc =
    U.unifyTyp LF.Empty cPsi sA sB ; sc ()

  (* trail f = ()
     Trail a function. If an exception is raised, unwind the trail and
     propagate the exception.
  *)
  let trail f =
    let () = U.mark () in
    try f () ; U.unwind () with e -> (U.unwind (); raise e)

  (* eqHead A dCl = bool
     Compare the cid_typ's of A and the head of dCl.
  *)
  let eqHead tM dCl = match (tM, dCl.tHead) with
    | (LF.Atom (_, i, _), LF.Atom (_, j, _)) ->
      i = j
    | _ -> false

  (* cidFromAtom A = cid_typ *)
  let cidFromAtom tM = match tM with
    | LF.Atom (_, i, _) -> i
    | _ -> invalid_arg
      "Logic.Solver.cidFromAtom: Match failure against LF.Atom (_,_,_)."

  (* shiftSub k = ^k
     Invariants:
       Psi, x1:_, x2:_, ... xk:_ |- ^k : Psi
  *)
  let shiftSub k = LF.Shift k

  (* gSolve dPool (Psi, k) (g, s) sc = ()
     Invariants:
       dPool ~ Psi
       k = |Psi|
       Psi |- s : Phi
       Phi |- g : Goal
       sc : proof -> unit
       If G |- M : g[s], then (sc M) is evaluated.

     Effects:
       Instantiation of MVars in s and dPool.
       Any effect (sc M) might have.

     Comments:
       In the arguments to 'sc', 'u' refers to the universal
       context and 't' refers to a proof term.
  *)
  let rec gSolve dPool (cPsi, k) (g, s) sc = match g with
    | Atom (tA) ->
      matchAtom dPool (cPsi, k) (tA, s) sc
    | Impl ((r, (LF.TypDecl (x, _) as tD)), g') ->
      let dPool' = DynCl (dPool, (C.resToClause (r, s), k)) in
      gSolve dPool' (LF.DDec (cPsi, S.decSub tD s), k + 1)
        (g', S.dot1 s) (fun (u, tM) -> sc (u, LF.Lam (Syntax.Loc.ghost, x, tM)))
    | All (LF.TypDecl (x, _) as tD, g') ->
      gSolve dPool (LF.DDec (cPsi, S.decSub tD s), k + 1)
        (g', S.dot1 s) (fun (u, tM) -> sc (u, LF.Lam (Syntax.Loc.ghost, x, tM)))

  (* matchAtom dPool (Psi, k) (A, s) sc = ()
     Invariants:
       dPool ~ Psi, k = |Psi|
       Psi |- s : Phi
       Phi |- A : Atom
       sc : proof -> unit
       If Psi |- M : A[s], then (sc M) is evaluated.

     Effects:
       Instatiation of MVars in s and dPool.
       Any effect (sc M) might have.
  *)
  and matchAtom dPool (cPsi, k) (tA, s) sc =

    (* matchDProg dPool = ()
       Try all the dynamic clauses in dPool starting with the most
       recent one. If dPool is empty, try the signature.
    *)
    let rec matchDProg dPool = match dPool with
      | DynCl (dPool', (dCl, k')) ->
        if (eqHead tA dCl) then
          let (s', fS) =
            C.dctxToSub cPsi (dCl.eVars, shiftSub (k - k'))
              (fun tS -> tS) in
          (* Trail to undo MVar instantiations. *)
          (try trail (fun () -> unify cPsi (tA, s) (dCl.tHead, s')
            (fun () -> solveSubGoals dPool (cPsi, k) (dCl.subGoals, s')
              (fun (u, tS) ->
                sc (u, LF.Root (Syntax.Loc.ghost, LF.BVar (k - k'), fS (spineFromRevList tS))))))
           with U.Failure _ -> ()) ; matchDProg dPool'
        else matchDProg dPool'
      | Empty ->
        matchSig (cidFromAtom tA)

    (* matchSig c = ()
       Try all the clauses in the static signature with head matching
       type constant c.
    *)
    and matchSig cidTyp =
      I.iterSClauses (fun w -> matchSgnClause w sc) cidTyp

    (* matchSgnClause (c, sCl) sc = ()
       Try to unify the head of sCl with A[s]. If unification succeeds,
       attempt to solve the subgoals of sCl.
    *)
    and matchSgnClause (cidTerm, sCl) sc =
      let (s', fS) =
        C.dctxToSub cPsi (sCl.eVars, shiftSub (Context.dctxLength cPsi))
          (fun tS -> tS) in
      (* Trail to undo MVar instantiations. *)
      try trail (fun () -> unify cPsi (tA, s) (sCl.tHead, s')
        (fun () -> solveSubGoals dPool (cPsi, k) (sCl.subGoals, s')
          (fun (u, tS) -> sc (u, LF.Root (Syntax.Loc.ghost, LF.Const (cidTerm), fS (spineFromRevList tS))))))
      with U.Failure _ -> ()

    in matchDProg dPool
(* spineFromRevList : LF.normal list -> LF.spine
  build an LF.spine out of a list of LF.normal, reversing the order of the elements*)
  and spineFromRevList lS =
      List.fold_left (fun tSc tMc -> LF.App(tMc, tSc)) LF.Nil lS

  (* solveSubGoals dPool (Psi, k) (G, s) sc = ()
     Invariants:
       dPool ~ Psi
       G = (G', g) | T
       Psi |- s : Phi
       Phi |- g : goal
       sc : (dctx * spine) -> unit
       If Psi |- M : g[s], then (sc App (M, S)) is evaluated.
       If Psi |- G = T, then (sc Nil) is evaluated, ending the
       spine of proof-terms for the goals in G.

     Effects:
       Instatiation of MVars in dPool and g[s].
       Any effect of (sc S).
  *)
  and solveSubGoals dPool (cPsi, k) (cG, s) sc = match cG with
    | True -> sc (cPsi, [])
    | Conjunct (cG', g) ->
      gSolve dPool (cPsi, k) (g, s)
        (fun (u, tM) -> solveSubGoals dPool (cPsi, k) (cG', s)
          (fun (v, tS) -> sc (v, tM::tS)))

  (* solve (g, s) sc = ()
     Invariants:
       Empty |- g[s] : goal
       sc : dctx * normal -> unit

     Effects:
       Same as gSolve.
  *)
  let solve (g, s) sc =
    gSolve Empty (LF.Null, 0) (g, s) sc

end


module Frontend = struct

  module P = Printer
  open Index

  exception Done                        (* Solved query successfully. *)
  exception AbortQuery of string        (* Abort solving the query.   *)

  (* 
   * exceeds B1 B2 = b
   * True if B1 = * or B1 >= B2.
   *)
  let exceeds (x:bound) (y:bound) : bool =
    match x, y with
      | Some i, Some j -> i >= j
      | Some i,   None -> false
      |   None,      _ -> true

  (* 
   * boundEq B1 B2 = b
   * Equality function for bounds.
   *)
  let boundEq (x:bound) (y:bound) : bool =
    match x, y with
      | Some i, Some j -> i = j
      |   None,   None -> true
      |      _,      _ -> false

  (*
   * lowerBound B1 B2 = min (B1, B2)
   *)
  let lowerBound (x:bound) (y:bound) : bound =
    match (x, y) with
      | Some i, Some j -> Some (min i j)
      |      x,   None -> x
      |   None,      y -> y

  (*
   * Abort query.
   *)
  let abort str = raise (AbortQuery str)

  (*
   * checkSolutions e t s = ()
   *)
  let checkSolutions (expected:bound) (tries:bound) (solutions:int) =
    let lb = lowerBound expected tries in
    if lb <> None && not (boundEq lb (Some solutions)) then
      abort ("Query error: Wrong number of solutions -- "
	     ^ "expected " ^ (P.boundToString expected) ^ " in "
	     ^ (P.boundToString tries) ^ " tries, but found "
	     ^ (string_of_int solutions))

  (*
   * Asks the user if he wants more solutions or not.
   *)
  let moreSolutions () : bool =
    printf "More? (y/N/q) ";
    match (read_line ()) with
      | "y" | "Y" | ";" -> true
      | "q" | "Q"       -> abort "Query error -- explicit quit."
      | _               -> false

  (*
   * solve q = ()
   *)
  let solve (sgnQuery : Index.sgnQuery) =

    (* Keep track of the number of solutions found. *)
    let solutions = ref 0 in

    (* Type checking function. *)
    let check (cPsi:LF.dctx) (tM:LF.normal) (s:LF.sub) =
	Check.LF.check LF.Empty cPsi (tM, S.id) (sgnQuery.skinnyTyp, s)
    in

    (*
     * Initial success continuation.
     * cf article for design description.
     *)
    let scInit ((cPsi:LF.dctx), (tM:LF.normal)) = (*TODO: curryfy this*)
      incr solutions;
      
      (* Rebuild the substitution and type check the proof term. *)
      if !Options.checkProofs then
        check cPsi tM (Convert.solToSub sgnQuery.instMVars); (* !querySub *)

      (* Print MVar instantiations. *)
      if !Options.chatter >= 3 then
        (
          printf "---------- Solution %d ----------\n[%s]\n%s\n"
            !solutions (P.dctxToString cPsi)
            (P.instToString sgnQuery.instMVars) ;
          (* Print proof term. *)
          (match sgnQuery.optName with
            | Some n ->
              printf "%s\n" (P.instToString [(n, tM)])
            | None -> ()) ;
          printf "\n"
	);

      (* Interactive. *)
      if !Options.askSolution then
        if not (moreSolutions ()) then
	  raise Done;

      (* Stop when no. of solutions exceeds tries. *)
      if exceeds (Some !solutions) sgnQuery.tries then
        raise Done;
    in
    (* End of scInit definition*)

    if not (boundEq sgnQuery.tries (Some 0)) then
      (
        if !Options.chatter >= 1 then
          P.printQuery sgnQuery;

        try
	  
          Solver.solve sgnQuery.query scInit ;
          (* Check solution bounds. *)
          checkSolutions sgnQuery.expected sgnQuery.tries !solutions
        with
          | Done -> printf "Done.\n"
          | AbortQuery (s) -> printf "%s\n" s
          | _ -> ()
      )

    else if !Options.chatter >= 2 then
      printf "Skipping query -- bound for tries = 0.\n"

end



(* val storeQuery : Id.name option -> LF.typ * int -> bound -> bound -> unit
 *
 * Stores the query for a future runLogic run.
 *)
let storeQuery p (tA, i) expected tries =
  Index.storeQuery (p, (tA, i), expected, tries)


(*
 * If !enabledLogic, run the logic programming engine. Otherwise do nothing.
 *)
let runLogic () =
  if !Options.enableLogic then
    (
      (* Transform LF signature into clauses. *)
      Index.robStore () ;
      
      (* Optional: Print signature clauses. *)
      if !Options.chatter >= 4 then
        Printer.printSignature ();

      (* Solve! *)
      Index.iterQueries Frontend.solve ;

      (* Clear the local storage.  *)
      Index.clearIndex ()
    )


(* val runLogicOn : Id.name option -> LF.typ * int -> bound -> bound -> unit *)
let runLogicOn p (tA, i) expected tries  =
  Index.singleQuery (p, (tA, i), expected, tries) Frontend.solve
