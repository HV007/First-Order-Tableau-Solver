datatype term = VAR of string
            | FUN of string * term list
            | CONST of string (* for generated constants only *)
datatype Pred = FF (* special constant for closing a tableau path *)
            | ATOM of string * term list
            | NOT of Pred
            | AND of Pred * Pred
            | OR of Pred * Pred
            | COND of Pred * Pred
            | BIC of Pred * Pred
            | ITE of Pred * Pred * Pred
            | ALL of term * Pred
            | EX of term * Pred
datatype Argument = HENCE of Pred list * Pred
exception NotVAR (* Binding term in a quantified formula is not a variable *)
exception NotWFT (* term is not well-formed *)
exception NotWFP (* predicate is not well-formed *)
exception NotWFA (* argument is not well-formed *)
exception NotClosed (* a formula is not closed *)
exception EnvironmentError
exception Unexpectedpred

val freshConstants = [CONST "A", CONST "B", CONST "C", CONST "D", CONST "E", CONST "F", CONST "G", CONST "H", CONST "I", CONST "J", CONST "K", CONST "L", CONST "M", CONST "N", CONST "O", CONST "P", CONST "Q", CONST "R", CONST "S", CONST "T", CONST "U", CONST "V", CONST "W", CONST "X", CONST "Y", CONST "Z"]

fun delete (item, list) = List.filter(fn x => x <> item) list

fun reverse xs =
let
  fun revhelp [] ys = ys
    | revhelp (x :: xs) ys = revhelp xs (x :: ys)
in
  revhelp xs []
end

fun envAdd (var, v, env) = (var, v) :: env
and envLookup (var, env) = case List.find(fn (x, _) => x = var) (reverse env) of
    SOME (x, v)   => v
|   NONE => raise EnvironmentError

fun boolEnvAdd(pred, env) = pred :: env
and boolEnvLookup(pred, env) = case List.find(fn (x) => x = pred)  env of
    SOME (x)   => true
|   NONE => false

fun substitutePred (pred, t1, t2) = case pred of
    ATOM (p, terms) => ATOM (p, List.map (fn term => substituteTerm(term, t1, t2)) terms)
|   NOT pred => NOT (substitutePred (pred, t1, t2))
|   AND (pred1, pred2) => AND (substitutePred(pred1, t1, t2), substitutePred(pred2, t1, t2))
|   OR (pred1, pred2) => OR (substitutePred(pred1, t1, t2), substitutePred(pred2, t1, t2))
|   COND (pred1, pred2) => COND (substitutePred(pred1, t1, t2), substitutePred(pred2, t1, t2))
|   BIC (pred1, pred2) => BIC (substitutePred(pred1, t1, t2), substitutePred(pred2, t1, t2))
|   ITE (pred1, pred2, pred3) => ITE (substitutePred(pred1, t1, t2), substitutePred(pred2, t1, t2), substitutePred(pred3, t1, t2))
|   ALL (t, pred) => if t <> t1 then ALL (t, substitutePred(pred, t1, t2)) else ALL (t, pred)
|   EX (t, pred) => if t <> t1 then EX (t, substitutePred(pred, t1, t2)) else EX (t, pred)
and substituteTerm (term, t1, t2) = case term of
    VAR x => if t1 = VAR x then t2 else VAR x
|   FUN (f, terms) => FUN (f, List.map (fn term => substituteTerm(term, t1, t2)) terms)
|   CONST a => CONST a

fun checkReducedList ([]) = ATOM ("NULL", [])
|   checkReducedList (predHead :: predListTail) = 
case predHead of
    ATOM (p, terms) => checkReducedList(predListTail)
|   NOT (ATOM (p, terms)) => checkReducedList(predListTail)
|   _ => predHead

fun checkPathClosed ([], env) = false
|   checkPathClosed (predHead :: predListTail, env) = case predHead of
    ATOM (p, terms) => if boolEnvLookup (NOT (ATOM (p, terms)), env) then true else checkPathClosed(predListTail, boolEnvAdd(ATOM (p, terms), env))
|   NOT (ATOM (p, terms)) => if boolEnvLookup (ATOM (p, terms), env) then true else checkPathClosed(predListTail, boolEnvAdd(NOT (ATOM (p, terms)), env))
|   _ => checkPathClosed(predListTail, env)

fun checkTautology ([], valuation) = true
|   checkTautology (predList, valuation) = 
let
    val reduct = checkReducedList(predList)
    val tau = delete(reduct, predList)
in
    if checkPathClosed(predList, []) then true else case reduct of
        ATOM (p, terms) => if p = "NULL" then false else raise Unexpectedpred
    |   NOT (ATOM (p, terms)) => raise Unexpectedpred
    |   NOT (NOT pred) => checkTautology(tau @ [pred], valuation)
    |   AND (pred1, pred2) => checkTautology(tau @ [pred1, pred2], valuation)
    |   NOT (AND (pred1, pred2)) => checkTautology(tau @ [NOT pred1], valuation) andalso checkTautology(tau @ [NOT pred2], valuation)
    |   OR (pred1, pred2) => checkTautology(tau @ [pred1], valuation) andalso checkTautology(tau @ [pred2], valuation)
    |   NOT (OR (pred1, pred2)) => checkTautology(tau @ [NOT pred1, NOT pred2], valuation)
    |   COND (pred1, pred2) => checkTautology(tau @ [NOT pred1], valuation) andalso checkTautology(tau @ [pred2], valuation)
    |   NOT (COND (pred1, pred2)) => checkTautology(tau @ [pred1, NOT pred2], valuation)
    |   BIC (pred1, pred2) => checkTautology(tau @ [AND (pred1, pred2)], valuation) andalso checkTautology(tau @ [AND (NOT pred1, NOT pred2)], valuation)
    |   NOT (BIC (pred1, pred2)) => checkTautology(tau @ [AND (pred1, NOT pred2)], valuation) andalso checkTautology(tau @ [AND (NOT pred1, pred2)], valuation)
    |   ITE (pred1, pred2, pred3) => checkTautology(tau @ [OR (AND (pred1, pred2), AND (NOT pred1, pred3))], valuation)
    |   NOT (ITE (pred1, pred2, pred3)) => checkTautology(tau @ [AND (OR (NOT pred1, NOT pred2), OR (pred1, NOT pred3))], valuation)
    |   ALL (t, pred) => checkTautology(tau @ [substitutePred(pred, t, envLookup(t, valuation))], valuation)
    |   NOT (ALL (t, pred)) => checkTautology(tau @ [substitutePred(NOT pred, t, envLookup(t, valuation))], valuation)
    |   EX (t, pred) => checkTautology(tau @ [substitutePred(pred, t, envLookup(t, valuation))], valuation)
    |   NOT (EX (t, pred)) => checkTautology(tau @ [substitutePred(NOT pred, t, envLookup(t, valuation))], valuation)
end

fun getConstantsPred(pred) = case pred of
    ATOM (p, terms) => List.foldl (fn (x, y) => x @ y) [] (List.map (fn term => getConstantsTerm term) terms)
|   NOT pred => getConstantsPred(pred)
|   AND (pred1, pred2) => getConstantsPred(pred1) @ getConstantsPred(pred2)
|   OR (pred1, pred2) => getConstantsPred(pred1) @ getConstantsPred(pred2)
|   COND (pred1, pred2) => getConstantsPred(pred1) @ getConstantsPred(pred2)
|   BIC (pred1, pred2) => getConstantsPred(pred1) @ getConstantsPred(pred2)
|   ITE (pred1, pred2, pred3) => getConstantsPred(pred1) @ getConstantsPred(pred2) @ getConstantsPred(pred3)
|   ALL (t, pred) => (case t of
        VAR x => getConstantsPred(pred)
    |   _ => raise NotVAR)
|   EX (t, pred) => (case t of
        VAR x => getConstantsPred(pred)
    |   _ => raise NotVAR)
|   _ => raise NotWFA
and getConstantsTerm(term: term) = case term of
    VAR x => []
|   FUN (f, []) => [FUN (f, [])]
|   FUN (f, terms) => List.foldl (fn (x, y) => x @ y) [] (List.map (fn term => getConstantsTerm term) terms)
|   CONST a => [CONST a]

fun getVariables(pred) = case pred of
    ATOM (p, terms) => []
|   NOT (ATOM (p, terms)) => []
|   NOT (NOT pred) => getVariables(pred)
|   AND (pred1, pred2) => getVariables(pred1) @ getVariables(pred2)
|   NOT (AND (pred1, pred2)) => getVariables(pred1) @ getVariables(pred2)
|   OR (pred1, pred2) => getVariables(pred1) @ getVariables(pred2)
|   NOT (OR (pred1, pred2)) => getVariables(pred1) @ getVariables(pred2)
|   COND (pred1, pred2) => getVariables(pred1) @ getVariables(pred2)
|   NOT (COND (pred1, pred2)) => getVariables(pred1) @ getVariables(pred2)
|   BIC (pred1, pred2) => getVariables(pred1) @ getVariables(pred2)
|   NOT (BIC (pred1, pred2)) => getVariables(pred1) @ getVariables(pred2)
|   ITE (pred1, pred2, pred3) => getVariables(pred1) @ getVariables(pred2) @ getVariables(pred3)
|   NOT (ITE (pred1, pred2, pred3)) => getVariables(pred1) @ getVariables(pred2) @ getVariables(pred3)
|   ALL (t, pred) => [t] @ getVariables(pred)
|   NOT (ALL (t, pred)) => getVariables(pred)
|   EX (t, pred) => getVariables(pred)
|   NOT (EX (t, pred)) => [t] @ getVariables(pred)

fun getExistentialVariables(pred) = case pred of
    ATOM (p, terms) => []
|   NOT (ATOM (p, terms)) => []
|   NOT (NOT pred) => getExistentialVariables(pred)
|   AND (pred1, pred2) => getExistentialVariables(pred1) @ getExistentialVariables(pred2)
|   NOT (AND (pred1, pred2)) => getExistentialVariables(pred1) @ getExistentialVariables(pred2)
|   OR (pred1, pred2) => getExistentialVariables(pred1) @ getExistentialVariables(pred2)
|   NOT (OR (pred1, pred2)) => getExistentialVariables(pred1) @ getExistentialVariables(pred2)
|   COND (pred1, pred2) => getExistentialVariables(pred1) @ getExistentialVariables(pred2)
|   NOT (COND (pred1, pred2)) => getExistentialVariables(pred1) @ getExistentialVariables(pred2)
|   BIC (pred1, pred2) => getExistentialVariables(pred1) @ getExistentialVariables(pred2)
|   NOT (BIC (pred1, pred2)) => getExistentialVariables(pred1) @ getExistentialVariables(pred2)
|   ITE (pred1, pred2, pred3) => getExistentialVariables(pred1) @ getExistentialVariables(pred2) @ getExistentialVariables(pred3)
|   NOT (ITE (pred1, pred2, pred3)) => getExistentialVariables(pred1) @ getExistentialVariables(pred2) @ getExistentialVariables(pred3)
|   ALL (t, pred) => getExistentialVariables(pred)
|   NOT (ALL (t, pred)) => [t] @ getExistentialVariables(pred)
|   EX (t, pred) => [t] @ getExistentialVariables(pred)
|   NOT (EX (t, pred)) => getExistentialVariables(pred)

fun getConstructorsPred(pred) = case pred of
    ATOM (p, terms) => List.foldl (fn (x, y) => x @ y) [] (List.map (fn term => getConstructorsTerm term) terms)
|   NOT pred => getConstructorsPred(pred)
|   AND (pred1, pred2) => getConstructorsPred(pred1) @ getConstructorsPred(pred2)
|   OR (pred1, pred2) => getConstructorsPred(pred1) @ getConstructorsPred(pred2)
|   COND (pred1, pred2) => getConstructorsPred(pred1) @ getConstructorsPred(pred2)
|   BIC (pred1, pred2) => getConstructorsPred(pred1) @ getConstructorsPred(pred2)
|   ITE (pred1, pred2, pred3) => getConstructorsPred(pred1) @ getConstructorsPred(pred2) @ getConstructorsPred(pred3)
|   ALL (t, pred) => getConstructorsPred(pred)
|   EX (t, pred) => getConstructorsPred(pred)
and getConstructorsTerm(term: term) = case term of
    VAR x => []
|   FUN (f, []) => []
|   FUN (f, terms) => List.foldl (fn (x, y) => x @ y) [FUN (f, (List.map (fn term => CONST "DUMMY") terms))] (List.map (fn term => getConstructorsTerm term) terms)
|   CONST a => []

fun verifyConstructors([]) = ()
|   verifyConstructors(FUN (name, terms) :: constructors) = (checkConstructor(name, length terms, constructors); verifyConstructors(constructors))
|   verifyConstructors(_ :: constructors) = raise NotWFA
and checkConstructor(name, arity, []) = ()
|   checkConstructor(name, arity, (FUN (name', terms) :: constructors)) = ((if (name = name' andalso length terms <> arity) then (raise NotWFT) else ()); checkConstructor(name, arity, constructors))
|   checkConstructor(name, arity, _ :: constructors) = raise NotWFA

fun getPredicates(pred) = case pred of
    ATOM (p, terms) => [ATOM (p, terms)]
|   NOT pred => getPredicates(pred)
|   AND (pred1, pred2) => getPredicates(pred1) @ getPredicates(pred2)
|   OR (pred1, pred2) => getPredicates(pred1) @ getPredicates(pred2)
|   COND (pred1, pred2) => getPredicates(pred1) @ getPredicates(pred2)
|   BIC (pred1, pred2) => getPredicates(pred1) @ getPredicates(pred2)
|   ITE (pred1, pred2, pred3) => getPredicates(pred1) @ getPredicates(pred2) @ getPredicates(pred3)
|   ALL (t, pred) => getPredicates(pred)
|   EX (t, pred) => getPredicates(pred)

fun verifyPredicates([]) = ()
|   verifyPredicates(pred :: predicates) = let val ATOM (name, terms) = pred in (checkPredicate(name, length terms, predicates); verifyPredicates(predicates)) end
and checkPredicate(name, arity, []) = ()
|   checkPredicate(name, arity, (pred :: predicates)) = let val ATOM (name', terms) = pred in ((if (name = name' andalso length terms <> arity) then (raise NotWFP) else ()); checkPredicate(name, arity, predicates)) end

fun checkClosedPred(pred, variables) = case pred of
    ATOM (p, terms) => List.map (fn term => checkClosedTerm(term, variables)) terms
|   NOT pred => checkClosedPred(pred, variables)
|   AND (pred1, pred2) => checkClosedPred(pred1, variables) @ checkClosedPred(pred2, variables)
|   OR (pred1, pred2) => checkClosedPred(pred1, variables) @ checkClosedPred(pred2, variables)
|   COND (pred1, pred2) => checkClosedPred(pred1, variables) @ checkClosedPred(pred2, variables)
|   BIC (pred1, pred2) => checkClosedPred(pred1, variables) @ checkClosedPred(pred2, variables)
|   ITE (pred1, pred2, pred3) => checkClosedPred(pred1, variables) @ checkClosedPred(pred2, variables) @ checkClosedPred(pred3, variables)
|   ALL (t, pred) => let val VAR x = t in checkClosedPred(pred, x :: variables) end
|   EX (t, pred) => let val VAR x = t in checkClosedPred(pred, x :: variables) end
and checkClosedTerm(term, variables) = case term of
    VAR x => if (List.exists (fn variable => variable = x) variables) then () else (raise NotClosed)
|   FUN (f, terms) => ()
|   CONST a => ()

fun generateTerms(constructors, subterms) = 
    List.foldl (fn (x, y) => x @ y) [] (List.map (fn constructor => (
        let val FUN (name, terms) = constructor in generateTermsGivenConstructor (name, subterms, length terms) end
    )) constructors)
and generateArguments(terms, arity) = if arity = 0 then [[]] else if arity = 1 then List.map (fn term => [term]) terms else (
    let val subterms = generateArguments (terms, arity - 1) in
        List.foldl (fn (x, y) => x @ y) [] (List.map (fn term => (List.map (fn subterm => ([term] @ subterm)) subterms)) terms)
    end
)
and generateTermsGivenConstructor(constructorName, terms, arity) = List.map (fn argument => FUN (constructorName, argument)) (generateArguments (terms, arity))

fun generateEnvironments(variables, valueList) = List.map (fn values => generateEnvironment(variables, values)) valueList
and generateEnvironment([], []) = []
|   generateEnvironment(var :: variables, value :: values) = envAdd(var, value, generateEnvironment(variables, values))

fun appendEnvironments (variables, constants, envList) = List.map (fn env => appendEnvironment(variables, constants, env)) envList
and appendEnvironment ([], constants, env) = env
|   appendEnvironment (var :: variables, const :: constants, env) = appendEnvironment(variables, constants, envAdd(var, const, env))

fun bigAnd([pred]) = pred
|   bigAnd(pred :: predList) = AND (pred, bigAnd predList)

fun isolate [] = []
| isolate (l as x::xs) =
    let fun remove (x,[]) = []
        |   remove (x,l as y::ys) = if x = y then remove(x,ys) else y::remove(x,ys)
    in
        x::isolate(remove(x,xs))
    end

fun getPrefix(L, 0) = []
|   getPrefix(x :: L, n) = x :: getPrefix(L, n - 1)

fun checkEnvironmentList([], predList) = false
|   checkEnvironmentList(env :: envList, predList) = if checkTautology(predList, env) then true else checkEnvironmentList(envList, predList)
and getValidEnvironmentFromList([], predList) = []
|   getValidEnvironmentFromList(env :: envList, predList) = if checkTautology(predList, env) then env else getValidEnvironmentFromList(envList, predList)

fun getValidEnvironment(predList, freshConstants, terms, depth) =
let
    val pred = bigAnd predList
    val existentialVariables = isolate (getExistentialVariables pred)
    val variables = isolate (getVariables pred)
    val constants = isolate (getConstantsPred pred)
    val constructors = isolate (getConstructorsPred pred)
    val valueList = generateArguments (terms, length variables)
    val envList = appendEnvironments (existentialVariables, freshConstants, generateEnvironments (variables, valueList))
in
    if checkEnvironmentList (envList, predList) then getValidEnvironmentFromList (envList, predList)
    else getValidEnvironment (predList, freshConstants, generateTerms (constructors, terms), depth + 1)
end

val idx = ref 0
val nodes = ref [] : (Pred * int) list ref
val treeEdges = ref [] : (int * int) list ref
val backEdges = ref [] : (int * int) list ref
val redEdges = ref [] : (int * int) list ref

fun addInitialNodes([]) = ()
|   addInitialNodes(pred :: predList) = (nodes := !nodes @ [(pred, !idx)]; if !idx = 0 then (idx := !idx + 1; addInitialNodes(predList)) else (treeEdges := !treeEdges @ [(!idx - 1, !idx)]; idx := !idx + 1; addInitialNodes(predList)))

fun addRedEdge([], env) = ()
|   addRedEdge(pred :: predList, env) = case pred of
    ATOM (p, terms) => if boolEnvLookup (NOT (ATOM (p, terms)), env) then (redEdges := !redEdges @ [(envLookup (ATOM (p, terms), !nodes), envLookup (NOT (ATOM (p, terms)), !nodes))]) else addRedEdge(predList, boolEnvAdd(ATOM (p, terms), env))
|   NOT (ATOM (p, terms)) => if boolEnvLookup (ATOM (p, terms), env) then (redEdges := !redEdges @ [(envLookup (ATOM (p, terms), !nodes), envLookup (NOT (ATOM (p, terms)), !nodes))]) else addRedEdge(predList, boolEnvAdd(NOT (ATOM (p, terms)), env))
|   _ => addRedEdge(predList, env)

fun addGeneratedNodes([], env, root) = ()
|   addGeneratedNodes(predList, env, root) =
let
    val reduct = checkReducedList(predList)
    val tau = delete(reduct, predList)
in
    if checkPathClosed(predList, []) then (nodes := !nodes @ [(FF, !idx)]; treeEdges := !treeEdges @ [(root, !idx)]; idx := !idx + 1; addRedEdge(predList, [])) else case reduct of
        ATOM (p, terms) => raise Unexpectedpred
    |   NOT (ATOM (p, terms)) => raise Unexpectedpred
    |   NOT (NOT pred) => (nodes := !nodes @ [(pred, !idx)]; treeEdges := !treeEdges @ [(root, !idx)]; backEdges := !backEdges @ [(!idx, envLookup (NOT (NOT pred), !nodes))]; idx := !idx + 1; addGeneratedNodes(tau @ [pred], env, !idx - 1))
    |   AND (pred1, pred2) => (nodes := !nodes @ [(pred1, !idx)]; treeEdges := !treeEdges @ [(root, !idx)]; backEdges := !backEdges @ [(!idx, envLookup (AND (pred1, pred2), !nodes))]; idx := !idx + 1;
        nodes := !nodes @ [(pred2, !idx)]; treeEdges := !treeEdges @ [(!idx - 1, !idx)]; backEdges := !backEdges @ [(!idx, envLookup (AND (pred1, pred2), !nodes))]; idx := !idx + 1;
        addGeneratedNodes(tau @ [pred1, pred2], env, !idx - 1))
    |   NOT (AND (pred1, pred2)) => (nodes := !nodes @ [(NOT pred1, !idx)]; treeEdges := !treeEdges @ [(root, !idx)]; backEdges := !backEdges @ [(!idx, envLookup (NOT (AND (pred1, pred2)), !nodes))]; idx := !idx + 1; addGeneratedNodes(tau @ [NOT pred1], env, !idx - 1);
        nodes := !nodes @ [(NOT pred2, !idx)]; treeEdges := !treeEdges @ [(root, !idx)]; backEdges := !backEdges @ [(!idx, envLookup (NOT (AND (pred1, pred2)), !nodes))]; idx := !idx + 1; addGeneratedNodes(tau @ [NOT pred2], env, !idx - 1))
    |   OR (pred1, pred2) => (nodes := !nodes @ [(pred1, !idx)]; treeEdges := !treeEdges @ [(root, !idx)]; backEdges := !backEdges @ [(!idx, envLookup (OR (pred1, pred2), !nodes))]; idx := !idx + 1; addGeneratedNodes(tau @ [pred1], env, !idx - 1);
        nodes := !nodes @ [(pred2, !idx)]; treeEdges := !treeEdges @ [(root, !idx)]; backEdges := !backEdges @ [(!idx, envLookup (OR (pred1, pred2), !nodes))]; idx := !idx + 1; addGeneratedNodes(tau @ [pred2], env, !idx - 1))
    |   NOT (OR (pred1, pred2)) => (nodes := !nodes @ [(NOT pred1, !idx)]; treeEdges := !treeEdges @ [(root, !idx)]; backEdges := !backEdges @ [(!idx, envLookup (NOT (OR (pred1, pred2)), !nodes))]; idx := !idx + 1;
        nodes := !nodes @ [(NOT pred2, !idx)]; treeEdges := !treeEdges @ [(!idx - 1, !idx)]; backEdges := !backEdges @ [(!idx, envLookup (NOT (OR (pred1, pred2)), !nodes))]; idx := !idx + 1;
        addGeneratedNodes(tau @ [NOT pred1, NOT pred2], env, !idx - 1))
    |   COND (pred1, pred2) => (nodes := !nodes @ [(NOT pred1, !idx)]; treeEdges := !treeEdges @ [(root, !idx)]; backEdges := !backEdges @ [(!idx, envLookup (COND (pred1, pred2), !nodes))]; idx := !idx + 1; addGeneratedNodes(tau @ [NOT pred1], env, !idx - 1);
        nodes := !nodes @ [(pred2, !idx)]; treeEdges := !treeEdges @ [(root, !idx)]; backEdges := !backEdges @ [(!idx, envLookup (COND (pred1, pred2), !nodes))]; idx := !idx + 1; addGeneratedNodes(tau @ [pred2], env, !idx - 1))
    |   NOT (COND (pred1, pred2)) => (nodes := !nodes @ [(pred1, !idx)]; treeEdges := !treeEdges @ [(root, !idx)]; backEdges := !backEdges @ [(!idx, envLookup (NOT (COND (pred1, pred2)), !nodes))]; idx := !idx + 1;
        nodes := !nodes @ [(NOT pred2, !idx)]; treeEdges := !treeEdges @ [(!idx - 1, !idx)]; backEdges := !backEdges @ [(!idx, envLookup (NOT (COND (pred1, pred2)), !nodes))]; idx := !idx + 1;
        addGeneratedNodes(tau @ [pred1, NOT pred2], env, !idx - 1))
    |   BIC (pred1, pred2) => (nodes := !nodes @ [(AND (pred1, pred2), !idx)]; treeEdges := !treeEdges @ [(root, !idx)]; backEdges := !backEdges @ [(!idx, envLookup (BIC (pred1, pred2), !nodes))]; idx := !idx + 1; addGeneratedNodes(tau @ [AND (pred1, pred2)], env, !idx - 1);
        nodes := !nodes @ [(AND (NOT pred1, NOT pred2), !idx)]; treeEdges := !treeEdges @ [(root, !idx)]; backEdges := !backEdges @ [(!idx, envLookup (BIC (pred1, pred2), !nodes))]; idx := !idx + 1; addGeneratedNodes(tau @ [AND (NOT pred1, NOT pred2)], env, !idx - 1))
    |   NOT (BIC (pred1, pred2)) => (nodes := !nodes @ [(AND (pred1, NOT pred2), !idx)]; treeEdges := !treeEdges @ [(root, !idx)]; backEdges := !backEdges @ [(!idx, envLookup (NOT (BIC (pred1, pred2)), !nodes))]; idx := !idx + 1; addGeneratedNodes(tau @ [AND (pred1, NOT pred2)], env, !idx - 1);
        nodes := !nodes @ [(AND (NOT pred1, pred2), !idx)]; treeEdges := !treeEdges @ [(root, !idx)]; backEdges := !backEdges @ [(!idx, envLookup (NOT (BIC (pred1, pred2)), !nodes))]; idx := !idx + 1; addGeneratedNodes(tau @ [AND (NOT pred1, pred2)], env, !idx - 1))
    |   ITE (pred1, pred2, pred3) => (nodes := !nodes @ [(OR (AND (pred1, pred2), AND (NOT pred1, pred3)), !idx)]; treeEdges := !treeEdges @ [(root, !idx)]; backEdges := !backEdges @ [(!idx, envLookup (ITE (pred1, pred2, pred3), !nodes))]; idx := !idx + 1; addGeneratedNodes(tau @ [OR (AND (pred1, pred2), AND (NOT pred1, pred3))], env, !idx - 1))
    |   NOT (ITE (pred1, pred2, pred3)) => (nodes := !nodes @ [(AND (OR (NOT pred1, NOT pred2), OR (pred1, NOT pred3)), !idx)]; treeEdges := !treeEdges @ [(root, !idx)]; backEdges := !backEdges @ [(!idx, envLookup (NOT (ITE (pred1, pred2, pred3)), !nodes))]; idx := !idx + 1; addGeneratedNodes(tau @ [AND (OR (NOT pred1, NOT pred2), OR (pred1, NOT pred3))], env, !idx - 1))
    |   ALL (t, pred) => (nodes := !nodes @ [(substitutePred(pred, t, envLookup(t, env)), !idx)]; treeEdges := !treeEdges @ [(root, !idx)]; backEdges := !backEdges @ [(!idx, envLookup (ALL (t, pred), !nodes))]; idx := !idx + 1; addGeneratedNodes(tau @ [substitutePred(pred, t, envLookup(t, env))], env, !idx - 1))
    |   NOT (ALL (t, pred)) => (nodes := !nodes @ [(substitutePred(NOT pred, t, envLookup(t, env)), !idx)]; treeEdges := !treeEdges @ [(root, !idx)]; backEdges := !backEdges @ [(!idx, envLookup (NOT (ALL (t, pred)), !nodes))]; idx := !idx + 1; addGeneratedNodes(tau @ [substitutePred(NOT pred, t, envLookup(t, env))], env, !idx - 1))
    |   EX (t, pred) => (nodes := !nodes @ [(substitutePred(pred, t, envLookup(t, env)), !idx)]; treeEdges := !treeEdges @ [(root, !idx)]; backEdges := !backEdges @ [(!idx, envLookup (EX (t, pred), !nodes))]; idx := !idx + 1; addGeneratedNodes(tau @ [substitutePred(pred, t, envLookup(t, env))], env, !idx - 1))
    |   NOT (EX (t, pred)) => (nodes := !nodes @ [(substitutePred(NOT pred, t, envLookup(t, env)), !idx)]; treeEdges := !treeEdges @ [(root, !idx)]; backEdges := !backEdges @ [(!idx, envLookup (NOT (EX (t, pred)), !nodes))]; idx := !idx + 1; addGeneratedNodes(tau @ [substitutePred(NOT pred, t, envLookup(t, env))], env, !idx - 1))
end

fun generateNodes(predList, env) = (addInitialNodes(predList); addGeneratedNodes(predList, env, !idx - 1))

fun stringJoinWithComma([]) = ""
| stringJoinWithComma([s]) = s
| stringJoinWithComma(s :: L) = s ^ ", " ^ stringJoinWithComma(L)

fun predToLatex(pred) = case pred of
    ATOM (p, terms) => if (length terms) = 0 then p else p ^ "(" ^ (stringJoinWithComma (map (fn t => termToLatex t) terms)) ^ ")"
|   NOT pred => "(\\neg " ^ predToLatex(pred) ^ ")"
|   AND (pred1, pred2) => "(" ^ predToLatex(pred1) ^ " \\wedge " ^ predToLatex(pred2) ^ ")"
|   OR (pred1, pred2) => "(" ^ predToLatex(pred1) ^ " \\vee " ^ predToLatex(pred2) ^ ")"
|   COND (pred1, pred2) => "(" ^ predToLatex(pred1) ^ " \\to " ^ predToLatex(pred2) ^ ")"
|   BIC (pred1, pred2) => "(" ^ predToLatex(pred1) ^ " \\leftrightarrow " ^ predToLatex(pred2) ^ ")"
|   ITE (pred1, pred2, pred3) => "ITE(" ^ predToLatex(pred1) ^ ", " ^ predToLatex(pred2) ^ ", " ^ predToLatex(pred3) ^ ")"
|   ALL (t, pred) => "\\forall " ^ termToLatex t ^ "[" ^ predToLatex(pred) ^ "]"
|   EX (t, pred) => "\\exists " ^ termToLatex t ^ "[" ^ predToLatex(pred) ^ "]"
|   FF => "\\bot"
and termToLatex(term) = case term of
    VAR (v) => v
|   CONST (c) => c
|   FUN (f, terms) => if (length terms) = 0 then f else f ^ "(" ^ (stringJoinWithComma (map (fn t => termToLatex t) terms)) ^ ")"

fun print(str, out) = TextIO.output(out, str)

fun printDigraph(nodes, treeEdges, backEdges, redEdges, out) = (
    print("digraph G {\n", out);
    print("\tnodesep = 0.5;\n", out);
    print("\tranksep = 0.35;\n", out);
    print("\tnode [shape=plaintext];\n", out);
    printNodes(nodes, out);
    print("\tsubgraph dir {\n", out);
    printTreeEdges(treeEdges, out);
    print("\t}\n", out);
    print("\tsubgraph ancestor {\n", out);
    print("\t\tedge [dir=back, color=blue, style=dashed]\n", out);
    printBackEdges(backEdges, out);
    print("\t}\n", out);
    print("\tsubgraph undir {\n", out);
    print("\t\tedge [dir=none, color=red]\n", out);
    printTreeEdges(redEdges, out);
    print("\t}\n", out);
    print("}\n", out)
)
and printNodes([], out) = ()
|   printNodes((pred, idx) :: nodes, out) = (
    print("\t\t" ^ Int.toString(idx) ^ " [texlbl=\"\\underline{" ^ Int.toString(idx) ^ ". $" ^ predToLatex(pred) ^ "$ }\"];\n", out);
    printNodes(nodes, out)
)
and printTreeEdges([], out) = ()
|   printTreeEdges((idx1, idx2) :: edges, out) = (
    print("\t\t" ^ Int.toString(idx1) ^ " -> " ^ Int.toString(idx2) ^ ";\n", out);
    printTreeEdges(edges, out)
)
and printBackEdges([], out) = ()
|   printBackEdges((idx1, idx2) :: edges, out) = (
    print("\t\t" ^ Int.toString(idx2) ^ " -> " ^ Int.toString(idx1) ^ ";\n", out);
    printBackEdges(edges, out)
)

fun mktableau (HENCE(predlist, pred)) =
let
    val predList = predlist @ [NOT pred]
    val pred = bigAnd predList
    val _ = verifyConstructors ((getConstructorsPred pred) @ (getConstantsPred pred))
    val _ = verifyPredicates (getPredicates pred)
    val _ = checkClosedPred (pred, [])
    val constants = isolate (getConstantsPred pred)
    val existentialVariables = isolate (getExistentialVariables pred)
    val env = getValidEnvironment (predList, freshConstants, constants @ getPrefix (freshConstants, length existentialVariables), 0)
    val out = TextIO.openOut "tableau.dot"
in
    (generateNodes(predList, env); printDigraph(!nodes, !treeEdges, !backEdges, !redEdges, out); TextIO.closeOut out; nodes := []; treeEdges := []; backEdges := []; redEdges := []; idx := 0)
end

(* fun mktableau2 (HENCE(predlist, pred)) =
let
    val predList = predlist @ [NOT pred]
    val pred = bigAnd predList
    val _ = verifyConstructors ((getConstructorsPred pred) @ (getConstantsPred pred))
    val _ = verifyPredicates (getPredicates pred)
    val _ = checkClosedPred (pred, [])
    val constants = isolate (getConstantsPred pred)
    val existentialVariables = isolate (getExistentialVariables pred)
    val env = getValidEnvironment (predList, freshConstants, constants @ getPrefix (freshConstants, length existentialVariables), 0)
    val out = TextIO.openOut "tableau.dot"
in ((getConstructorsPred pred) @ (getConstantsPred pred)) end *)