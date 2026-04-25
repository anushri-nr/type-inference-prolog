:- begin_tests(typeInf).
:- include(typeInf). 

/* Note: when writing tests keep in mind that 
    the use of of global variable and function definitions
    define facts for gvar() predicate. Either test
    directy infer() predicate or call
    delegeGVars() predicate to clean up gvar().
*/

% tests for typeExp
test(typeExp_iplus) :- 
    typeExp(iplus(int,int), int).

% this test should fail
test(typeExp_iplus_F, [fail]) :-
    typeExp(iplus(int, int), float).

test(typeExp_iplus_T, [true(T == int)]) :-
    typeExp(iplus(int, int), T).

% NOTE: use nondet as option to test if the test is nondeterministic

% test for statement with state cleaning
test(typeStatement_gvar, [nondet, true(T == int)]) :- % should succeed with T=int
    deleteGVars(), /* clean up variables */
    typeStatement(gvLet(v, T, iplus(X, Y)), unit),
    assertion(X == int), assertion( Y == int), % make sure the types are int
    gvar(v, int). % make sure the global variable is defined

% same test as above but with infer 
test(infer_gvar, [nondet]) :-
    infer([gvLet(v, T, iplus(X, Y))], unit),
    assertion(T==int), assertion(X==int), assertion(Y=int),
    gvar(v,int).

% test custom function with mocked definition
test(mockedFct, [nondet]) :-
    deleteGVars(), % clean up variables since we cannot use infer
    asserta(gvar(my_fct, [int, float])), % add my_fct(int)-> float to the gloval variables
    typeExp(my_fct(X), T), % infer type of expression using or function
    assertion(X==int), assertion(T==float). % make sure the types infered are correct

test(typeExp_var, [nondet, true(T == int)]) :-
    deleteGVars(),
    asserta(gvar(x, int)),
    typeExp(var(x), T).

test(typeExp_var_missing, [fail]) :-
    deleteGVars(),
    typeExp(var(missing), _T).

test(infer_gvar_reference, [nondet]) :-
    infer([gvLet(x, T, int), gvLet(y, U, iplus(var(x), int))], unit),
    assertion(T == int),
    assertion(U == int),
    gvar(x, int),
    gvar(y, int).

test(infer_gvar_reference_bad_type, [fail]) :-
    infer([gvLet(x, _T, string), gvLet(y, _U, iplus(var(x), int))], unit).

test(typeExp_iminus, [true(T == int)]) :-
    typeExp(iminus(int, int), T).

test(typeExp_imul, [true(T == int)]) :-
    typeExp(imul(int, int), T).

test(typeExp_ilt, [true(T == bool)]) :-
    typeExp(ilt(int, int), T).

test(typeExp_fgt, [true(T == bool)]) :-
    typeExp(fgt(float, float), T).

test(typeExp_and, [true(T == bool)]) :-
    typeExp(and(bool, bool), T).

test(typeExp_not, [true(T == bool)]) :-
    typeExp(not(bool), T).

test(typeExp_bad_bool_op, [fail]) :-
    typeExp(and(int, bool), bool).

test(typeStatement_expr, [true(T == int)]) :-
    typeStatement(expr(iplus(int, int)), T).

test(infer_expr_single, [nondet, true(T == int)]) :-
    infer([expr(iplus(int, int))], T).

test(infer_expr_after_gvar, [nondet, true(T == int)]) :-
    infer([gvLet(x, _X, int), expr(iplus(var(x), int))], T).

test(infer_expr_bad_type, [fail]) :-
    infer([expr(iplus(string, int))], _T).

test(typeStatement_block, [nondet, true(T == bool)]) :-
    typeStatement(block([expr(iplus(int, int)), expr(ilt(int, int))]), T).

test(infer_block_single, [nondet, true(T == bool)]) :-
    infer([block([expr(iplus(int, int)), expr(ilt(int, int))])], T).

test(infer_block_with_gvar, [nondet, true(T == int)]) :-
    infer([block([gvLet(x, _X, int), expr(iplus(var(x), int))])], T).

test(infer_block_bad_statement, [fail]) :-
    infer([block([expr(iplus(int, int)), expr(iplus(string, int))])], _T).

test(typeStatement_if, [true(T == int)]) :-
    typeStatement(if(ilt(int, int), expr(int), expr(int)), T).

test(infer_if_expr, [nondet, true(T == int)]) :-
    infer([if(ilt(int, int), expr(iplus(int, int)), expr(iminus(int, int)))], T).

test(infer_if_block, [nondet, true(T == bool)]) :-
    infer([if(ilt(int, int),
              block([gvLet(x, _X, int), expr(ilt(var(x), int))]),
              expr(bool))], T).

test(infer_if_bad_cond, [fail]) :-
    infer([if(int, expr(int), expr(int))], _T).

test(infer_if_branch_mismatch, [fail]) :-
    infer([if(ilt(int, int), expr(int), expr(string))], _T).

test(typeStatement_letIn, [true(T == int)]) :-
    deleteGVars(),
    typeStatement(letIn(x, int, int, expr(iplus(var(x), int))), T).

test(infer_letIn_expr, [nondet, true(T == int)]) :-
    infer([letIn(x, int, int, expr(iplus(var(x), int)))], T).

test(infer_letIn_block, [nondet, true(T == bool)]) :-
    infer([letIn(x, int, int,
                 block([gvLet(y, _Y, iplus(var(x), int)),
                        expr(ilt(var(y), int))]))], T).

test(infer_letIn_bad_init, [fail]) :-
    infer([letIn(x, int, string, expr(var(x)))], _T).

test(infer_letIn_no_leak, [fail]) :-
    infer([letIn(x, int, int, expr(var(x))), expr(var(x))], _T).

test(infer_letIn_shadow_global, [nondet, true(T == string)]) :-
    infer([gvLet(x, _X, int),
           letIn(x, string, string, expr(var(x)))], T).

test(typeStatement_for, [true(T == unit)]) :-
    deleteGVars(),
    typeStatement(for(i, int, int, expr(iplus(var(i), int))), T).

test(infer_for, [nondet, true(T == unit)]) :-
    infer([for(i, int, int, expr(iplus(var(i), int)))], T).

test(infer_for_block_body, [nondet, true(T == unit)]) :-
    infer([for(i, int, int,
               block([gvLet(x, _X, iplus(var(i), int)),
                      expr(print(var(x)))])
          )], T).

test(infer_for_bad_start, [fail]) :-
    infer([for(i, string, int, expr(var(i)))], _T).

test(infer_for_bad_end, [fail]) :-
    infer([for(i, int, string, expr(var(i)))], _T).

test(infer_for_no_leak, [fail]) :-
    infer([for(i, int, int, expr(var(i))), expr(var(i))], _T).

test(typeStatement_gfLet, [nondet]) :-
    deleteGVars(),
    typeStatement(gfLet(add, [[x, int], [y, int]], int,
                        expr(iplus(var(x), var(y)))), unit),
    gvar(add, [int, int, int]).

test(infer_gfLet, [nondet]) :-
    infer([gfLet(add, [[x, int], [y, int]], int,
                 expr(iplus(var(x), var(y))))], unit),
    gvar(add, [int, int, int]).

test(infer_gfLet_call, [nondet, true(T == int)]) :-
    infer([gfLet(add, [[x, int], [y, int]], int,
                 expr(iplus(var(x), var(y)))),
           expr(add(int, int))], T).

test(infer_gfLet_call_bad_arg, [fail]) :-
    infer([gfLet(add, [[x, int], [y, int]], int,
                 expr(iplus(var(x), var(y)))),
           expr(add(int, string))], _T).

test(infer_gfLet_bad_return, [fail]) :-
    infer([gfLet(bad, [[x, int]], string,
                 expr(iplus(var(x), int)))], _T).

test(infer_gfLet_args_no_leak, [fail]) :-
    infer([gfLet(add, [[x, int], [y, int]], int,
                 expr(iplus(var(x), var(y)))),
           expr(var(x))], _T).

test(infer_gfLet_block_body, [nondet, true(T == bool)]) :-
    infer([gfLet(is_positive, [[x, int]], bool,
                 block([expr(igt(var(x), int))])),
           expr(is_positive(int))], T).

:-end_tests(typeInf).
