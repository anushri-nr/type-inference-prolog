:- dynamic gvar/2.
/* match functions by unifying with arguments 
    and infering the result
*/

/* variable reference */
typeExp(Var, T):-
    \+ var(Var),
    Var = var(Name),
    !,
    atom(Name),
    gvar(Name, T).

typeExp(Fct, T):-
    \+ var(Fct), /* make sure Fct is not a variable */ 
    \+ atom(Fct), /* or an atom */
    functor(Fct, Fname, _Nargs), /* ensure we have a functor */
    !, /* if we make it here we do not try anything else */
    Fct =.. [Fname|Args], /* get list of arguments */
    append(Args, [T], FType), /* make it loook like a function signature */
    functionType(Fname, TArgs), /* get type of arguments from definition */
    typeExpList(FType, TArgs). /* recurisvely match types */

/* propagate basic types */
typeExp(T, T):-
    bType(T).

/* list version to allow function mathine */
typeExpList([], []).
typeExpList([Hin|Tin], [Hout|Tout]):-
    typeExp(Hin, Hout), /* type infer the head */
    typeExpList(Tin, Tout). /* recurse */

/* extract argument types from function argument declarations */
argTypes([], []).
argTypes([[Name, Type]|Args], [Type|Types]):-
    atom(Name),
    bType(Type),
    argTypes(Args, Types).

/* temporarily add function arguments as local variables */
assertArgs([], []).
assertArgs([[Name, Type]|Args], [Ref|Refs]):-
    asserta(gvar(Name, Type), Ref),
    assertArgs(Args, Refs).

eraseRefs([]).
eraseRefs([Ref|Refs]):-
    erase(Ref),
    eraseRefs(Refs).
    
/* TODO: add statements types and their type checking */
/* expression computation as a statement */
typeStatement(expr(Code), T):-
    typeExp(Code, T),
    bType(T).

/* code block */
typeStatement(block(Code), T):-
    is_list(Code),
    typeCode(Code, T).

/* if statement */
typeStatement(if(Cond, Then, Else), T):-
    typeExp(Cond, bool),
    typeStatement(Then, T),
    typeStatement(Else, T),
    bType(T).

/* local let-in statement */
typeStatement(letIn(Name, Type, Init, Body), T):-
    atom(Name),
    typeExp(Init, Type),
    bType(Type),
    setup_call_cleanup(
        asserta(gvar(Name, Type), Ref),
        once(typeStatement(Body, T)),
        erase(Ref)
    ),
    bType(T).

/* for statement */
typeStatement(for(Var, Start, End, Body), unit):-
    atom(Var),
    typeExp(Start, int),
    typeExp(End, int),
    setup_call_cleanup(
        asserta(gvar(Var, int), Ref),
        once(typeStatement(Body, _T)),
        erase(Ref)
    ).


/* global function definition */
typeStatement(gfLet(Name, Args, ReturnType, Body), unit):-
    atom(Name),
    argTypes(Args, ArgTypes),
    append(ArgTypes, [ReturnType], FType),
    bType(FType),
    setup_call_cleanup(
        assertArgs(Args, Refs),
        once(typeStatement(Body, ReturnType)),
        eraseRefs(Refs)
    ),
    asserta(gvar(Name, FType)).

/* global variable definition
    Example:
        gvLet(v, T, int) ~ let v = 3;
 */
typeStatement(gvLet(Name, T, Code), unit):-
    atom(Name), /* make sure we have a bound name */
    typeExp(Code, T), /* infer the type of Code and ensure it is T */
    bType(T), /* make sure we have an infered type */
    asserta(gvar(Name, T)). /* add definition to database */

/* Code is simply a list of statements. The type is 
    the type of the last statement 
*/
typeCode([S], T):-typeStatement(S, T).
typeCode([S, S2|Code], T):-
    typeStatement(S,_T),
    typeCode([S2|Code], T).

/* top level function */
infer(Code, T) :-
    is_list(Code), /* make sure Code is a list */
    deleteGVars(), /* delete all global definitions */
    typeCode(Code, T).

/* Basic types
    TODO: add more types if needed
 */
bType(int).
bType(float).
bType(string).
bType(bool).
bType(unit). /* unit type for things that are not expressions */
/*  functions type.
    The type is a list, the last element is the return type
    E.g. add: int->int->int is represented as [int, int, int]
    and can be called as add(1,2)->3
 */
bType([H]):- bType(H).
bType([H|T]):- bType(H), bType(T).

/*
    TODO: as you encounter global variable definitions
    or global functions add their definitions to 
    the database using:
        asserta( gvar(Name, Type) )
    To check the types as you encounter them in the code
    use:
        gvar(Name, Type) with the Name bound to the name.
    Type will be bound to the global type
    Examples:
        g

    Call the predicate deleveGVars() to delete all global 
    variables. Best wy to do this is in your top predicate
*/

deleteGVars():-retractall(gvar(_, _)), asserta((gvar(_X, _Y):-false)).

/*  builtin functions
    Each definition specifies the name and the 
    type as a function type

    TODO: add more functions
*/

fType(iplus, [int, int, int]).
fType(iminus, [int, int, int]).
fType(imul, [int, int, int]).
fType(idiv, [int, int, int]).

fType(fplus, [float, float, float]).
fType(fminus, [float, float, float]).
fType(fmul, [float, float, float]).
fType(fdiv, [float, float, float]).

fType(fToInt, [float, int]).
fType(iToFloat, [int, float]).

fType(ilt, [int, int, bool]).
fType(igt, [int, int, bool]).
fType(ieq, [int, int, bool]).

fType(flt, [float, float, bool]).
fType(fgt, [float, float, bool]).
fType(feq, [float, float, bool]).

fType(and, [bool, bool, bool]).
fType(or, [bool, bool, bool]).
fType(not, [bool, bool]).

fType(print, [_X, unit]). /* simple print */

/* Find function signature
   A function is either buld in using fType or
   added as a user definition with gvar(fct, List)
*/

% Check the user defined functions first
functionType(Name, Args):-
    gvar(Name, Args),
    is_list(Args). % make sure we have a function not a simple variable

% Check first built in functions
functionType(Name, Args) :-
    fType(Name, Args), !. % make deterministic

% This gets wiped out but we have it here to make the linter happy
gvar(_, _) :- false().
