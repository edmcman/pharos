% Copyright 2017 Carnegie Mellon University.
% ============================================================================================
% Driver rules for forward reasoning
% ============================================================================================

% These rules turn ordinary forward reasoning rules into dynamically asserted facts.  They
% follow a fairly rigid pattern, and might be generated by Prolog meta-programming in the
% future to keep the code cleaner.  These rules have been moved out of rules.pl to make space
% for more important rules that aren't just machinery...

% Each rule takes no parameters because it is supposed to assert a single fact in the same way
% that the guessing rules currently do, and return the callable parameter in "Out".

% The standard form of these rules (with commentary) is:
%
%concludeXXX(Out) :-
%    % We begin with an unbound set of parameters to a reasoning method.  In general, leaving the
%    % parameters unbound, and letting Prolog do it's thing has performed better than trying to
%    % enumerate possible values before calling reasonXXX().  It's a little unclear why, but
%    % that's what Cory's observed.
%    reasonXXX(Parameters),
%
%    % Occasionally there will be additional _fast_ constraints here.  iso_dif in particular
%    may be faster than a table lookup, since it's mostly a built in.
%    iso_dif(Parameter1, Parameter2),
%
%    % Check that the fact hasn't already been asserted.
%    not(factXXX(Parameters)),
%
%    % Check that there's no contradictory reasoning (not always required).
%    not(factNOTXXX(Parameters)),
%
%    % Although we're not doing so right now, it might be beneficial to have certain
%    % constraints that are always required here instead of in each reasoning rule?
%
%    % Report what we're doing for debugging.
%    loginfo('Concluding factXXX('),
%    loginfo(Parameters), loginfoln(').'),
%
%    % Then return the assertion in the Out Parameters, so that the caller can call() it to
%    % assert the fact.  Asserting the fact in our caller allows us to backtrack properly, while
%    % making the assertion here directly did not. Also the concludeMergeClasses() rule is a
%    % special case in that it does more than just call try_assert().
%    Out = try_assert(factXXX(Parameters)).

% --------------------------------------------------------------------------------------------
% Make a singleton class for any method in Set.
makeObjects(Set) :-
    maplist(make, Set).

% This predicate is called to retract subsumed facts
class_size_remove_redundant(factClassSizeGTE(Class, Size)) :-
    !,
    (setof(factClassSizeGTE(Class, TSize),
           (factClassSizeGTE(Class, TSize),
            TSize < Size),
           SizeFactSet) ->
         maplist(try_retract, SizeFactSet);
     true).

class_size_remove_redundant(factClassSizeLTE(Class, Size)) :-
    !,
    (setof(factClassSizeLTE(Class, TSize),
          (factClassSizeLTE(Class, TSize),
           TSize > Size),
          SizeFactSet) ->
     maplist(try_retract, SizeFactSet);
    true).

class_size_remove_redundant(X) :-
    throw_with_backtrace(error(representation_error(X), class_size_remove_redundant/1)).
ignore_one_arg(_X).

% Helper that produces an action from the arguments
try_assert_builder(Pred, ArgTuple, Out) :-
    try_assert_builder(ignore_one_arg, Pred, ArgTuple, Out).

try_assert_builder(Extra, Pred, ArgTuple, Out) :-
    tuple_to_list(ArgTuple, TupleElements),
    Fact =.. [Pred|TupleElements],
    Out = (try_assert(Fact),
           call(Extra, Fact)).

concludeMethod(Out) :-
    reportFirstSeen('concludeMethod'),
    setof(Method,
          (reasonMethod(Method),
           not(factMethod(Method)),
           not(factNOTMethod(Method)),
           loginfo('Concluding factMethod('),
           loginfo(Method), loginfoln(').')),
          MethodSets),
    maplist(try_assert_builder(factMethod), MethodSets, ActionSets),
    % Note: After we create the factMethod facts, we call makeNewObjects to ensure the proper
    % classes are created.
    Out = ((all(ActionSets),
            makeObjects(MethodSets))).

concludeConstructor(Out) :-
    reportFirstSeen('concludeConstructor'),
    setof(Method,
          (reasonConstructor(Method),
           not(factConstructor(Method)),
           not(factNOTConstructor(Method)),
           loginfo('Concluding factConstructor('),
           loginfo(Method), loginfoln(').')),
          MethodSets),
    maplist(try_assert_builder(factConstructor), MethodSets, ActionSets),
    Out = all(ActionSets).

concludeNOTConstructor(Out) :-
    reportFirstSeen('concludeNOTConstructor'),
    setof(Method,
          (reasonNOTConstructor(Method),
           not(factNOTConstructor(Method)),
           not(factConstructor(Method)),
           loginfo('Concluding factNOTConstructor('),
           loginfo(Method), loginfoln(').')),
          MethodSets),
    maplist(try_assert_builder(factNOTConstructor), MethodSets, ActionSets),
    Out = all(ActionSets).

concludeRealDestructor(Out) :-
    reportFirstSeen('concludeRealDestructor'),
    setof(Method,
          (reasonRealDestructor(Method),
           not(factRealDestructor(Method)),
           not(factNOTRealDestructor(Method)),
           loginfo('Concluding factRealDestructor('),
           loginfo(Method), loginfoln(').')),
          MethodSets),
    maplist(try_assert_builder(factRealDestructor), MethodSets, ActionSets),
    Out = all(ActionSets).

concludeNOTRealDestructor(Out) :-
    reportFirstSeen('concludeNOTRealDestructor'),
    setof(Method,
          (reasonNOTRealDestructor(Method),
           not(factRealDestructor(Method)),
           not(factNOTRealDestructor(Method)),
           loginfo('Concluding factNOTRealDestructor('),
           loginfo(Method), loginfoln(').')),
          MethodSets),
    maplist(try_assert_builder(factNOTRealDestructor), MethodSets, ActionSets),
    Out = all(ActionSets).

concludeDeletingDestructor(Out) :-
    reportFirstSeen('concludeDeletingDestructor'),
    setof(Method,
          (reasonDeletingDestructor(Method),
           not(factDeletingDestructor(Method)),
           not(factNOTDeletingDestructor(Method)),
           loginfo('Concluding factDeletingDestructor('),
           loginfo(Method), loginfoln(').')),
          MethodSets),
    maplist(try_assert_builder(factDeletingDestructor), MethodSets, ActionSets),
    Out = all(ActionSets).

concludeNOTDeletingDestructor(Out) :-
    setof(Method,
          (reasonNOTDeletingDestructor(Method),
           not(factDeletingDestructor(Method)),
           not(factNOTDeletingDestructor(Method)),
           loginfo('Concluding factNOTDeletingDestructor('),
           loginfo(Method), loginfoln(').')),
          MethodSets),
    maplist(try_assert_builder(factNOTDeletingDestructor), MethodSets, ActionSets),
    Out = all(ActionSets).

% This fact is only reasoned about, and it's similar to derived constructor.
concludeObjectInObject(Out) :-
    reportFirstSeen('concludeObjectInObject'),
    setof((OuterClass, InnerClass, Offset),
          (reasonObjectInObject(OuterClass, InnerClass, Offset),
           iso_dif(OuterClass, InnerClass),
           not(factObjectInObject(OuterClass, InnerClass, Offset)),
           % There's no factNOTObjectInObject, since most things aren't in most other things.
           loginfo('Concluding factObjectInObject('),
           loginfo(OuterClass), loginfo(', '),
           loginfo(InnerClass), loginfo(', '),
           loginfo(Offset), loginfoln(').')),
          TupleSets),
    maplist(try_assert_builder(factObjectInObject), TupleSets, ActionSets),
    Out = all(ActionSets).

concludeDerivedClass(Out) :-
    reportFirstSeen('concludeDerivedClass'),
    setof((DerivedClass, BaseClass, ObjectOffset),
          (reasonDerivedClass(DerivedClass, BaseClass, ObjectOffset),
           iso_dif(DerivedClass, BaseClass),
           not(factDerivedClass(DerivedClass, BaseClass, ObjectOffset)),
           not(factNOTDerivedClass(DerivedClass, BaseClass, ObjectOffset)),
           loginfo('Concluding factDerivedClass('),
           loginfo(DerivedClass), loginfo(', '),
           loginfo(BaseClass), loginfo(', '),
           loginfo(ObjectOffset), loginfoln(').')),
          TupleSets),
    maplist(try_assert_builder(factDerivedClass), TupleSets, ActionSets),
    Out = all(ActionSets).

concludeNOTDerivedClass(Out) :-
    reportFirstSeen('concludeNOTDerivedClass'),
    setof((DerivedClass, BaseClass, ObjectOffset),
          (reasonNOTDerivedClass(DerivedClass, BaseClass, ObjectOffset),
           iso_dif(DerivedClass, BaseClass),
           not(factDerivedClass(DerivedClass, BaseClass, ObjectOffset)),
           not(factNOTDerivedClass(DerivedClass, BaseClass, ObjectOffset)),
           loginfo('Concluding factNOTDerivedClass('),
           loginfo(DerivedClass), loginfo(', '),
           loginfo(BaseClass), loginfo(', '),
           loginfo(ObjectOffset), loginfoln(').')),
          TupleSets),
    maplist(try_assert_builder(factNOTDerivedClass), TupleSets, ActionSets),
    Out = all(ActionSets).

concludeEmbeddedObject(Out) :-
    reportFirstSeen('concludeEmbeddedObject'),
    setof((OuterClass, InnerClass, ObjectOffset),
          (reasonEmbeddedObject(OuterClass, InnerClass, ObjectOffset),
           iso_dif(OuterClass, InnerClass),
           not(factEmbeddedObject(OuterClass, InnerClass, ObjectOffset)),
           not(factNOTEmbeddedObject(OuterClass, InnerClass, ObjectOffset)),
           loginfo('Concluding factEmbeddedObject('),
           loginfo(OuterClass), loginfo(', '),
           loginfo(InnerClass), loginfo(', '),
           loginfo(ObjectOffset), loginfoln(').')),
          TupleSets),
    maplist(try_assert_builder(factEmbeddedObject), TupleSets, ActionSets),
    Out = all(ActionSets).

concludeNOTEmbeddedObject(Out) :-
    reportFirstSeen('concludeNOTEmbeddedObject'),
    setof((OuterClass, InnerClass, ObjectOffset),
          (reasonNOTEmbeddedObject(OuterClass, InnerClass, ObjectOffset),
           iso_dif(OuterClass, InnerClass),
           not(factEmbeddedObject(OuterClass, InnerClass, ObjectOffset)),
           not(factNOTEmbeddedObject(OuterClass, InnerClass, ObjectOffset)),
           loginfo('Concluding factNOTEmbeddedObject('),
           loginfo(OuterClass), loginfo(', '),
           loginfo(InnerClass), loginfo(', '),
           loginfo(ObjectOffset), loginfoln(').')),
          TupleSets),
    maplist(try_assert_builder(factNOTEmbeddedObject), TupleSets, ActionSets),
    Out = all(ActionSets).

% --------------------------------------------------------------------------------------------

concludeVFTable(Out) :-
    reportFirstSeen('concludeVFTable'),
    setof(VFTable,
          (reasonVFTable(VFTable),
           not(factVFTable(VFTable)),
           not(factNOTVFTable(VFTable)),
           loginfo('Concluding factVFTable('), loginfo(VFTable), loginfoln(').')),
          VFTableSets),
    maplist(try_assert_builder(factVFTable), VFTableSets, ActionSets),
    Out = all(ActionSets).

% There's no reasoning for NOT a vftable?  The fact might be asserted by a failed guess, but
% that's about as close as we would get to reasoning currently...

concludeVFTableWrite(Out) :-
    reportFirstSeen('concludeVFTableWrite'),
    setof((Insn, Method, Offset, VFTable),
          (reasonVFTableWrite(Insn, Method, Offset, VFTable),
           not(factVFTableWrite(Insn, Method, Offset, VFTable)),
           %not(reasonNOTVFTableWrite(Insn, Method, Offset, VFTable)),
           loginfo('Concluding factVFTableWrite('),
           loginfo(Insn), loginfo(', '),
           loginfo(Method), loginfo(', '),
           loginfo(Offset), loginfo(', '),
           loginfo(VFTable), loginfoln(').')),
          TupleSets),
    maplist(try_assert_builder(factVFTableWrite), TupleSets, ActionSets),
    Out = all(ActionSets).

concludeVFTableOverwrite(Out) :-
    reportFirstSeen('concludeVFTableOverwrite'),
    setof((Method, VFTable1, VFTable2, Offset),
          (reasonVFTableOverwrite(Method, VFTable1, VFTable2, Offset),
           not(factVFTableOverwrite(Method, VFTable1, VFTable2, Offset)),
           %not(reasonNOTVFTableOverwrite(Method, VFTable1, VFTable2, Offset)),
           loginfo('Concluding factVFTableOverwrite('),
           loginfo(Method), loginfo(', '),
           loginfo(VFTable1), loginfo(', '),
           loginfo(VFTable2), loginfo(', '),
           loginfo(Offset), loginfoln(').')),
          TupleSets),
    maplist(try_assert_builder(factVFTableOverwrite), TupleSets, ActionSets),
    Out = all(ActionSets).

concludeVFTableEntry(Out) :-
    reportFirstSeen('concludeVFTableEntry'),
    setof((VFTable, VFTableOffset, Address),
          (reasonVFTableEntry(VFTable, VFTableOffset, Address),
           not(factVFTableEntry(VFTable, VFTableOffset, Address)),
           not(factNOTVFTableEntry(VFTable, VFTableOffset, Address)),
           loginfo('Concluding factVFTableEntry('),
           loginfo(VFTable), loginfo(', '),
           loginfo(VFTableOffset), loginfo(', '),
           loginfo(Address), loginfoln(').')),
          TupleSets),
    maplist(try_assert_builder(factVFTableEntry), TupleSets, ActionSets),
    Out = all(ActionSets).

concludeNOTVFTableEntry(Out) :-
    reportFirstSeen('concludeNOTVFTableEntry'),
    setof((VFTable, VFTableOffset, Address),
          (reasonNOTVFTableEntry(VFTable, VFTableOffset, Address),
           not(factVFTableEntry(VFTable, VFTableOffset, Address)),
           not(factNOTVFTableEntry(VFTable, VFTableOffset, Address)),
           loginfo('Concluding factNOTVFTableEntry('),
           loginfo(VFTable), loginfo(', '),
           loginfo(VFTableOffset), loginfo(', '),
           loginfo(Address), loginfoln(').')),
          TupleSets),
    maplist(try_assert_builder(factNOTVFTableEntry), TupleSets, ActionSets),
    Out = all(ActionSets).

concludeVFTableSizeGTE(Out) :-
    reportFirstSeen('concludeVFTableSizeGTE'),
    setof((VFTable, Size),
          (reasonVFTableSizeGTE(VFTable, Size),
           not((factVFTableSizeGTE(VFTable, KnownSize), KnownSize >= Size)),
           loginfo('Concluding factVFTableSizeGTE('),
           loginfo(VFTable), loginfo(', '),
           loginfo(Size), loginfoln(').')),
          TupleSets),
    maplist(try_assert_builder(factVFTableSizeGTE), TupleSets, ActionSets),
    Out = all(ActionSets).

concludeVFTableSizeLTE(Out) :-
    reportFirstSeen('concludeVFTableSizeLTE'),
    setof((VFTable, Size),
          (reasonVFTableSizeLTE(VFTable, Size),
           not((factVFTableSizeLTE(VFTable, KnownSize), KnownSize >= Size)),
           loginfo('Concluding factVFTableSizeLTE('),
           loginfo(VFTable), loginfo(', '),
           loginfo(Size), loginfoln(').')),
          TupleSets),
    maplist(try_assert_builder(factVFTableSizeLTE), TupleSets, ActionSets),
    Out = all(ActionSets).

concludeVirtualFunctionCall(Out) :-
    setof((Insn, Method, OOffset, VFTable, TOffset),
          (reasonVirtualFunctionCall(Insn, Method, OOffset, VFTable, TOffset),
           not(factVirtualFunctionCall(Insn, Method, OOffset, VFTable, TOffset)),
           not(factNOTVirtualFunctionCall(Insn, Method, OOffset, VFTable, TOffset)),
           loginfo('Concluding factVirtualFunctonCall('),
           loginfo(Insn), loginfo(', '),
           loginfo(Method), loginfo(', '),
           loginfo(OOffset), loginfo(', '),
           loginfo(VFTable), loginfo(', '),
           loginfo(TOffset), loginfoln(').')),
          TupleSets),
    maplist(try_assert_builder(factVirtualFunctionCall), TupleSets, ActionSets),
    Out = all(ActionSets).

% --------------------------------------------------------------------------------------------

concludeVBTable(Out) :-
    reportFirstSeen('concludeVBTable'),
    setof(VBTable,
          (reasonVBTable(VBTable),
           not(factVBTable(VBTable)),
           not(factNOTVBTable(VBTable)),
           loginfo('Concluding factVBTable('), loginfo(VBTable), loginfoln(').')),
          VBTableSets),
    maplist(try_assert_builder(factVBTable), VBTableSets, ActionSets),
    Out = all(ActionSets).

% There are currently no forward reasoning rules for factNOTVBTable.

concludeVBTableWrite(Out) :-
    reportFirstSeen('concludeVBTableWrite'),
    setof((Insn, Method, Offset, VBTable),
          (reasonVBTableWrite(Insn, Method, Offset, VBTable),
           not(factVBTableWrite(Insn, Method, Offset, VBTable)),
           %not(reasonNOTVBTableWrite(Insn, Method, Offset, VBTable)),
           loginfo('Concluding factVBTableWrite('),
           loginfo(Insn), loginfo(', '),
           loginfo(Method), loginfo(', '),
           loginfo(Offset), loginfo(', '),
           loginfo(VBTable), loginfoln(').')),
          TupleSets),
    maplist(try_assert_builder(factVBTableWrite), TupleSets, ActionSets),
    Out = all(ActionSets).

% There are currently no forward reasoning rules for factNOTVBTableWrite.

concludeVBTableEntry(Out) :-
    reportFirstSeen('concludeVBTableEntry'),
    setof((VBTable, VBTableOffset, Value),
          (reasonVBTableEntry(VBTable, VBTableOffset, Value),
           not(factVBTableEntry(VBTable, VBTableOffset, Value)),
           not(factNOTVBTableEntry(VBTable, VBTableOffset, Value)),
           loginfo('Concluding factVBTableEntry('),
           loginfo(VBTable), loginfo(', '),
           loginfo(VBTableOffset), loginfo(', '),
           loginfo(Value), loginfoln(').')),
          TupleSets),
    maplist(try_assert_builder(factVBTableEntry), TupleSets, ActionSets),
    Out = all(ActionSets).

% There are currently no forward reasoning rules for factNOTVBTableEntry.

% --------------------------------------------------------------------------------------------

concludeClassSizeGTE(Out) :-
    reportFirstSeen('concludeClassSizeGTE'),
    setof((Class, Size),
          (reasonClassSizeGTE(Class, Size),
           not((factClassSizeGTE(Class, KnownSize), KnownSize >= Size)),
           loginfo('Concluding factClassSizeGTE('),
           loginfo(Class), loginfo(', '),
           loginfo(Size), loginfoln(').')),
          TupleSets),
    maplist(try_assert_builder(class_size_remove_redundant, factClassSizeGTE), TupleSets, ActionSets),
    Out = all(ActionSets).

concludeClassSizeLTE(Out) :-
    reportFirstSeen('concludeClassSizeLTE'),
    setof((Class, Size),
          (reasonClassSizeLTE(Class, Size),
           not((factClassSizeLTE(Class, KnownSize), KnownSize =< Size)),
           loginfo('Concluding factClassSizeLTE('),
           loginfo(Class), loginfo(', '),
           loginfo(Size), loginfoln(').')),
          TupleSets),
    maplist(try_assert_builder(class_size_remove_redundant, factClassSizeLTE), TupleSets, ActionSets),
    Out = all(ActionSets).

concludeClassHasNoBase(Out) :-
    reportFirstSeen('concludeClassHasNoBase'),
    setof(Class,
          (reasonClassHasNoBase(Class),
           not(factClassHasNoBase(Class)),
           not(factClassHasUnknownBase(Class)),
           loginfo('Concluding factClassHasNoBase('), loginfo(Class), loginfoln(').')),
          ClassSets),
    maplist(try_assert_builder(factClassHasNoBase), ClassSets, ActionSets),
    Out = all(ActionSets).

concludeClassHasUnknownBase(Out) :-
    reportFirstSeen('concludeClassHasUnknownBase'),
    setof(Class,
          (reasonClassHasUnknownBase(Class),
           not(factClassHasUnknownBase(Class)),
           not(factClassHasNoBase(Class)),
           loginfo('Concluding factClassHasUnknownBase('), loginfo(Class), loginfoln(').')),
          ClassSets),
    maplist(try_assert_builder(factClassHasUnknownBase), ClassSets, ActionSets),
    Out = all(ActionSets).

concludeClassCallsMethod(Out) :-
    reportFirstSeen('concludeClassCallsMethod'),
    setof((Class, Method),
          ExistingClass^(reasonClassCallsMethod(Class, Method),
           iso_dif(Class, Method),
           find(Method, ExistingClass),
           iso_dif(Class, ExistingClass),
           not(factClassCallsMethod(Class, Method)),
           %not(factNOTClassCallsMethod(Class, Method)),
           loginfo('Concluding factClassCallsMethod('), loginfo(Class), loginfo(', '),
           loginfo(Method), loginfoln(').')),
          TupleSets),
    maplist(try_assert_builder(factClassCallsMethod), TupleSets, ActionSets),
    Out = all(ActionSets).

concludeNOTMergeClasses(Out) :-
    reportFirstSeen('concludeNOTMergeClasses'),
    setof((Class1, Class2),
          (reasonNOTMergeClasses_new(Class1, Class2),
           iso_dif(Class1, Class2),
           not(dynFactNOTMergeClasses(Class1, Class2)),
           loginfo('Concluding factNOTMergeClasses('), loginfo(Class1), loginfo(', '),
           loginfo(Class2), loginfoln(').')),
          ClassSets),
    maplist(try_assert_builder(factNOTMergeClasses), ClassSets, ActionSets),
    Out = all(ActionSets).

concludeMergeClasses(Out) :-
    reportFirstSeen('concludeMergeClasses'),
    %% minof((Class1, Class2),
    %%       (reasonMergeClasses(Class1, Class2),
    %%        not(dynFactNOTMergeClasses(Class1, Class2)))),
    reasonMergeClasses(Class1, Class2),
    logtrace('factMergeClasses early('),
    logtrace(Class1), logtraceln(Class2),
    not(dynFactNOTMergeClasses(Class1, Class2)),
    loginfo('Concluding mergeClasses('),
    loginfo(Class1), loginfo(', '),
    loginfo(Class2), loginfoln(').'),
    Out = mergeClasses(Class1, Class2).

/* Local Variables:   */
/* mode: prolog       */
/* fill-column:    95 */
/* comment-column: 0  */
/* End:               */
