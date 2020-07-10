:- dynamic concurrent/0.

:- assert(concurrent).

possibly_concurrent_maplist(Goal, GoalList) :-
    concurrent -> concurrent_maplist(Goal, GoalList)
    ; maplist(Goal, GoalList).

possibly_concurrent_all(GoalList) :-
    possibly_concurrent_maplist(call, GoalList).

or_list([H|Tail]) :- call(H); or_list(Tail).

possibly_concurrent_find_earliest(Output, GoalList) :-
    concurrent -> find_earliest(Output, GoalList)
    ; once(or_list(GoalList)).

% ================================================================================
% find_earliest
% ================================================================================

do_work(Coordinator) :-

    thread_self(Me),

    % Request work
    thread_send_message(Coordinator, needwork(Me)),

    % Get work. The work includes both the work and the output
    % variable.  This is important because thread_send_messages
    % rewrite free variables.  So when we call the Goal, it will set
    % the output variable in WorkerAnswerVar.  We then unify this to
    % CoordinatorAnswerVar so the coordinator knows which variable it
    % is in.
    thread_get_message(work(WorkID, MyWork, WorkerAnswerVar)),

    %format('My work: ~w~n', [MyWork]),

    !,

    (transaction((
                        % Do work
                        %format('WorkerAnswerVar in WorkerThread is ~w~n', WorkerAnswerVar),
                        call(MyWork),
                        % Report success
                        %WorkerAnswerVar=CoordinatorAnswerVar,
                        %format('WorkerAnswerVar is ~w~n', WorkerAnswerVar),
                        thread_send_message(Coordinator, success(Me, WorkID)),
                        %format('Thread ~w waiting for a Msg~n', [Me]),
                        % Get instructions
                        thread_get_message(Msg),
                        %format('Thread ~w received a Msg ~w~n', [Me, Msg]),
                        % Commit or rollback?
                        Msg = commit
                    )),
     %writeln('Success commit, yeah'),
     thread_send_message(Coordinator, committed(WorkerAnswerVar))
     %format('Threat ~w sent committed message to thread ~w~n', [Me, Coordinator])
     ;
    thread_send_message(Coordinator, failed(Me, WorkID))).

do_work_repeatedly(Coordinator) :-
    repeat,
    once(do_work(Coordinator)),
    fail.

coordinator_handle_msg(AnswerVar, GoalList, needwork(ThreadID)) :-
    %format('Thread ~w needs work~n', [ThreadID]),
    available_work(WorkID),
    nth0(WorkID, GoalList, Work),
    !,
    %format('Work ~w is available~n', [Work]),
    retract(available_work(WorkID)),

    thread_send_message(ThreadID, work(WorkID, Work, AnswerVar)).

coordinator_handle_msg(_AnswerVar, _GoalList, needwork(_ThreadID)) :-
    not(available_work(_WorkID)),
    !.
    %format('Thread ~w needs work but there is none!~n', [ThreadID]).
    % Do nothing.  The coordinator thread will exit.

coordinator_handle_msg(_AnswerVar, _GoalList, success(ThreadID, WorkID)) :-
    %format('~w was successful ~w!~n', [WorkID, AnswerVar]),

    retractall(result(WorkID, _)),
    assert(result(WorkID, success)),
    assert(waiting(ThreadID,WorkID)).

coordinator_handle_msg(_AnswerVar, _GoalList, failed(_ThreadID, WorkID)) :-

    retractall(result(WorkID, _)),
    assert(result(WorkID, failed)).

coordinator_handle_msg(_AnswerVar, _GoalList, Msg) :-
    format('Generic message handler: ~w~n', [Msg]),
    throw(unexpected_error).

coordinator_check_waiting(Queue, AnswerVar) :-
    % Find lowest successful N
    setof(WorkID, result(WorkID, success), S),

    S = [BestID|_],

    %format('Best ID: ~w~n', [BestID]),

    % We can mark any pending items above this as failed or successful so we skip them
    % XXX: What happens if someone is already working on this WorkID?
    forall((result(WorkID, pending), WorkID > BestID),
           (%format('Marking WorkID ~w as obsolete~n', [WorkID]),
            assert(result(WorkID, obsolete)),
            retractall(result(WorkID, pending)))),

    % Any waiting above N can be told to rollback.
    forall((waiting(ThreadID, WorkID), WorkID > BestID),
           (%format('Telling ThreadID ~w to rollback for obsolete Work ID ~w~n', [ThreadID, WorkID]),
            retractall(waiting(ThreadID, WorkID)),
            thread_send_message(ThreadID, rollback))),

    % If there are no pending below this, N is the best and needs to be committed.
    not((result(WorkID, pending), WorkID < BestID))
    ->
        %format('Work ID ~w is the best!~n', [BestID]),
        % This thread must be waiting
        waiting(ThreadID, BestID),
        thread_send_message(ThreadID, commit),
        %format('Waiting for commit from thread ~w~n', [ThreadID]),

        % Unify with the answer from the winner
        thread_get_message(Queue, committed(AnswerVar))
    ;
    fail.

% What is the work for WorkID ID?
work_helper(ID, AnswerVar, Out) :- Out = (0 is ID mod 43, format('I won!!! ~w~n', [ID]), AnswerVar=ID).
%work_helper(ID, Out) :- Out = (random_between(0, 99, MyRand), MyRand < 5, format('I won!!! ~w~n', [ID])).
%work_helper(ID, Out) :- Out = (random(MyRand), MyRand < 0.05, format('I won!!! ~w~n', [ID])).

coordinator(GoalList, Queue, AnswerVar) :-

    %format('AnswerVar in coordinator ~w~n', AnswerVar),

    repeat,
    once((thread_get_message(Queue, Msg),
    %format('Received msg ~w~n', [Msg]),
    coordinator_handle_msg(AnswerVar, GoalList, Msg))),

    (coordinator_check_waiting(Queue, AnswerVar) ->
     % Exit: We found the answer.
         true
    ; (
    % We did not find the answer.  Fail out of loop
        not(result(_, pending)) -> !,
                                   fail
    ) ; (
    % Neither.  Fail to restart loop
    fail
    )).

% Stolen from threads.pl
jobs(Jobs, Options) :-
    (   option(threads(Jobs), Options)
    ->  true
    ;   current_prolog_flag(cpu_count, Jobs)
        ->  true
    ;   Jobs = 1
    ).

find_earliest(_AnswerVar, GoalList, _Options) :-
    not(is_list(GoalList)),
    !,
    throw(type_error(list,GoalList)).

find_earliest(AnswerVar, GoalList, Options) :-
    % Setup
    setup_call_cleanup((forall(nth0(N, GoalList, _Goal),
                               (assert(result(N, pending)),
                                assert(available_work(N)))),

                        message_queue_create(Queue, [alias(coordinator)]),

                        jobs(Jobs, Options),
                        % bagof is tough to convince not to introduce fresh variables for AnswerVar
                        findall(do_work_repeatedly(Queue), between(1, Jobs, _Num), Goals_),

                        Goals = [coordinator(GoalList, Queue, AnswerVar)|Goals_]),

                       % Goal
                       first_solution(AnswerVar, Goals, []),

                       % Cleanup
                       (message_queue_destroy(Queue),
                        retractall(result(_,_)),
                        retractall(waiting(_,_)))).

find_earliest(Answer, GoalList) :-
    find_earliest(Answer, GoalList, []).

test(Max, AnswerVar) :-
    bagof(G,

          N^(between(1, Max, N),
             work_helper(N, AnswerVar, G)),

          GoalList),

    find_earliest(AnswerVar, GoalList).

