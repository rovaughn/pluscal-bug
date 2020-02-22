-------------------------------- MODULE main --------------------------------
EXTENDS FiniteSets, TLC, Integers, Sequences

(*--algorithm wisp
variables called = [process1 |-> FALSE, process2 |-> FALSE];

define
    \* Eventually, because both processes are weakly fair, test_procedure
    \* should run and finish in both processes.
    Fair == <>[](called.process1 /\ called.process2)
end define;

\* Macro that just calls test_procedure.
macro test_macro() begin
    call test_procedure();
end macro;

\* test_procedure marks called[self] as TRUE so we can verify if this procedure
\* ever runs for each process.
procedure test_procedure() begin
    TestProcedure:
        called[self] := TRUE;
        return;
end procedure;

\* process1 is a fair process that calls test_procedure via macro.
fair process process1 = "process1" begin
    TestProcess1: test_macro();
end process;

\* process2 is a fair process that calls test_procedure directly.
fair process process2 = "process2" begin
    TestProcess2: call test_procedure();
end process;

end algorithm; *)
\* BEGIN TRANSLATION
VARIABLES called, pc, stack

(* define statement *)
Fair == <>[](called.process1 /\ called.process2)


vars == << called, pc, stack >>

ProcSet == {"process1"} \cup {"process2"}

Init == (* Global variables *)
        /\ called = [process1 |-> FALSE, process2 |-> FALSE]
        /\ stack = [self \in ProcSet |-> << >>]
        /\ pc = [self \in ProcSet |-> CASE self = "process1" -> "TestProcess1"
                                        [] self = "process2" -> "TestProcess2"]

TestProcedure(self) == /\ pc[self] = "TestProcedure"
                       /\ called' = [called EXCEPT ![self] = TRUE]
                       /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                       /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]

test_procedure(self) == TestProcedure(self)

TestProcess1 == /\ pc["process1"] = "TestProcess1"
                /\ stack' = [stack EXCEPT !["process1"] = << [ procedure |->  "test_procedure",
                                                               pc        |->  "Done" ] >>
                                                           \o stack["process1"]]
                /\ pc' = [pc EXCEPT !["process1"] = "TestProcedure"]
                /\ UNCHANGED called

process1 == TestProcess1

TestProcess2 == /\ pc["process2"] = "TestProcess2"
                /\ stack' = [stack EXCEPT !["process2"] = << [ procedure |->  "test_procedure",
                                                               pc        |->  "Done" ] >>
                                                           \o stack["process2"]]
                /\ pc' = [pc EXCEPT !["process2"] = "TestProcedure"]
                /\ UNCHANGED called

process2 == TestProcess2

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == process1 \/ process2
           \/ (\E self \in ProcSet: test_procedure(self))
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(process1)
        /\ WF_vars(process2) /\ WF_vars(test_procedure("process2"))

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION

=============================================================================
\* Modification History
\* Last modified Fri Feb 21 17:59:52 MST 2020 by alec
\* Created Fri Feb 21 17:42:58 MST 2020 by alec
