-------------------------------- MODULE main --------------------------------
EXTENDS FiniteSets, TLC, Integers, Sequences

(*--algorithm wisp
variables called = [process1 |-> FALSE, process2 |-> FALSE];

define
    Fair == <>[](called.process2)
end define;

macro test_macro() begin
    call test_procedure();
end macro;

procedure test_procedure() begin
    TestProcedure:
        called[self] := TRUE;
        return;
end procedure;

fair process process1 = "process1" begin
    TestProcess2: test_macro();
end process;

fair process process2 = "process2" begin
    TestProcess2: call test_procedure();
end process;

end algorithm; *)
\* BEGIN TRANSLATION
\* Label TestProcess2 of process process1 at line 12 col 5 changed to TestProcess2_
VARIABLES called, pc, stack

(* define statement *)
Fair == <>[](called.process2)


vars == << called, pc, stack >>

ProcSet == {"process1"} \cup {"process2"}

Init == (* Global variables *)
        /\ called = [process1 |-> FALSE, process2 |-> FALSE]
        /\ stack = [self \in ProcSet |-> << >>]
        /\ pc = [self \in ProcSet |-> CASE self = "process1" -> "TestProcess2_"
                                        [] self = "process2" -> "TestProcess2"]

TestProcedure(self) == /\ pc[self] = "TestProcedure"
                       /\ called' = [called EXCEPT ![self] = TRUE]
                       /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                       /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]

test_procedure(self) == TestProcedure(self)

TestProcess2_ == /\ pc["process1"] = "TestProcess2_"
                 /\ stack' = [stack EXCEPT !["process1"] = << [ procedure |->  "test_procedure",
                                                                pc        |->  "Done" ] >>
                                                            \o stack["process1"]]
                 /\ pc' = [pc EXCEPT !["process1"] = "TestProcedure"]
                 /\ UNCHANGED called

process1 == TestProcess2_

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
\* Last modified Fri Feb 21 17:49:18 MST 2020 by alec
\* Created Fri Feb 21 17:42:58 MST 2020 by alec
