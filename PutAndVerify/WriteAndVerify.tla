--------------------------- MODULE WriteAndVerify ---------------------------

CONSTANT CLIENTS

VARIABLE storage, clState

WVTypeOk == /\ storage \in [ CLIENTS -> { "none", "empty", "written" } ]
            /\ clState \in [ CLIENTS -> { "begin", "precheck-done", "blank-written", 
                                          "write-check-done", "committed", "aborted" } ]

WVInit == /\ storage = [ cli \in CLIENTS |-> "none" ]
          /\ clState = [ cli \in CLIENTS |-> "begin" ]

(* Only one execution can be committed. *)
(* Once committed, the file has been written. *)
WVConsistency == /\ \A i, j \in CLIENTS : 
                    (* If i != j, clState[i] and clState[j] cannot be both committed. *)
                    i /= j /\ clState[i] = "committed" => ~clState[j] = "committed"
                 /\ \A i, j \in CLIENTS : 
                    i /= j /\ storage[i] = "written" => ~storage[j] = "written"
                 /\ \A i \in CLIENTS : clState[i] = "committed" <=> storage[i] = "written"

(* "Verify" condition: storage only contains our file or nothing. *)
Check(c) == /\ \A f \in CLIENTS : f = c \/ storage[f] = "none"

Precheck(c) ==    /\ clState[c] = "begin" 
                  /\ IF Check(c) 
                     THEN clState' = [ clState EXCEPT ![c] = "precheck-done" ]
                     ELSE clState' = [ clState EXCEPT ![c] = "aborted" ]
                  /\ UNCHANGED << storage >>

WriteBlank(c) == /\ clState[c] = "precheck-done"
                 /\ storage' = [ storage EXCEPT ![c] = "empty" ]
                 /\ clState' = [ clState EXCEPT ![c] = "blank-written" ]

ConflictCheck(c) == /\ clState[c] = "blank-written" 
                    /\ IF Check(c) 
                       THEN clState' = [ clState EXCEPT ![c] = "write-check-done" ]
                       ELSE clState' = [ clState EXCEPT ![c] = "aborted" ]
                    /\ UNCHANGED << storage >>
                    
(* Delete the file when aborted. *)
RollBack(c) == /\ clState[c] = "aborted"
               /\ storage[c] /= "none"
               /\ storage' = [ storage EXCEPT ![c] = "none" ]
               /\ clState' = [ clState EXCEPT ![c] = "begin" ]

Commit(c) == /\ clState[c] = "write-check-done"
             /\ clState' = [ clState EXCEPT ![c] = "committed" ]
             /\ storage' = [ storage EXCEPT ![c] = "written" ]
             
WVNext == \E c \in CLIENTS: \/ Precheck(c)
                            \/ WriteBlank(c)
                            \/ ConflictCheck(c)
                            \/ RollBack(c)
                            \/ Commit(c)

WVSpec == WVInit /\ [][WVNext]_<< storage, clState >> 
                    
THEOREM WVSpec => [](WVConsistency /\ WVTypeOk)
               
=============================================================================
\* Modification History
\* Last modified Sat Jun 29 14:21:06 CST 2024 by Hillium
\* Created Sat Jun 29 10:41:34 CST 2024 by Hillium
