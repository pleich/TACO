------------------------------- MODULE bosco -------------------------------
EXTENDS Integers, FiniteSets

CONSTANT Processes, NbOfCorrProc, N, F, T

ASSUME NbOfCorrProc = N - F
    /\ N > 3 * T
    /\ T >= F
    /\ T >= 1

VARIABLES nsnt0, nsnt1, nsnt01, ProcessesLocations

--------------------------------------------------------------------------------
TypeOk == nsnt0 \in Nat
    /\ nsnt1 \in Nat 
    /\ nsnt01 \in Nat
    /\ ProcessesLocations \in [Processes -> {"loc0", "loc1", "locS0", "locS1", "locD0", "locD1", "locU0", "locU1" }] 

Init == ProcessesLocations \in [Processes -> {"loc0", "loc1"}] 
    /\ nsnt0 = 0
    /\ nsnt1 = 0
    /\ nsnt01 = 0
--------------------------------------------------------------------------------

Rule0(p) == ProcessesLocations[p] = "loc0"
    /\ ProcessesLocations' = [ProcessesLocations EXCEPT ![p] = "locS0"]
    /\ nsnt0' = nsnt0 + 1
    /\ nsnt01' = nsnt01 + 1                   
    /\ UNCHANGED<< nsnt1 >>
--------------------------------------------------------------------------------
Rule1(p) == ProcessesLocations[p] = "loc1"
    /\ ProcessesLocations' = [ProcessesLocations EXCEPT ![p] = "locS1"]
    /\ nsnt1' = nsnt1 + 1
    /\ nsnt01' = nsnt01 + 1
    /\ UNCHANGED<< nsnt0 >>
--------------------------------------------------------------------------------
Rule2(p) == ProcessesLocations[p] = "locS0"
    /\ nsnt01 >= N - T - F
    /\ 2 * nsnt0 >= N + 3 * T + 1 - 2 * F
    /\ ProcessesLocations' = [ProcessesLocations EXCEPT ![p] = "locD0"]
    /\ UNCHANGED<< nsnt0, nsnt1, nsnt01 >>    
--------------------------------------------------------------------------------
Rule3(p) == ProcessesLocations[p] = "locS1"
    /\ nsnt01 >= N - T - F
    /\ 2 * nsnt1 >= N + 3 * T + 1 - 2 * F
    /\ ProcessesLocations' = [ProcessesLocations EXCEPT ![p] = "locD1"]
    /\ UNCHANGED<< nsnt0, nsnt1, nsnt01 >>          
--------------------------------------------------------------------------------
Rule4(p) == ProcessesLocations[p] = "locS0"
    /\ nsnt01 >= N - T - F
    /\ 2 * nsnt0 < N + 3 * T + 1
    /\ 2 * nsnt1 < N + 3 * T + 1
    /\ 2 * nsnt0 >= N - T + 1 - 2 * F
    /\ 2 * nsnt1 < N - T + 1
    /\ ProcessesLocations' = [ProcessesLocations EXCEPT ![p] = "locU0"]
    /\ UNCHANGED<< nsnt0, nsnt1, nsnt01 >>
--------------------------------------------------------------------------------
Rule5(p) == ProcessesLocations[p] = "locS1"
    /\ nsnt01 >= N - T - F
    /\ 2 * nsnt0 < N + 3 * T + 1
    /\ 2 * nsnt1 < N + 3 * T + 1
    /\ 2 * nsnt0 >= N - T + 1 - 2 * F
    /\ 2 * nsnt1 < N - T + 1
    /\ ProcessesLocations' = [ProcessesLocations EXCEPT ![p] = "locU0"]
    /\ UNCHANGED<< nsnt0, nsnt1, nsnt01>>
--------------------------------------------------------------------------------
Rule6(p) == ProcessesLocations[p] = "locS0"
    /\ nsnt01 >= N - T - F
    /\ 2 * nsnt0 < N + 3 * T + 1
    /\ 2 * nsnt1 < N + 3 * T + 1
    /\ 2 * nsnt0 < N - T + 1
    /\ 2 * nsnt1 >= N - T + 1 - 2 * F
    /\ ProcessesLocations' = [ProcessesLocations EXCEPT ![p] = "locU1"]
    /\ UNCHANGED<< nsnt0, nsnt1, nsnt01 >>
--------------------------------------------------------------------------------
Rule7(p) == ProcessesLocations[p] = "locS1"
    /\ nsnt01 >= N - T - F
    /\ 2 * nsnt0 < N + 3 * T + 1
    /\ 2 * nsnt1 < N + 3 * T + 1
    /\ 2 * nsnt0 < N - T + 1
    /\ 2 * nsnt1 >= N - T + 1 - 2 * F
    /\ ProcessesLocations' = [ProcessesLocations EXCEPT ![p] = "locU1"]
    /\ UNCHANGED<<nsnt0, nsnt1, nsnt01 >>
--------------------------------------------------------------------------------
Rule8(p) == ProcessesLocations[p] = "locS0"
    /\ nsnt01 >= N - T - F
    /\ 2 * nsnt0 < N + 3 * T + 1
    /\ 2 * nsnt1 < N + 3 * T + 1
    /\ 2 * nsnt0 < N - T + 1
    /\ 2 * nsnt1 < N - T + 1
    /\ ProcessesLocations' = [ProcessesLocations EXCEPT ![p] = "locU0"]
    /\ UNCHANGED<< nsnt0, nsnt1, nsnt01 >>
--------------------------------------------------------------------------------
Rule9(p) == ProcessesLocations[p] = "locS0"
    /\ nsnt01 >= N - T - F
    /\ 2 * nsnt0 < N + 3 * T + 1
    /\ 2 * nsnt1 < N + 3 * T + 1
    /\ 2 * nsnt0 >= N - T + 1 - 2 * F
    /\ 2 * nsnt1 >= N - T + 1 - 2 * F
    /\ ProcessesLocations' = [ProcessesLocations EXCEPT ![p] = "locU0"]
    /\ UNCHANGED<< nsnt0, nsnt1, nsnt01 >>
--------------------------------------------------------------------------------
Rule10(p) == ProcessesLocations[p] = "locS1"
    /\ nsnt01 >= N - T - F
    /\ 2 * nsnt0 < N + 3 * T + 1
    /\ 2 * nsnt1 < N + 3 * T + 1
    /\ 2 * nsnt0 < N - T + 1 
    /\ 2 * nsnt1 < N - T + 1 
    /\ ProcessesLocations' = [ProcessesLocations EXCEPT ![p] = "locU1"]
    /\ UNCHANGED<< nsnt0, nsnt1, nsnt01 >>
--------------------------------------------------------------------------------
Rule11(p) == ProcessesLocations[p] = "locS1"
    /\ nsnt01 >= N - T - F
    /\ 2 * nsnt0 < N + 3 * T + 1
    /\ 2 * nsnt1 < N + 3 * T + 1
    /\ 2 * nsnt0 >= N - T + 1 - 2 * F
    /\ 2 * nsnt1 >= N - T + 1 - 2 * F
    /\ ProcessesLocations' = [ProcessesLocations EXCEPT ![p] = "locU1"]
    /\ UNCHANGED<< nsnt0, nsnt1, nsnt01>>
--------------------------------------------------------------------------------
Rule12(p) == ProcessesLocations[p] = "loc0"
    /\ ProcessesLocations' = [ProcessesLocations EXCEPT ![p] = "loc0"]
    /\ UNCHANGED<< nsnt0, nsnt1, nsnt01>>
--------------------------------------------------------------------------------
Rule13(p) == ProcessesLocations[p] = "loc1"
    /\ ProcessesLocations' = [ProcessesLocations EXCEPT ![p] = "loc1"]
    /\ UNCHANGED<< nsnt0, nsnt1, nsnt01 >>
--------------------------------------------------------------------------------
Rule14(p) ==  ProcessesLocations[p] = "locS0"
    /\ ProcessesLocations' = [ProcessesLocations EXCEPT ![p] = "locS0"]
    /\ UNCHANGED<< nsnt0, nsnt1, nsnt01 >>
--------------------------------------------------------------------------------
Rule15(p) == ProcessesLocations[p] = "locS1"
    /\ ProcessesLocations' = [ProcessesLocations EXCEPT ![p] = "locS1"]
    /\ UNCHANGED<< nsnt0, nsnt1, nsnt01 >>
--------------------------------------------------------------------------------
Rule16(p) == ProcessesLocations[p] = "locD0"
    /\ ProcessesLocations' = [ProcessesLocations EXCEPT ![p] = "locD0"]
    /\ UNCHANGED<< nsnt0, nsnt1, nsnt01 >>
--------------------------------------------------------------------------------
Rule17(p) == ProcessesLocations[p] = "locD1"
                     /\ ProcessesLocations' = [ProcessesLocations EXCEPT ![p] = "locD1"]
                     /\ UNCHANGED <<nsnt0, nsnt1, nsnt01 >>
--------------------------------------------------------------------------------
Rule18(p) == ProcessesLocations[p] = "locU0"
    /\ ProcessesLocations' = [ProcessesLocations EXCEPT ![p] = "locU0"]
    /\ UNCHANGED << nsnt0, nsnt1, nsnt01 >>
--------------------------------------------------------------------------------
Rule19(p) == ProcessesLocations[p] = "locU1"
    /\ ProcessesLocations' = [ProcessesLocations EXCEPT ![p] = "locU1"]
    /\ UNCHANGED << nsnt0, nsnt1, nsnt01 >>
--------------------------------------------------------------------------------
Next == \E p \in Processes: Rule0(p) \/ Rule1(p) \/ Rule2(p) \/ Rule3(p) 
    \/ Rule4(p) \/ Rule5(p) \/ Rule6(p) \/ Rule7(p) \/ Rule8(p) \/ Rule9(p)
    \/ Rule10(p) \/ Rule11(p) \/ Rule12(p) \/ Rule13(p) \/ Rule14(p) 
    \/ Rule15(p) \/ Rule16(p) \/ Rule17(p) \/ Rule18(p) \/ Rule19(p)
--------------------------------------------------------------------------------
Spec == Init /\ [][Next]_<< ProcessesLocations,nsnt0,nsnt1,nsnt01 >>
--------------------------------------------------------------------------------

NumInloc0 == Cardinality({p \in Processes : ProcessesLocations[p] = "loc0"})
NumInloc1 == Cardinality({p \in Processes : ProcessesLocations[p] = "loc1"})
NumInlocD1 == Cardinality({p \in Processes : ProcessesLocations[p] = "locD1" })
NumInlocD0 == Cardinality({p \in Processes : ProcessesLocations[p] = "locD0" })
NumInlocS1 == Cardinality({p \in Processes : ProcessesLocations[p] = "locS1"})
NumInlocU0 == Cardinality({p \in Processes : ProcessesLocations[p] = "locU0"})
NumInlocU1 == Cardinality({p \in Processes : ProcessesLocations[p] = "locU1"})
NumInlocS0 == Cardinality({p \in Processes : ProcessesLocations[p] = "locS0"})

one_step0 == ((F = 0 /\ N > 5 * T) \/ (N > 7 * T)) => 
    (NumInloc1 = 0 => [](NumInlocD1 = 0 /\ NumInlocU0 = 0 /\ NumInlocU1 = 0))

one_step1 == ((F = 0 /\ N > 5 * T) \/ (N > 7 * T)) => 
    ((NumInloc0 = 0) => [](NumInlocD0 = 0 /\ NumInlocU0 = 0 /\ NumInlocU1 = 0))

lemma3_0 == []((NumInlocD0 /= 0) => (NumInlocD1 = 0))
lemma3_1 == []((NumInlocD1 /= 0) => (NumInlocD0 = 0))
lemma3_2 == []((NumInlocD0 /= 0) => (NumInlocU1 = 0))
lemma3_3 == []((NumInlocD1 /= 0) => (NumInlocU0 = 0))

fast0 ==
  (((F = 0 /\ N > 5 * T) \/ (N > 7 * T))
    /\ <>[] ( ((nsnt01 < N - T) \/ (2 * nsnt0 < N + 3 * T + 1) \/ (NumInlocS0 = 0))
              /\ (NumInloc0 = 0) /\ (NumInloc1 = 0) ))
  =>
  ((NumInloc1 = 0) => <> ((NumInloc0 = 0) /\ (NumInloc1 = 0) /\ (NumInlocS0 = 0) 
                            /\ (NumInlocS1 = 0)
                      /\ (NumInlocD1 = 0) /\ (NumInlocU0 = 0) /\ (NumInlocU1 = 0)))

fast1 ==
  (((F = 0 /\ N > 5 * T) \/ (N > 7 * T))
    /\ <>[] ( ((nsnt01 < N - T) \/ (2 * nsnt1 < N + 3 * T + 1) \/ (NumInlocS1 = 0))
              /\ (NumInloc0 = 0) /\ (NumInloc1 = 0) ))
  =>
  ((NumInloc0 = 0) => <> ((NumInloc0 = 0) /\ (NumInloc1 = 0) /\ (NumInlocS0 = 0) 
                            /\ (NumInlocS1 = 0)
                      /\ (NumInlocD0 = 0) /\ (NumInlocU0 = 0) /\ (NumInlocU1 = 0)))

termination ==
    (<>[]((nsnt01 < N - T \/ (NumInlocS0 = 0 /\ NumInlocS1 = 0)) 
        /\ NumInloc0 = 0 /\ NumInloc1 = 0 ))
    => <>(NumInloc0 = 0 /\ NumInloc1 = 0 /\ NumInlocS0 = 0 /\ NumInlocS1 = 0)
================================================================================
