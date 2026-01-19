-------------------------------- MODULE bcrb -----------------------------------
EXTENDS  FiniteSets, Integers, FiniteSets

CONSTANTS Processes, NbOfCorrProc, N, Tb, Tc, Fb, Fc

ASSUME NbOfCorrProc = N - Fb
    /\ N > 3 * Tb + 2 * Tc
    /\ Tb >= Fb
    /\ Tb >= 0
    /\ Tc >= Fc
    /\ Tc >= 0


VARIABLES ProcessesLocations, nsnt, nsntCandF, ncrashed

--------------------------------------------------------------------------------
TypeOk == nsnt \in Nat
    /\ nsntCandF \in Nat 
    /\ ncrashed \in Nat 
    /\ ProcessesLocations \in [Processes -> {"loc0", "loc1", "locSE", "locAC", "locCR"}]
    

Init == ProcessesLocations \in [Processes -> {"loc0", "loc1"}]
    /\ nsnt = 0
    /\ nsntCandF = 0
    /\ ncrashed = 0
--------------------------------------------------------------------------------

Rule0(p) == ProcessesLocations[p] = "loc0"
    /\ ncrashed < Fc
    /\ ProcessesLocations' = [ProcessesLocations EXCEPT ![p] = "locCR"]
    /\ ncrashed' = ncrashed + 1
    /\ UNCHANGED << nsnt, nsntCandF >>
--------------------------------------------------------------------------------
Rule1(p) == ProcessesLocations[p] = "loc1"
    /\ ncrashed < Fc
    /\ ProcessesLocations' = [ProcessesLocations EXCEPT ![p] = "locCR"]
    /\ ncrashed' = ncrashed + 1
    /\ UNCHANGED << nsnt, nsntCandF>>
--------------------------------------------------------------------------------
Rule2(p) == ProcessesLocations[p] = "loc1"
    /\ ncrashed < Fc
    /\ ProcessesLocations' = [ProcessesLocations EXCEPT ![p] = "locCR"]
    /\ nsntCandF' = nsntCandF + 1
    /\ ncrashed' = ncrashed + 1
    /\ UNCHANGED << nsnt >>
--------------------------------------------------------------------------------
Rule3(p) == ProcessesLocations[p] = "locSE"
    /\ ncrashed < Fc
    /\ ProcessesLocations' = [ProcessesLocations EXCEPT ![p] = "locCR"]
    /\ ncrashed' = ncrashed + 1
    /\ UNCHANGED << nsnt, nsntCandF >>
--------------------------------------------------------------------------------
Rule4(p) == ProcessesLocations[p] = "locAC"
    /\ ncrashed < Fc
    /\ ProcessesLocations' = [ProcessesLocations EXCEPT ![p] = "locCR"]
    /\ ncrashed' = ncrashed + 1
    /\ UNCHANGED << nsnt, nsntCandF >>
--------------------------------------------------------------------------------
Rule5(p) == ProcessesLocations[p] = "loc1"
    /\ ProcessesLocations' = [ProcessesLocations EXCEPT ![p] = "locSE"]
    /\ nsnt' = nsnt + 1
    /\ nsntCandF' = nsntCandF + 1
    /\ UNCHANGED <<ncrashed>>
--------------------------------------------------------------------------------
Rule6(p) == ProcessesLocations[p] = "loc0"
    /\ nsntCandF >= 2 * Tb + Tc + 1 - Fb
    /\ ProcessesLocations' = [ProcessesLocations EXCEPT ![p] = "locAC"]
    /\ nsnt' = nsnt + 1
    /\ nsntCandF' = nsntCandF + 1
    /\ UNCHANGED << ncrashed>>
--------------------------------------------------------------------------------
 Rule7(p) == ProcessesLocations[p] = "loc1"
    /\ nsntCandF >= 2 * Tb + Tc + 1 - Fb
    /\ ProcessesLocations' = [ProcessesLocations EXCEPT ![p] = "locAC"]
    /\ nsnt' = nsnt + 1
    /\ nsntCandF' = nsntCandF + 1
    /\ UNCHANGED << ncrashed>>
--------------------------------------------------------------------------------
Rule8(p) == ProcessesLocations[p] = "loc0"
    /\ nsntCandF >= Tb + 1 - Fb
    /\ ProcessesLocations' = [ProcessesLocations EXCEPT ![p] = "locSE"]
    /\ nsnt' = nsnt + 1
    /\ nsntCandF' = nsntCandF + 1
    /\ UNCHANGED << ncrashed >>
--------------------------------------------------------------------------------
Rule9(p) == ProcessesLocations[p] = "locSE"
    /\ nsntCandF >= 2 * Tb + Tc + 1 - Fb
    /\ ProcessesLocations' = [ProcessesLocations EXCEPT ![p] = "locAC"]
    /\ UNCHANGED << nsnt, nsntCandF, ncrashed >>
--------------------------------------------------------------------------------
Rule10(p) == ProcessesLocations[p] = "loc0"
    /\ ProcessesLocations' = [ProcessesLocations EXCEPT ![p] = "loc0"]
    /\ UNCHANGED << nsnt, nsntCandF, ncrashed >>
--------------------------------------------------------------------------------
Rule11(p) == ProcessesLocations[p] = "locSE"
    /\ ProcessesLocations' = [ProcessesLocations EXCEPT ![p] = "locSE"]
    /\ UNCHANGED << nsnt, nsntCandF, ncrashed>>

--------------------------------------------------------------------------------
Rule12(p) == ProcessesLocations[p] = "locAC"
    /\ ProcessesLocations' = [ProcessesLocations EXCEPT ![p] = "locAC"]
    /\ UNCHANGED << nsnt, nsntCandF, ncrashed>>
--------------------------------------------------------------------------------

Next == \E p \in Processes: Rule0(p)
    \/ Rule1(p)
    \/ Rule2(p)
    \/ Rule3(p)
    \/ Rule4(p)
    \/ Rule5(p)
    \/ Rule6(p)
    \/ Rule7(p)
    \/ Rule8(p)
    \/ Rule9(p)
    \/ Rule10(p)
    \/ Rule11(p)
    \/ Rule12(p)
--------------------------------------------------------------------------------
Spec == Init /\ [][Next]_<< ProcessesLocations, nsnt, nsntCandF, ncrashed >>
--------------------------------------------------------------------------------

NumInloc0 == Cardinality({ p \in Processes : ProcessesLocations[p] = "loc0" })
NumInloc1 == Cardinality({ p \in Processes : ProcessesLocations[p] = "loc1" })
NumInlocAC == Cardinality({ p \in Processes : ProcessesLocations[p] = "locAC" })
NumInlocSE == Cardinality({ p \in Processes : ProcessesLocations[p] = "locSE" })

unforg == (NumInloc1 = 0) => [](NumInlocAC = 0)

corr ==
    <>[](
        (
            ((nsnt < Tb + 1) \/ (NumInloc0 = 0))
            /\ ((nsnt < 2 * Tb + Tc + 1) \/ (NumInloc0 = 0))
            /\ ((nsnt < 2 * Tb + Tc + 1) \/ (NumInlocSE = 0))
            /\ (NumInloc1 = 0)
        )
        => ((NumInloc0 = 0) => <>(NumInlocAC /= 0))
    )

relay ==
    <>[](
        (
            ((nsnt < Tb + 1) \/ (NumInloc0 = 0))
            /\ ((nsnt < 2 * Tb + Tc + 1) \/ (NumInloc0 = 0))
            /\ ((nsnt < 2 * Tb + Tc + 1) \/ (NumInlocSE = 0))
            /\ (NumInloc1 = 0)
        )
        =>
        [](
           (NumInlocAC /= 0)
           => <> ((NumInloc0 = 0) /\ (NumInloc1 = 0) /\ (NumInlocSE = 0))
        )
    )
================================================================================
