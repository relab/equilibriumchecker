----------------------------- MODULE FRChecker -----------------------------

EXTENDS Integers, Sequences, FiniteSets

CONSTANT Blocks, Processes

VARIABLES Blockchain1, Decided1, Profit1, NewBlock1, Valid1, Merit1, Blockchain2, Decided2, Profit2, NewBlock2, Valid2, Merit2, Rational

G1 == INSTANCE Committee WITH Blockchain <- Blockchain1, Decided <- Decided1, NewBlock <- NewBlock1, Profit <- Profit1, Valid <- Valid1, Merit <- Merit1

G2 == INSTANCE Committee WITH Blockchain <- Blockchain2, Decided <- Decided2, NewBlock <- NewBlock2, Profit <- Profit2, Valid <- Valid2, Merit <- Merit2

Init == /\ G1!Init
        /\ G2!Init
        /\ Rational = CHOOSE p \in Processes : TRUE
           
CommitBlock == /\ G1!CommitBlock("Reward All")
               /\ G2!CommitBlock("Reward All")
               /\ UNCHANGED <<Rational>>
               
AddNewBlock(p,b) == /\ G1!AddNewBlock(p,b)
                    /\ G2!AddNewBlock(p,b)
                    /\ UNCHANGED <<Rational>>

              
Vote(p) == /\ G1!Vote(p,TRUE)
           /\ IF p = Rational
              THEN G2!Vote(p,FALSE)
              ELSE G2!Vote(p,TRUE)
           /\ UNCHANGED <<Rational>>

              
Termination == /\ G1!Termination
               /\ G2!Termination
           
Next == \/ CommitBlock
        \/ \E p \in Processes , b \in Blocks : AddNewBlock(p,b)
        \/ \E p \in Processes : Vote(p)
        
Check == IF Termination
         THEN Profit1[Rational]+Merit1[Rational] \geq Profit2[Rational]+Merit2[Rational]
         ELSE TRUE
        
Equilibrium == IF Termination
               THEN \A p \in Processes: Profit1[p] \geq Profit2[p]
               ELSE TRUE
=============================================================================
\* Modification History
\* Last modified Fri Sep 17 00:29:48 CEST 2021 by SHRservice
\* Created Wed Sep 15 02:47:10 CEST 2021 by SHRservice
