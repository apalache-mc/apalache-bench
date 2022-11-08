-------------------------- MODULE EgalitarianPaxos --------------------------

EXTENDS (*Naturals,*) Integers, FiniteSets

(*
 @typeAlias: replica = Str;
 @typeAlias: instance = <<$replica,Int>>;
 @typeAlias: ballot = <<Int,$replica>>;
 @typeAlias: status = Str;
 @typeAlias: preAccept = {type: Str, src: $replica, dst: $replica, inst: $instance, ballot: $ballot, cmd: Int, deps: Set($instance), seq: Int};
 @typeAlias: accept = {type: Str, src: $replica, dst: $replica, inst: $instance, ballot: $ballot, cmd: Int, deps: Set($instance), seq: Int};
 @typeAlias: commit = {type: Str, inst: $instance, ballot: $ballot, cmd: Int, deps: Set($instance), seq: Int};
 @typeAlias: prepare = {type: Str, src: $replica, dst: $replica, inst: $instance, ballot: $ballot};
 @typeAlias: preAcceptReply = {type: Str, src: $replica, dst: $replica, inst: $instance, ballot: $ballot, deps: Set($instance), seq: Int, committed: Set($instance)};
 @typeAlias: acceptReply = {type: Str, src: $replica, dst: $replica, inst: $instance, ballot: $ballot};
 @typeAlias: prepareReply = {type: Str, src: $replica, dst: $replica, inst: $instance, ballot: $ballot, prev_ballot: $ballot , status: $status, cmd: Int, deps: Set($instance), seq: Int};
 @typeAlias: tryPreAccept = {type: Str, src: $replica, dst: $replica, inst: $instance, ballot: $ballot, cmd: Int, deps: Set($instance), seq: Int};
 @typeAlias: tryPreAcceptReply = {type: Str, src: $replica, dst: $replica, inst: $instance, ballot: $ballot, status: $status};
 @typeAlias: cmdLog = {inst: $instance, status: $status, ballot: $ballot, cmd: Int, deps: Set($instance), seq: Int};
*)
EgalitarianPaxos_typedefs == TRUE

-----------------------------------------------------------------------------

Max(S) == IF S = ({}) THEN 0 ELSE CHOOSE i \in S : \A j \in S : j <= i

(*********************************************************************************)
(* Constant parameters:                                                          *)
(*       Commands: the set of all possible commands                              *)
(*       Replicas: the set of all EPaxos replicas                                *)
(*       FastQuorums(r): the set of all fast quorums where r is a command leader *)
(*       SlowQuorums(r): the set of all slow quorums where r is a command leader *)
(*********************************************************************************)

\*CONSTANTS Commands, Replicas, FastQuorums(_), SlowQuorums(_), MaxBallot
CONSTANTS
    \* @type: Set(Int);
    Commands,
    \* @type: Set($replica);
    Replicas,
    \* @type: $replica -> Set(Set($replica));
    FastQuorumsFun,
    \* @type: $replica -> Set(Set($replica));
    SlowQuorumsFun,
    \* @type: Int;
    MaxBallot

(* APALACHE-BEGIN: *)
NCommands == 2

ConstInit ==
    /\ Commands \in { 1..2 }
    /\ Replicas \in { {"r1", "r2", "r3"} }
    /\ MaxBallot \in { 5 }
    /\ SlowQuorumsFun \in
        { [ r \in Replicas |->
          { Q \in SUBSET Replicas:
             r \in Q /\ Cardinality(Q) = (Cardinality(Replicas) \div 2) + 1 } ] }
    /\ FastQuorumsFun \in
        { [ r \in Replicas |->
          { Q \in SUBSET Replicas:
             r \in Q /\ Cardinality(Q) =
                (Cardinality(Replicas) \div 2) +
                             ((Cardinality(Replicas) \div 2) + 1) \div 2 } ] }

SlowQuorums(r) == SlowQuorumsFun[r]
FastQuorums(r) == FastQuorumsFun[r]

InstT == <<STRING, Int>>
MT == [type |-> STRING,
        src |-> STRING,
        dst |-> STRING,
        inst |-> InstT,
        committed |-> {InstT},
        deps |-> {InstT},
        ballot |-> <<Int, STRING>>,
        prev_ballot |-> <<Int, STRING>>,
        cmd |-> Int,
        seq |-> Int,
        status |-> STRING]

CmdLogT == [
    inst |-> InstT,
    status |-> STRING,
    ballot |-> <<Int, STRING>>,
    cmd |-> Int,
    deps |-> {InstT},
    seq |-> Int]

CommittedT == <<Int, {InstT}, Int>>
PreparingT == <<STRING, Int>>
DepsT == InstT


(* APALACHE-END *)

\*ASSUME IsFiniteSet(Replicas)

(***************************************************************************)
(* Quorum conditions:                                                      *)
(*  (simplified)                                                           *)
(***************************************************************************)

(*
ASSUME \A r \in Replicas:
  /\ SlowQuorums(r) \subseteq SUBSET Replicas
  /\ \A SQ \in SlowQuorums(r):
    /\ r \in SQ
    /\ Cardinality(SQ) = (Cardinality(Replicas) \div 2) + 1

ASSUME \A r \in Replicas:
  /\ FastQuorums(r) \subseteq SUBSET Replicas
  /\ \A FQ \in FastQuorums(r):
    /\ r \in FQ
    /\ Cardinality(FQ) = (Cardinality(Replicas) \div 2) +
                         ((Cardinality(Replicas) \div 2) + 1) \div 2
*)


(***************************************************************************)
(* Special none command                                                    *)
(***************************************************************************)

\*none == CHOOSE c : c \notin Commands
\* APALACHE:
none == 0


(***************************************************************************)
(* The instance space                                                      *)
(***************************************************************************)

\*Instances == Replicas \X (1..Cardinality(Commands))
\* APALACHE:
Instances == Replicas \X (1..NCommands)

(***************************************************************************)
(* The possible status of a command in the log of a replica.               *)
(***************************************************************************)

Status == {"not-seen", "pre-accepted", "accepted", "committed"}


(***************************************************************************)
(* All possible protocol messages:                                         *)
(***************************************************************************)

(*
Message ==
        [type: {"pre-accept"}, src: Replicas, dst: Replicas,
        inst: Instances, ballot: Nat \X Replicas,
        cmd: Commands \cup {none}, deps: SUBSET Instances, seq: Nat]
  \cup  [type: {"accept"}, src: Replicas, dst: Replicas,
        inst: Instances, ballot: Nat \X Replicas,
        cmd: Commands \cup {none}, deps: SUBSET Instances, seq: Nat]
  \cup  [type: {"commit"},
        inst: Instances, ballot: Nat \X Replicas,
        cmd: Commands \cup {none}, deps: SUBSET Instances, seq: Nat]
  \cup  [type: {"prepare"}, src: Replicas, dst: Replicas,
        inst: Instances, ballot: Nat \X Replicas]
  \cup  [type: {"pre-accept-reply"}, src: Replicas, dst: Replicas,
        inst: Instances, ballot: Nat \X Replicas,
        deps: SUBSET Instances, seq: Nat, committed: SUBSET Instances]
  \cup  [type: {"accept-reply"}, src: Replicas, dst: Replicas,
        inst: Instances, ballot: Nat \X Replicas]
  \cup  [type: {"prepare-reply"}, src: Replicas, dst: Replicas,
        inst: Instances, ballot: Nat \X Replicas, prev_ballot: Nat \X Replicas,
        status: Status,
        cmd: Commands \cup {none}, deps: SUBSET Instances, seq: Nat]
  \cup  [type: {"try-pre-accept"}, src: Replicas, dst: Replicas,
        inst: Instances, ballot: Nat \X Replicas,
        cmd: Commands \cup {none}, deps: SUBSET Instances, seq: Nat]
  \cup  [type: {"try-pre-accept-reply"}, src: Replicas, dst: Replicas,
        inst: Instances, ballot: Nat \X Replicas, status: Status \cup {"OK"}]
*)

MessagePreAccept == [type: {"pre-accept"}, src: Replicas, dst: Replicas, inst: Instances, ballot: Int \X Replicas, cmd: Commands \cup {none}, deps: SUBSET Instances, seq: Int]
MessageAccept == [type: {"accept"}, src: Replicas, dst: Replicas, inst: Instances, ballot: Int \X Replicas, cmd: Commands \cup {none}, deps: SUBSET Instances, seq: Int]
MessageCommit == [type: {"commit"}, inst: Instances, ballot: Int \X Replicas, cmd: Commands \cup {none}, deps: SUBSET Instances, seq: Int]
MessagePrepare == [type: {"prepare"}, src: Replicas, dst: Replicas, inst: Instances, ballot: Int \X Replicas]
MessagePreAcceptReply == [type: {"pre-accept-reply"}, src: Replicas, dst: Replicas, inst: Instances, ballot: Int \X Replicas, deps: SUBSET Instances, seq: Int, committed: SUBSET Instances]
MessageAcceptReply == [type: {"accept-reply"}, src: Replicas, dst: Replicas, inst: Instances, ballot: Int \X Replicas]
MessagePrepareReply == [type: {"prepare-reply"}, src: Replicas, dst: Replicas, inst: Instances, ballot: Int \X Replicas, prev_ballot: Int \X Replicas, status: Status, cmd: Commands \cup {none}, deps: SUBSET Instances, seq: Int]
MessageTryPreAccept == [type: {"try-pre-accept"}, src: Replicas, dst: Replicas, inst: Instances, ballot: Int \X Replicas, cmd: Commands \cup {none}, deps: SUBSET Instances, seq: Int]
MessageTryPreAcceptReply == [type: {"try-pre-accept-reply"}, src: Replicas, dst: Replicas, inst: Instances, ballot: Int \X Replicas, status: Status \cup {"OK"}]

(*******************************************************************************)
(* Variables:                                                                  *)
(*                                                                             *)
(*          comdLog = the commands log at each replica                         *)
(*          proposed = command that have been proposed                         *)
(*          executed = the log of executed commands at each replica            *)
(*          sentMsg = sent (but not yet received) messages                     *)
(*          crtInst = the next instance available for a command                *)
(*                    leader                                                   *)
(*          leaderOfInst = the set of instances each replica has               *)
(*                         started but not yet finalized                       *)
(*          committed = maps commands to set of commit attributs               *)
(*                      tuples                                                 *)
(*          ballots = largest ballot number used by any                        *)
(*                    replica                                                  *)
(*          preparing = set of instances that each replica is                  *)
(*                      currently preparing (i.e. recovering)                  *)
(*                                                                             *)
(*                                                                             *)
(*******************************************************************************)

VARIABLES
    \* @type: $replica -> Set($cmdLog);
    cmdLog,
    \* @type: Set(Int);
    proposed,
    \* @type: $replica -> Set(<<Int, Int>>);
    executed,
    \* sentMsg,
    \* @type: Set($preAccept);
    sentMsgPreAccept,
    \* @type: Set($accept);
    sentMsgAccept,
    \* @type: Set($commit);
    sentMsgCommit,
    \* @type: Set($prepare);
    sentMsgPrepare,
    \* @type: Set($preAcceptReply);
    sentMsgPreAcceptReply,
    \* @type: Set($acceptReply);
    sentMsgAcceptReply,
    \* @type: Set($prepareReply);
    sentMsgPrepareReply,
    \* @type: Set($tryPreAccept);
    sentMsgTryPreAccept,
    \* @type: Set($tryPreAcceptReply);
    sentMsgTryPreAcceptReply,
    \* @type: $replica -> Int;
    crtInst,
    \* @type: $replica -> Set($instance);
    leaderOfInst,
    \* @type: $instance -> Set(<<Int, Set($instance), Int>>);
    committed,
    \* @type: Int;
    ballots,
    \* @type: $replica -> Set($instance);
    preparing

TypeOK ==
    /\ cmdLog \in [Replicas -> SUBSET [inst: Instances,
                                       status: Status,
                                       ballot: Int \X Replicas,
                                       cmd: Commands \cup {none},
                                       deps: SUBSET Instances,
                                       seq: Int]]
    /\ proposed \in SUBSET Commands
    /\ executed \in [Replicas -> SUBSET (Int \X Commands)]
    \* /\ sentMsg \in SUBSET Message
    /\ sentMsgPreAccept \in SUBSET MessagePreAccept
    /\ sentMsgAccept \in SUBSET MessageAccept
    /\ sentMsgCommit \in SUBSET MessageCommit
    /\ sentMsgPrepare \in SUBSET MessagePrepare
    /\ sentMsgPreAcceptReply \in SUBSET MessagePreAcceptReply
    /\ sentMsgAcceptReply \in SUBSET MessageAcceptReply
    /\ sentMsgPrepareReply \in SUBSET MessagePrepareReply
    /\ sentMsgTryPreAccept \in SUBSET MessageTryPreAccept
    /\ sentMsgTryPreAcceptReply \in SUBSET MessageTryPreAcceptReply
    /\ crtInst \in [Replicas -> Int]
    /\ leaderOfInst \in [Replicas -> SUBSET Instances]
    /\ committed \in [Instances -> SUBSET ((Commands \cup {none}) \X
                                           (SUBSET Instances) \X
                                           Int)]
    /\ ballots \in Int
    /\ preparing \in [Replicas -> SUBSET Instances]

vars == << cmdLog, proposed, executed, sentMsgPreAccept, sentMsgAccept, sentMsgCommit, sentMsgPrepare, sentMsgPreAcceptReply, sentMsgAcceptReply, sentMsgPrepareReply, sentMsgTryPreAccept, sentMsgTryPreAcceptReply, crtInst, leaderOfInst,
           committed, ballots, preparing >>

(***************************************************************************)
(* Initial state predicate                                                 *)
(***************************************************************************)

Init ==
  \* /\ sentMsg = {}
  /\ sentMsgPreAccept = {}
  /\ sentMsgAccept = {}
  /\ sentMsgCommit = {}
  /\ sentMsgPrepare = {}
  /\ sentMsgPreAcceptReply = {}
  /\ sentMsgAcceptReply = {}
  /\ sentMsgPrepareReply = {}
  /\ sentMsgTryPreAccept = {}
  /\ sentMsgTryPreAcceptReply = {}
  /\ cmdLog = [r \in Replicas |-> {}]
  /\ proposed = {}
  /\ executed = [r \in Replicas |-> {}]
  /\ crtInst = [r \in Replicas |-> 1]
  /\ leaderOfInst = [r \in Replicas |-> {}]
  /\ committed = [i \in Instances |-> {}]
  /\ ballots = 1
  /\ preparing = [r \in Replicas |-> {}]



(***************************************************************************)
(* Actions                                                                 *)
(***************************************************************************)

StartPhase1(C, cleader, Q, inst, ballot, oldMsg) ==
    LET newDeps == {rec.inst: rec \in cmdLog[cleader]}
        newSeq == 1 + Max({t.seq: t \in cmdLog[cleader]})
        oldRecs == {rec \in cmdLog[cleader] : rec.inst = inst} IN
        /\ cmdLog' = [cmdLog EXCEPT ![cleader] = (@ \ oldRecs) \cup
                                {[inst   |-> inst,
                                  status |-> "pre-accepted",
                                  ballot |-> ballot,
                                  cmd    |-> C,
                                  deps   |-> newDeps,
                                  seq    |-> newSeq ]}]
        /\ leaderOfInst' = [leaderOfInst EXCEPT ![cleader] = @ \cup {inst}]
        /\ sentMsgPreAccept' = (sentMsgPreAccept \ oldMsg) \cup
                                ([type  : {"pre-accept"},
                                  src   : {cleader},
                                  dst   : Q \ {cleader},
                                  inst  : {inst},
                                  ballot: {ballot},
                                  cmd   : {C},
                                  deps  : {newDeps},
                                  seq   : {newSeq}])

StartPhase1SentMsgPrepareReply(C, cleader, Q, inst, ballot, oldMsg) ==
    LET newDeps == {rec.inst: rec \in cmdLog[cleader]}
        newSeq == 1 + Max({t.seq: t \in cmdLog[cleader]})
        oldRecs == {rec \in cmdLog[cleader] : rec.inst = inst} IN
        /\ cmdLog' = [cmdLog EXCEPT ![cleader] = (@ \ oldRecs) \cup
                                {[inst   |-> inst,
                                  status |-> "pre-accepted",
                                  ballot |-> ballot,
                                  cmd    |-> C,
                                  deps   |-> newDeps,
                                  seq    |-> newSeq ]}]
        /\ leaderOfInst' = [leaderOfInst EXCEPT ![cleader] = @ \cup {inst}]
        /\ sentMsgPrepareReply' = sentMsgPrepareReply \ oldMsg
        /\ sentMsgPreAccept' = sentMsgPreAccept \cup
                                ([type  : {"pre-accept"},
                                  src   : {cleader},
                                  dst   : Q \ {cleader},
                                  inst  : {inst},
                                  ballot: {ballot},
                                  cmd   : {C},
                                  deps  : {newDeps},
                                  seq   : {newSeq}])

StartPhase1SentMsgTryPreAcceptReply(C, cleader, Q, inst, ballot, oldMsg) ==
    LET newDeps == {rec.inst: rec \in cmdLog[cleader]}
        newSeq == 1 + Max({t.seq: t \in cmdLog[cleader]})
        oldRecs == {rec \in cmdLog[cleader] : rec.inst = inst} IN
        /\ cmdLog' = [cmdLog EXCEPT ![cleader] = (@ \ oldRecs) \cup
                                {[inst   |-> inst,
                                  status |-> "pre-accepted",
                                  ballot |-> ballot,
                                  cmd    |-> C,
                                  deps   |-> newDeps,
                                  seq    |-> newSeq ]}]
        /\ leaderOfInst' = [leaderOfInst EXCEPT ![cleader] = @ \cup {inst}]
        /\ sentMsgTryPreAcceptReply' = sentMsgTryPreAcceptReply \ oldMsg
        /\ sentMsgPreAccept' = sentMsgPreAccept \cup
                                ([type  : {"pre-accept"},
                                  src   : {cleader},
                                  dst   : Q \ {cleader},
                                  inst  : {inst},
                                  ballot: {ballot},
                                  cmd   : {C},
                                  deps  : {newDeps},
                                  seq   : {newSeq}])

\* @type: (Int, $replica) => Bool;
Propose(C, cleader) ==
    LET newInst == <<cleader, crtInst[cleader]>>
        newBallot == <<0, cleader>>
    IN  /\ proposed' = proposed \cup {C}
        /\ (\E Q \in FastQuorums(cleader):
                 StartPhase1(C, cleader, Q, newInst, newBallot, {}))
        /\ crtInst' = [crtInst EXCEPT ![cleader] = @ + 1]
        /\ UNCHANGED << executed, committed, ballots, preparing, sentMsgAccept, sentMsgCommit, sentMsgPrepare, sentMsgPreAcceptReply, sentMsgAcceptReply, sentMsgPrepareReply, sentMsgTryPreAccept, sentMsgTryPreAcceptReply >>


Phase1Reply(replica) ==
    \E msg \in sentMsgPreAccept:
        /\ msg.type = "pre-accept"
        /\ msg.dst = replica
        /\ LET oldRec == {rec \in cmdLog[replica]: rec.inst = msg.inst} IN
            /\ (\A rec \in oldRec :
                (rec.ballot = msg.ballot \/rec.ballot[1] < msg.ballot[1]))
            /\ LET newDeps == msg.deps \cup
                            ({t.inst: t \in cmdLog[replica]} \ {msg.inst})
                   newSeq == Max({msg.seq,
                                  1 + Max({t.seq: t \in cmdLog[replica]})})
                   instCom == {t.inst: t \in {tt \in cmdLog[replica] :
                              tt.status \in {"committed", "executed"}}} IN
                /\ cmdLog' = [cmdLog EXCEPT ![replica] = (@ \ oldRec) \cup
                                    {[inst   |-> msg.inst,
                                      status |-> "pre-accepted",
                                      ballot |-> msg.ballot,
                                      cmd    |-> msg.cmd,
                                      deps   |-> newDeps,
                                      seq    |-> newSeq]}]
                /\ sentMsgPreAccept' = sentMsgPreAccept \ {msg}
                /\ sentMsgPreAcceptReply' = sentMsgPreAcceptReply \cup
                                    {[type  |-> "pre-accept-reply",
                                      src   |-> replica,
                                      dst   |-> msg.src,
                                      inst  |-> msg.inst,
                                      ballot|-> msg.ballot,
                                      deps  |-> newDeps,
                                      seq   |-> newSeq,
                                      committed|-> instCom]}
                /\ UNCHANGED << proposed, crtInst, executed, leaderOfInst,
                                committed, ballots, preparing, sentMsgAccept, sentMsgCommit, sentMsgPrepare, sentMsgAcceptReply, sentMsgPrepareReply, sentMsgTryPreAccept, sentMsgTryPreAcceptReply >>

Phase1Fast(cleader, i, Q) ==
    /\ i \in leaderOfInst[cleader]
    /\ Q \in FastQuorums(cleader)
    /\ \E record \in cmdLog[cleader]:
        /\ record.inst = i
        /\ record.status = "pre-accepted"
        /\ record.ballot[1] = 0
        /\ LET replies == {msg \in sentMsgPreAcceptReply:
                                /\ msg.inst = i
                                /\ msg.type = "pre-accept-reply"
                                /\ msg.dst = cleader
                                /\ msg.src \in Q
                                /\ msg.ballot = record.ballot} IN
            /\ (\A replica \in (Q \ {cleader}):
                    \E msg \in replies: msg.src = replica)
            /\ (\A r1, r2 \in replies:
                /\ r1.deps = r2.deps
                /\ r1.seq = r2.seq)
            /\ LET r == CHOOSE rTemp \in replies : TRUE IN
                /\ LET localCom == {t.inst:
                            t \in {tt \in cmdLog[cleader] :
                                 tt.status \in {"committed", "executed"}}}
                       extCom == UNION {msg.committed: msg \in replies} IN
                       (r.deps \subseteq (localCom \cup extCom))
                /\ cmdLog' = [cmdLog EXCEPT ![cleader] = (@ \ {record}) \cup
                                        {[inst   |-> i,
                                          status |-> "committed",
                                          ballot |-> record.ballot,
                                          cmd    |-> record.cmd,
                                          deps   |-> r.deps,
                                          seq    |-> r.seq ]}]
                /\ sentMsgPreAcceptReply' = sentMsgPreAcceptReply \ replies
                /\ sentMsgCommit' = sentMsgCommit \cup
                            {[type  |-> "commit",
                            inst    |-> i,
                            ballot  |-> record.ballot,
                            cmd     |-> record.cmd,
                            deps    |-> r.deps,
                            seq     |-> r.seq]}
                /\ leaderOfInst' = [leaderOfInst EXCEPT ![cleader] = @ \ {i}]
                /\ committed' = [committed EXCEPT ![i] =
                                            @ \cup {<<record.cmd, r.deps, r.seq>>}]
                /\ UNCHANGED << proposed, executed, crtInst, ballots, preparing, sentMsgPreAccept, sentMsgAccept, sentMsgPrepare, sentMsgAcceptReply, sentMsgPrepareReply, sentMsgTryPreAccept, sentMsgTryPreAcceptReply >>

Phase1Slow(cleader, i, Q) ==
    /\ i \in leaderOfInst[cleader]
    /\ Q \in SlowQuorums(cleader)
    /\ \E record \in cmdLog[cleader]:
        /\ record.inst = i
        /\ record.status = "pre-accepted"
        /\ LET replies == {msg \in sentMsgPreAcceptReply:
                                /\ msg.inst = i
                                /\ msg.type = "pre-accept-reply"
                                /\ msg.dst = cleader
                                /\ msg.src \in Q
                                /\ msg.ballot = record.ballot} IN
            /\ (\A replica \in (Q \ {cleader}): \E msg \in replies: msg.src = replica)
            /\ LET finalDeps == UNION {msg.deps : msg \in replies}
                   finalSeq == Max({msg.seq : msg \in replies}) IN
                /\ cmdLog' = [cmdLog EXCEPT ![cleader] = (@ \ {record}) \cup
                                        {[inst   |-> i,
                                          status |-> "accepted",
                                          ballot |-> record.ballot,
                                          cmd    |-> record.cmd,
                                          deps   |-> finalDeps,
                                          seq    |-> finalSeq ]}]
                /\ \E SQ \in SlowQuorums(cleader):
                    /\ sentMsgPreAcceptReply' = sentMsgPreAcceptReply \ replies
                    /\ sentMsgAccept' = sentMsgAccept \cup
                            ([type : {"accept"},
                            src : {cleader},
                            dst : SQ \ {cleader},
                            inst : {i},
                            ballot: {record.ballot},
                            cmd : {record.cmd},
                            deps : {finalDeps},
                            seq : {finalSeq}])
                /\ UNCHANGED << proposed, executed, crtInst, leaderOfInst,
                                committed, ballots, preparing, sentMsgPreAccept, sentMsgCommit, sentMsgPrepare, sentMsgAcceptReply, sentMsgPrepareReply, sentMsgTryPreAccept, sentMsgTryPreAcceptReply >>

Phase2Reply(replica) ==
    \E msg \in sentMsgAccept:
        /\ msg.type = "accept"
        /\ msg.dst = replica
        /\ LET oldRec == {rec \in cmdLog[replica]: rec.inst = msg.inst} IN
            /\ (\A rec \in oldRec: (rec.ballot = msg.ballot \/
                                    rec.ballot[1] < msg.ballot[1]))
            /\ cmdLog' = [cmdLog EXCEPT ![replica] = (@ \ oldRec) \cup
                                {[inst   |-> msg.inst,
                                  status |-> "accepted",
                                  ballot |-> msg.ballot,
                                  cmd    |-> msg.cmd,
                                  deps   |-> msg.deps,
                                  seq    |-> msg.seq]}]
            /\ sentMsgAccept' = sentMsgAccept \ {msg}
            /\ sentMsgAcceptReply' = sentMsgAcceptReply \cup
                                {[type  |-> "accept-reply",
                                  src   |-> replica,
                                  dst   |-> msg.src,
                                  inst  |-> msg.inst,
                                  ballot|-> msg.ballot]}
            /\ UNCHANGED << proposed, crtInst, executed, leaderOfInst,
                            committed, ballots, preparing, sentMsgPreAccept, sentMsgCommit, sentMsgPrepare, sentMsgPreAcceptReply, sentMsgPrepareReply, sentMsgTryPreAccept, sentMsgTryPreAcceptReply >>


Phase2Finalize(cleader, i, Q) ==
    /\ i \in leaderOfInst[cleader]
    /\ Q \in SlowQuorums(cleader)
    /\ \E record \in cmdLog[cleader]:
        /\ record.inst = i
        /\ record.status = "accepted"
        /\ LET replies == {msg \in sentMsgAcceptReply:
                                /\ msg.inst = i
                                /\ msg.type = "accept-reply"
                                /\ msg.dst = cleader
                                /\ msg.src \in Q
                                /\ msg.ballot = record.ballot} IN
            /\ (\A replica \in (Q \ {cleader}): \E msg \in replies:
                                                        msg.src = replica)
            /\ cmdLog' = [cmdLog EXCEPT ![cleader] = (@ \ {record}) \cup
                                    {[inst   |-> i,
                                      status |-> "committed",
                                      ballot |-> record.ballot,
                                      cmd    |-> record.cmd,
                                      deps   |-> record.deps,
                                      seq    |-> record.seq ]}]
            /\ sentMsgAcceptReply' = sentMsgAcceptReply \ replies
            /\ sentMsgCommit' = sentMsgCommit \cup
                        {[type  |-> "commit",
                        inst    |-> i,
                        ballot  |-> record.ballot,
                        cmd     |-> record.cmd,
                        deps    |-> record.deps,
                        seq     |-> record.seq]}
            /\ committed' = [committed EXCEPT ![i] = @ \cup
                               {<<record.cmd, record.deps, record.seq>>}]
            /\ leaderOfInst' = [leaderOfInst EXCEPT ![cleader] = @ \ {i}]
            /\ UNCHANGED << proposed, executed, crtInst, ballots, preparing, sentMsgPreAccept, sentMsgAccept, sentMsgPrepare, sentMsgPreAcceptReply, sentMsgPrepareReply, sentMsgTryPreAccept, sentMsgTryPreAcceptReply >>

\* @type: ($replica, $commit) => Bool;
Commit(replica, cmsg) ==
    LET oldRec == {rec \in cmdLog[replica] : rec.inst = cmsg.inst} IN
        /\ \A rec \in oldRec : (rec.status \notin {"committed", "executed"} /\
                                rec.ballot[1] <= cmsg.ballot[1])
        /\ cmdLog' = [cmdLog EXCEPT ![replica] = (@ \ oldRec) \cup
                                    {[inst     |-> cmsg.inst,
                                      status   |-> "committed",
                                      ballot   |-> cmsg.ballot,
                                      cmd      |-> cmsg.cmd,
                                      deps     |-> cmsg.deps,
                                      seq      |-> cmsg.seq]}]
        /\ committed' = [committed EXCEPT ![cmsg.inst] = @ \cup
                               {<<cmsg.cmd, cmsg.deps, cmsg.seq>>}]
        /\ UNCHANGED << proposed, executed, crtInst, leaderOfInst,
                        ballots, preparing, sentMsgPreAccept, sentMsgAccept, sentMsgCommit, sentMsgPrepare, sentMsgPreAcceptReply, sentMsgAcceptReply, sentMsgPrepareReply, sentMsgTryPreAccept, sentMsgTryPreAcceptReply >>


(***************************************************************************)
(* Recovery actions                                                        *)
(***************************************************************************)

SendPrepare(replica, i, Q) ==
    /\ i \notin leaderOfInst[replica]
    \*/\ i \notin preparing[replica]
    /\ ballots <= MaxBallot
    /\ ~(\E rec \in cmdLog[replica] :
                        /\ rec.inst = i
                        /\ rec.status \in {"committed", "executed"})
    /\ sentMsgPrepare' = sentMsgPrepare \cup
                    ([type   : {"prepare"},
                     src    : {replica},
                     dst    : Q,
                     inst   : {i},
                     ballot : {<< ballots, replica >>}])
    /\ ballots' = ballots + 1
    /\ preparing' = [preparing EXCEPT ![replica] = @ \cup {i}]
    /\ UNCHANGED << cmdLog, proposed, executed, crtInst,
                    leaderOfInst, committed, sentMsgPreAccept, sentMsgAccept, sentMsgCommit, sentMsgPreAcceptReply, sentMsgAcceptReply, sentMsgPrepareReply, sentMsgTryPreAccept, sentMsgTryPreAcceptReply >>

ReplyPrepare(replica) ==
    \E msg \in sentMsgPrepare :
        /\ msg.type = "prepare"
        /\ msg.dst = replica
        /\ \/ \E rec \in cmdLog[replica] :
                /\ rec.inst = msg.inst
                /\ msg.ballot[1] > rec.ballot[1]
                /\ sentMsgPrepare' = sentMsgPrepare \ {msg}
                /\ sentMsgPrepareReply' = sentMsgPrepareReply \cup
                            {[type  |-> "prepare-reply",
                              src   |-> replica,
                              dst   |-> msg.src,
                              inst  |-> rec.inst,
                              ballot|-> msg.ballot,
                              prev_ballot|-> rec.ballot,
                              status|-> rec.status,
                              cmd   |-> rec.cmd,
                              deps  |-> rec.deps,
                              seq   |-> rec.seq]}
                 /\ cmdLog' = [cmdLog EXCEPT ![replica] = (@ \ {rec}) \cup
                            {[inst  |-> rec.inst,
                              status|-> rec.status,
                              ballot|-> msg.ballot,
                              cmd   |-> rec.cmd,
                              deps  |-> rec.deps,
                              seq   |-> rec.seq]}]
                 /\ IF rec.inst \in leaderOfInst[replica] THEN
                        /\ leaderOfInst' = [leaderOfInst EXCEPT ![replica] =
                                                                @ \ {rec.inst}]
                        /\ UNCHANGED << proposed, executed, committed,
                                        crtInst, ballots, preparing, sentMsgPreAccept, sentMsgAccept, sentMsgCommit, sentMsgPreAcceptReply, sentMsgAcceptReply, sentMsgTryPreAccept, sentMsgTryPreAcceptReply >>
                    ELSE UNCHANGED << proposed, executed, committed, crtInst,
                                      ballots, preparing, leaderOfInst, sentMsgPreAccept, sentMsgAccept, sentMsgCommit, sentMsgPreAcceptReply, sentMsgAcceptReply, sentMsgTryPreAccept, sentMsgTryPreAcceptReply >>

           \/ /\ ~(\E rec \in cmdLog[replica] : rec.inst = msg.inst)
              /\ sentMsgPrepare' = sentMsgPrepare \ {msg}
              /\ sentMsgPrepareReply' = sentMsgPrepareReply \cup
                            {[type  |-> "prepare-reply",
                              src   |-> replica,
                              dst   |-> msg.src,
                              inst  |-> msg.inst,
                              ballot|-> msg.ballot,
                              prev_ballot|-> << 0, replica >>,
                              status|-> "not-seen",
                              cmd   |-> none,
                              deps  |-> {},
                              seq   |-> 0]}
              /\ cmdLog' = [cmdLog EXCEPT ![replica] = @ \cup
                            {[inst  |-> msg.inst,
                              status|-> "not-seen",
                              ballot|-> msg.ballot,
                              cmd   |-> none,
                              deps  |-> {},
                              seq   |-> 0]}]
              /\ UNCHANGED << proposed, executed, committed, crtInst, ballots,
                              leaderOfInst, preparing, sentMsgPreAccept, sentMsgAccept, sentMsgCommit, sentMsgPreAcceptReply, sentMsgAcceptReply, sentMsgTryPreAccept, sentMsgTryPreAcceptReply >>

PrepareFinalize(replica, i, Q) ==
    /\ i \in preparing[replica]
    /\ \E rec \in cmdLog[replica] :
       /\ rec.inst = i
       /\ rec.status \notin {"committed", "executed"}
       /\ LET replies == {msg \in sentMsgPrepareReply :
                        /\ msg.inst = i
                        /\ msg.type = "prepare-reply"
                        /\ msg.dst = replica
                        /\ msg.ballot = rec.ballot} IN
            /\ (\A rep \in Q : \E msg \in replies : msg.src = rep)
            /\  \/ \E com \in replies :
                        /\ (com.status \in {"committed", "executed"})
                        /\ preparing' = [preparing EXCEPT ![replica] = @ \ {i}]
                        /\ sentMsgPrepareReply' = sentMsgPrepareReply \ replies
                        /\ UNCHANGED << cmdLog, proposed, executed, crtInst, leaderOfInst,
                                        committed, ballots, sentMsgPreAccept, sentMsgAccept, sentMsgCommit, sentMsgPrepare, sentMsgPreAcceptReply, sentMsgAcceptReply, sentMsgTryPreAccept, sentMsgTryPreAcceptReply >>
                \/ /\ ~(\E msg \in replies : msg.status \in {"committed", "executed"})
                   /\ \E acc \in replies :
                        /\ acc.status = "accepted"
                        /\ (\A msg \in (replies \ {acc}) :
                            (msg.prev_ballot[1] <= acc.prev_ballot[1] \/
                             msg.status # "accepted"))
                        /\ sentMsgPrepareReply' = sentMsgPrepareReply \ replies
                        /\ sentMsgAccept' = sentMsgAccept \cup
                                 ([type  : {"accept"},
                                  src   : {replica},
                                  dst   : Q \ {replica},
                                  inst  : {i},
                                  ballot: {rec.ballot},
                                  cmd   : {acc.cmd},
                                  deps  : {acc.deps},
                                  seq   : {acc.seq}])
                        /\ cmdLog' = [cmdLog EXCEPT ![replica] = (@ \ {rec}) \cup
                                {[inst  |-> i,
                                  status|-> "accepted",
                                  ballot|-> rec.ballot,
                                  cmd   |-> acc.cmd,
                                  deps  |-> acc.deps,
                                  seq   |-> acc.seq]}]
                         /\ preparing' = [preparing EXCEPT ![replica] = @ \ {i}]
                         /\ leaderOfInst' = [leaderOfInst EXCEPT ![replica] = @ \cup {i}]
                         /\ UNCHANGED << proposed, executed, crtInst, committed, ballots, sentMsgPreAccept, sentMsgCommit, sentMsgPrepare, sentMsgPreAcceptReply, sentMsgAcceptReply, sentMsgTryPreAccept, sentMsgTryPreAcceptReply >>
                \/ /\ ~(\E msg \in replies :
                        msg.status \in {"accepted", "committed", "executed"})
                   /\ LET preaccepts == {msg \in replies : msg.status = "pre-accepted"} IN
                       (\/  /\ \A p1, p2 \in preaccepts :
                                    p1.cmd = p2.cmd /\ p1.deps = p2.deps /\ p1.seq = p2.seq
                            /\ ~(\E pl \in preaccepts : pl.src = i[1])
                            /\ Cardinality(preaccepts) >= Cardinality(Q) - 1
                            /\ LET pac == CHOOSE pacTemp \in preaccepts : TRUE IN
                                /\ sentMsgPrepareReply' = sentMsgPrepareReply \ replies
                                /\ sentMsgAccept' = sentMsgAccept \cup
                                         ([type  : {"accept"},
                                          src   : {replica},
                                          dst   : Q \ {replica},
                                          inst  : {i},
                                          ballot: {rec.ballot},
                                          cmd   : {pac.cmd},
                                          deps  : {pac.deps},
                                          seq   : {pac.seq}])
                                /\ cmdLog' = [cmdLog EXCEPT ![replica] = (@ \ {rec}) \cup
                                        {[inst  |-> i,
                                          status|-> "accepted",
                                          ballot|-> rec.ballot,
                                          cmd   |-> pac.cmd,
                                          deps  |-> pac.deps,
                                          seq   |-> pac.seq]}]
                                 /\ preparing' = [preparing EXCEPT ![replica] = @ \ {i}]
                                 /\ leaderOfInst' = [leaderOfInst EXCEPT ![replica] = @ \cup {i}]
                                 /\ UNCHANGED << proposed, executed, crtInst, committed, ballots, sentMsgPreAccept, sentMsgCommit, sentMsgPrepare, sentMsgPreAcceptReply, sentMsgAcceptReply, sentMsgTryPreAccept, sentMsgTryPreAcceptReply >>
                        \/  /\ \A p1, p2 \in preaccepts : p1.cmd = p2.cmd /\
                                                          p1.deps = p2.deps /\
                                                          p1.seq = p2.seq
                            /\ ~(\E pl \in preaccepts : pl.src = i[1])
                            /\ Cardinality(preaccepts) < Cardinality(Q) - 1
                            /\ Cardinality(preaccepts) >= Cardinality(Q) \div 2
                            /\ LET pac == CHOOSE pacTemp \in preaccepts : TRUE IN
                                /\ sentMsgPrepareReply' = sentMsgPrepareReply \ replies
                                /\ sentMsgTryPreAccept' = sentMsgTryPreAccept \cup
                                         ([type  : {"try-pre-accept"},
                                          src   : {replica},
                                          dst   : Q,
                                          inst  : {i},
                                          ballot: {rec.ballot},
                                          cmd   : {pac.cmd},
                                          deps  : {pac.deps},
                                          seq   : {pac.seq}])
                                /\ preparing' = [preparing EXCEPT ![replica] = @ \ {i}]
                                /\ leaderOfInst' = [leaderOfInst EXCEPT ![replica] = @ \cup {i}]
                                /\ UNCHANGED << cmdLog, proposed, executed,
                                                crtInst, committed, ballots, sentMsgPreAccept, sentMsgAccept, sentMsgCommit, sentMsgPrepare, sentMsgPreAcceptReply, sentMsgAcceptReply, sentMsgTryPreAcceptReply >>
                        \/  /\ \/ \E p1, p2 \in preaccepts : p1.cmd # p2.cmd \/
                                                             p1.deps # p2.deps \/
                                                             p1.seq # p2.seq
                               \/ \E pl \in preaccepts : pl.src = i[1]
                               \/ Cardinality(preaccepts) < Cardinality(Q) \div 2
                            /\ preaccepts # ({})
                            /\ LET pac == CHOOSE pacTemp \in preaccepts : pacTemp.cmd # none IN
                                /\ StartPhase1SentMsgPrepareReply(pac.cmd, replica, Q, i, rec.ballot, replies)
                                /\ preparing' = [preparing EXCEPT ![replica] = @ \ {i}]
                                /\ UNCHANGED << proposed, executed, crtInst, committed, ballots, sentMsgAccept, sentMsgCommit, sentMsgPrepare, sentMsgPreAcceptReply, sentMsgAcceptReply, sentMsgTryPreAccept, sentMsgTryPreAcceptReply >>)
                \/  /\ \A msg \in replies : msg.status = "not-seen"
                    /\ StartPhase1SentMsgPrepareReply(none, replica, Q, i, rec.ballot, replies)
                    /\ preparing' = [preparing EXCEPT ![replica] = @ \ {i}]
                    /\ UNCHANGED << proposed, executed, crtInst, committed, ballots, sentMsgAccept, sentMsgCommit, sentMsgPrepare, sentMsgPreAcceptReply, sentMsgAcceptReply, sentMsgTryPreAccept, sentMsgTryPreAcceptReply >>

ReplyTryPreaccept(replica) ==
    \E tpa \in sentMsgTryPreAccept :
        /\ tpa.type = "try-pre-accept"
        /\ tpa.dst = replica
        /\ LET oldRec == {rec \in cmdLog[replica] : rec.inst = tpa.inst} IN
            /\ \A rec \in oldRec : rec.ballot[1] <= tpa.ballot[1] /\
                                   rec.status \notin {"accepted", "committed", "executed"}
            /\ \/ (\E rec \in cmdLog[replica] \ oldRec:
                        /\ tpa.inst \notin rec.deps
                        /\ \/ rec.inst \notin tpa.deps
                           \/ rec.seq >= tpa.seq
                        /\ sentMsgTryPreAccept' = sentMsgTryPreAccept \ {tpa}
                        /\ sentMsgTryPreAcceptReply' = sentMsgTryPreAcceptReply \cup
                                    {[type  |-> "try-pre-accept-reply",
                                      src   |-> replica,
                                      dst   |-> tpa.src,
                                      inst  |-> tpa.inst,
                                      ballot|-> tpa.ballot,
                                      status|-> rec.status]} )
                        /\ UNCHANGED << cmdLog, proposed, executed, committed, crtInst,
                                        ballots, leaderOfInst, preparing, sentMsgPreAccept, sentMsgAccept, sentMsgCommit, sentMsgPrepare, sentMsgPreAcceptReply, sentMsgAcceptReply, sentMsgPrepareReply >>
               \/ /\ (\A rec \in cmdLog[replica] \ oldRec:
                            tpa.inst \in rec.deps \/ (rec.inst \in tpa.deps /\
                                                      rec.seq < tpa.seq))
                  /\ sentMsgTryPreAccept' = sentMsgTryPreAccept \ {tpa}
                  /\ sentMsgTryPreAcceptReply' = sentMsgTryPreAcceptReply \cup
                                    {[type  |-> "try-pre-accept-reply",
                                      src   |-> replica,
                                      dst   |-> tpa.src,
                                      inst  |-> tpa.inst,
                                      ballot|-> tpa.ballot,
                                      status|-> "OK"]}
                  /\ cmdLog' = [cmdLog EXCEPT ![replica] = (@ \ oldRec) \cup
                                    {[inst  |-> tpa.inst,
                                      status|-> "pre-accepted",
                                      ballot|-> tpa.ballot,
                                      cmd   |-> tpa.cmd,
                                      deps  |-> tpa.deps,
                                      seq   |-> tpa.seq]}]
                  /\ UNCHANGED << proposed, executed, committed, crtInst, ballots,
                                  leaderOfInst, preparing, sentMsgPreAccept, sentMsgAccept, sentMsgCommit, sentMsgPrepare, sentMsgPreAcceptReply, sentMsgAcceptReply, sentMsgPrepareReply >>


FinalizeTryPreAccept(cleader, i, Q) ==
    \E rec \in cmdLog[cleader]:
        /\ rec.inst = i
        /\ LET tprs == {msg \in sentMsgTryPreAcceptReply : msg.type = "try-pre-accept-reply" /\
                            msg.dst = cleader /\ msg.inst = i /\
                            msg.ballot = rec.ballot} IN
            /\ \A r \in Q: \E tpr \in tprs : tpr.src = r
            /\ \/ /\ \A tpr \in tprs: tpr.status = "OK"
                  /\ sentMsgTryPreAcceptReply' = sentMsgTryPreAcceptReply \ tprs
                  /\ sentMsgAccept' = sentMsgAccept \cup
                             ([type  : {"accept"},
                              src   : {cleader},
                              dst   : Q \ {cleader},
                              inst  : {i},
                              ballot: {rec.ballot},
                              cmd   : {rec.cmd},
                              deps  : {rec.deps},
                              seq   : {rec.seq}])
                  /\ cmdLog' = [cmdLog EXCEPT ![cleader] = (@ \ {rec}) \cup
                            {[inst  |-> i,
                              status|-> "accepted",
                              ballot|-> rec.ballot,
                              cmd   |-> rec.cmd,
                              deps  |-> rec.deps,
                              seq   |-> rec.seq]}]
                  /\ UNCHANGED << proposed, executed, committed, crtInst, ballots,
                                  leaderOfInst, preparing, sentMsgPreAccept, sentMsgCommit, sentMsgPrepare, sentMsgPreAcceptReply, sentMsgAcceptReply, sentMsgPrepareReply, sentMsgTryPreAccept >>
               \/ /\ \E tpr \in tprs: tpr.status \in {"accepted", "committed", "executed"}
                  /\ StartPhase1SentMsgTryPreAcceptReply(rec.cmd, cleader, Q, i, rec.ballot, tprs)
                  /\ UNCHANGED << proposed, executed, committed, crtInst, ballots,
                                  preparing, sentMsgAccept, sentMsgCommit, sentMsgPrepare, sentMsgPreAcceptReply, sentMsgAcceptReply, sentMsgPrepareReply, sentMsgTryPreAccept >>
               \/ /\ \E tpr \in tprs: tpr.status = "pre-accepted"
                  /\ \A tpr \in tprs: tpr.status \in {"OK", "pre-accepted"}
                  /\ sentMsgTryPreAcceptReply' = sentMsgTryPreAcceptReply \ tprs
                  /\ leaderOfInst' = [leaderOfInst EXCEPT ![cleader] = @ \ {i}]
                  /\ UNCHANGED << cmdLog, proposed, executed, committed, crtInst,
                                  ballots, preparing, sentMsgPreAccept, sentMsgAccept, sentMsgCommit, sentMsgPrepare, sentMsgPreAcceptReply, sentMsgAcceptReply, sentMsgPrepareReply, sentMsgTryPreAccept >>



(***************************************************************************)
(* Action groups                                                           *)
(***************************************************************************)

CommandLeaderAction ==
    \/ (\E C \in (Commands \ proposed) :
            \E cleader \in Replicas : Propose(C, cleader))
    \/ (\E cleader \in Replicas : \E inst \in leaderOfInst[cleader] :
            \/ (\E Q \in FastQuorums(cleader) : Phase1Fast(cleader, inst, Q))
            \/ (\E Q \in SlowQuorums(cleader) : Phase1Slow(cleader, inst, Q))
            \/ (\E Q \in SlowQuorums(cleader) : Phase2Finalize(cleader, inst, Q))
            \/ (\E Q \in SlowQuorums(cleader) : FinalizeTryPreAccept(cleader, inst, Q)))

ReplicaAction ==
    \E replica \in Replicas :
        (\/ Phase1Reply(replica)
         \/ Phase2Reply(replica)
         \/ \E cmsg \in sentMsgCommit : (cmsg.type = "commit" /\ Commit(replica, cmsg))
         \/ \E i \in Instances :
            /\ crtInst[i[1]] > i[2] (* This condition states that the instance has *)
                                    (* been started by its original owner          *)
            /\ \E Q \in SlowQuorums(replica) : SendPrepare(replica, i, Q)
         \/ ReplyPrepare(replica)
         \/ \E i \in preparing[replica] :
            \E Q \in SlowQuorums(replica) : PrepareFinalize(replica, i, Q)
         \/ ReplyTryPreaccept(replica))


(***************************************************************************)
(* Next action                                                             *)
(***************************************************************************)

Next ==
    \/ CommandLeaderAction
    \/ ReplicaAction


(***************************************************************************)
(* The complete definition of the algorithm                                *)
(***************************************************************************)

Spec == Init /\ [][Next]_vars


(***************************************************************************)
(* Theorems                                                                *)
(***************************************************************************)

Nontriviality ==
    \A i \in Instances :
        [](\A C \in committed[i] : C[1] \in proposed \/ C[1] = none)

Stability ==
    \A replica \in Replicas :
        \A i \in Instances :
            \A C \in Commands :
                []((\E rec1 \in cmdLog[replica] :
                    /\ rec1.inst = i
                    /\ rec1.cmd = C
                    /\ rec1.status \in {"committed", "executed"}) =>
                    [](\E rec2 \in cmdLog[replica] :
                        /\ rec2.inst = i
                        /\ rec2.cmd = C
                        /\ rec2.status \in {"committed", "executed"}))

Consistency ==
    \A i \in Instances :
        [](Cardinality(committed[i]) <= 1)

THEOREM Spec => ([]TypeOK) /\ Nontriviality /\ Stability /\ Consistency

\* APALACHE
\* Consistency rewritten as a state invariant
ConsistencyAsInv ==
    \A i \in Instances: \A c, d \in committed[i]: c = d

\* We use this state invariant to find the first commit
NoCommits == \A i \in Instances: committed[i] = {}






=============================================================================
\* Modification History
\* Last modified Sat Mar 30 12:52:55 CET 2019 by igor
\* Last modified Sat Aug 24 12:25:28 EDT 2013 by iulian
\* Created Tue Apr 30 11:49:57 EDT 2013 by iulian
