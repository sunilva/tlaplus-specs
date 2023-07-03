------------------------ MODULE ViewStampReplication ------------------------
(*  
    paper: https://pmg.csail.mit.edu/papers/vr-revisited.pdf
    
    VSR is an algorithm for implementing state machine replication. The group of replicas elect one replica 
    as a primary which handles requests from clients & replicates the same among the replicas. Once a request 
    is replicated to a majority of replicas then it is safe to be executed by the state machine. Given 2F+1 replicas
    VSR can sustain upto to F failures. 
    
    VSR is divided into 4 subprotocols: 
    - Normal operation for replica co-ordination
    - View change for handling primary failure
    - Recovery for enabling failed replica(restart) to rejoin the replica group
    - Reconfiguration for changing replica group membership 
        - replace faulty replica
        - increase/decrease no. replicas in the replica group
    - VSR assumes independent replica failure & doesn't need disk, instead replicas(after restart) get
      the latest system state from other replicas. 
    Replicas will be in one of the four states viz. normal, view-change, recovery, reconfiguration 
    depending on the sub-protocol in which they are operating.
    
    All messages sent from primary to backup replicas carry view number & epoch number, view number determines 
    primary & epoch number abstracts the replica group configuration. 
    
    Whenever the primary fails(backup replicas stop receiving heart beat messages from the primary) the 
    system goes through a view change electing another replica as a new primary. A group of replicas within 
    same view co-ordinate replication otherwise the requests from the primary are ignored. 
    
    If system needs to decrease/increase no. of replicas or replace a replica in the system then it goes 
    through an epoch change.
    
    Replicated Log:
        Log on each replica appears as shown in the diagram below.
        - epoch-no:   epoch number abstracts system configuration, if replicas present in system change 
                      then system goes through a epoch change.    
        - view-no:    view number abstracts failure(primary replica changes), if a primary fails then 
                      the system goes through a view change. 
        - op-no:      it's an index for a slot in the log, each slot contains one request or command. 
        - commit-no:  identifies the op-no upto which the state machine has consumed the input reqests or commands.
        
        |<=======================================time=====================================>|    
        |<~~~~~~~~~~~~~e1~~~~~~~~~~~>|<~~~~~~~~~~~~~~~~~~~~~~~e2~~~~~~~~~~~~~~~~~~~~~~~~~~>|
        |<----v1---->|<------v2----->|<---v3-->|<----v4---->|<-------------v5------------->|
        |<a><b><c><d>|<e><f><g><h><i>|<j><k><l>|<m><n><o><p>|<q><r><s><t><u><v><w><x><y><z>|
            
        en: epoch-no
        vn: view-no
        <.>: operations or command            
         
        This TLA+ spec implements normal & view-change sub-protocols. 
        
        Normal Operation: PREPARE, COMMIT & GET-STATE(not implemented) 
        * Primary & backup replicas take part in replication if they are part of the same view 
          & their status is normal. Messages sent from primary to backup contain view-number.
        * Primary takes input requests from the clients & replicates it to the backup replicas by sending 
          PREPARE message to the replicas.Backup replica adds request to its log & advances op-no.
        * Once primary receives a quorum of replies(including itself), it applies the request to the state machine. 
          This is called commit & commit-no gets incremented.
        * The primary also instructs the replicas to apply the request by sending a COMMIT message.
            
        View Change Operation: StartViewChange(SVC), DoViewChange(DVC) & StartView(SV)
        * If backup replicas stop receiving heart beat messages then they change their state to view-change & start
          SVC broadcast message among themselves.
        * Once a replica receives a quorum of SVC messages it sends a DVC message containing its log to the new primary.
        * Once the new primary receives at least a quorum of DVC messages, it consolidates all the logs 
          received in the SVC messages & sends a SV message to the replicas. The correctness condition for log 
          consolidation is that no committed requests are lost.
        * The log for all replicas is reinitialized with the log contained in the SV message.
        
        Safety condition: As soon as replica enters view-change state they stop accepting PREPARE messages, otherwise 
        old primary(slow) would get ACKs & thus commit a request while new primary is not sent these new requests in DVC message.
        
        Recovery: TODO
        Reconfiguration: TODO
        
    Note: 
    Above description is only a brief explanation of the VSR algorithm, for complete description the paper 
    should be referred.
    
    Message:     
    - message duplication(can simply be implemmented by not dropping delivered messages, Lamport uses this approach) 
      & loss are not implemented
    - delay & out-of-order delivery is achieved using TLA \E construct
    
    Replica:
    - recovery & reconfig sub-protocols are not implemented
    - getState is not implemented, it is triggered by backup replicas to fetch latest state from other replicas
        * get-state is used by lagging replicas comes into picture in the following scenarios 
            * replica receives PREPARE msg wherein msg(op-no) > replica-log(op-no) + 1
            * replica receives PREPARE msg with view-no greater than it's view-no.  
            * replica receives COMMIT msg wherein commit-no > op-no.

    Commit index can go backwards:
    - Primary receives a quorum of responses & advances the commit index, soon after this
      primary crashes & another replica is elected as primary. 
    - Obviously, newly elected leader's commit index would be lesser than 
      the previous primary's commit index.
    - At this point primary comes back online(din't crash) & receives SV message from 
      new primary, thus it's commit index goes backwards.
         
    To handle this situation, the operations applied to app state must be made idempotent or 
    a condition can be added to increase commit index monotonically(as done in this spec).      
    
    Network partition scenario:
    - Consider a network partition situation wherein there are a quorum of replicas in one partition &
      the remaining replicas are in another partition. 
    - The non-quorum replicas get into view-change status as they don't receive heart beat messages
      from the primary.
    - Since the replicas don't receive a quorum of SVC messages their view-no doesn't advance. 
    - When the network partition heals their SVC messages will continue to be discarded if the view-no 
      is lesser than the view-no of the quorum replicas.
        
    They can rejoin the quorum replica group if they do a get-state operation after receiving a PREPARE msg from 
    the primary but this is not explicitly stated in the paper, especially given that their current status 
    is view-change the PREPARE msg might get silently ignored. 
                  
    specific implementation notes: 
    - failed primary is not included in SVC & DVC messaging but is sent SV message after completing SVC & DVC messaging
    - client & SM interaction are left out to keep model simple & state space size limited
    - commit messages are sent after receiving prepare-ok messages from backups i.e not periodically   

    Short intro to TLA+:
    - Computation model: 
       - state = assignment of values to variables
       - behavior = state transitions, there can be many, many possible behviors
       - algorithm = all possible set of behaviors
    - Solution(algorithm) expressed as spec(state transitions) is fed to the TLC model checker. TLC model
      checker generates(state space exploration) behaviors using the spec & the behaviors are validated against
      the safety & liveness properties.    

                     +-----------+
        spec     --->| TLC model |===> behavior violating safety or liveness properties
        safety   --->| checker   |     Or 
        liveness --->|           |===> state space exploration completed, successfully       
                     +-----------+   
*)

(* 
    Tested using the following model:
    * request: {1,2,3}, replicaCount: 3, viewChangeTriggerLimit: 0 state space size: 3M
    * request: {1,2},   replicaCount: 3, viewChangeTriggerLimit: 1 state space size: 1M
    * request: {1,2,3}, replicaCount: 3, viewChangeTriggerLimit: 1 state space size: 205M   
    * request: {1,2},   replicaCount: 3, viewChangeTriggerLimit: 2 state space size: 44M 
    
    Notes:
    * NIL is a model value
    * Uncheck deadlock from the model definition
    
    Tips:
    * Run the model without checking any safety & liveness properties, this will give an idea about 
      the size of the state space. 
    * Once you the state space size check for safety properties followed by liveness properties.  
    * Checkout https://vimeo.com/264959035
*)

(*
Conclusion: 
TLA+ is an excellent tool to mechanically check concurrent executions since it exhaustively 
checks all possible executions. It is very difficult to reason about all possible concurrent executions, 
like all possible interleavings of SVC, DVC & SV messages during a view-change.

However the complete state space exploration for concurrent executions also means that the 
model can only checked for small model sizes.

*)
EXTENDS Integers, FiniteSets, TLC, Naturals, Sequences 

CONSTANTS request, viewChangeTriggerLimit, replicaCount, NIL

VARIABLES
    replicas,
    (*
        Instead of having multiple variables(like status, view etc) have one record for reach replica, 
        this is what pluscal does w.r.t it's process abstraction.Pluscal provides process abstraction along with 
        local variables which are not visible outside of the process, accessible with self as domain variable.
        - better encapsulation with state being modeled as record per replica
        - avoids shared memory style of access
        - shorter UNCHANGED variables listings 

        function with domain as replica, gives record containing following fields
        - old_config    -> {replicas}, currently unused
        - config        -> {replicas}, currently unused
        - status        -> {"normal", "view-change", "recovering", "reconfig"}
        - log           -> << >> contains client request entries which will be applied to SM
        - epoch         -> Nat, currently unused
        - view          -> Nat
        - op_no         -> Nat (initialized to zero)
        - commit_no     -> Nat (initialized to zero)
        - last_normal_view  -> Nat, view changes can be discontinuous(because next primary can be down)  
                               since replicas build one log entry at a time, it is sufficient to store only 
                               highest op_no recvd in PREPAREOK msgs
        - svc_msgs_recvd    -> {replica}, size of(svc_msgs)  gives no. of svc msgs received, also accounts for duplicate msgs
        - dvc_msgs_recvd    -> [r |-> [l, v, v', n, k]], l = log, v = new view, v' = last_normal_view, n = op_no, k = commit_no  
    *)
    replicaState,
    (*
        - function with domain as msg & count as range
        - messages can be duplicated, delayed, dropped & delivered out-of-order
        
        - delayed & out-of-order delivery: use \E TLA construct 
        - dropped: reduce count 
        - duplicate: increase count
        note: deliver a msg if count > 0
    *)
    messages,
    (*  set of operations to be to the replicated state machine *)
    aux_req, 
    (*  no. of view changes to be triggered *)
    aux_vc_limit
-----------------------------------------------------------------------------------------------------------------------------------------------------
\*replicaCount == Cardinality(replicas)
quorumCount == (replicaCount \div 2) + 1
Size(arg_set) == Cardinality(arg_set)
\* subsets consisting majority of replicas
Quorum == {r \in SUBSET(replicas): Size(r)*2 > replicaCount } 

Max(a, b) == IF a > b THEN a ELSE b
Min(a, b) == IF a < b THEN a ELSE b

\* Helper operators
state(r)    == replicaState[r]
oldConfig(r)== replicaState[r].old_config
config(r)   == replicaState[r].config
status(r)   == replicaState[r].status
epoch(r)    == replicaState[r].epoch  
view(r)     == replicaState[r].view
opNo(r)     == replicaState[r].op_no
log(r)      == replicaState[r].log
commitNo(r) == replicaState[r].commit_no
prepareOk(r)== replicaState[r].prepare_ok
rcvdSvcMsgs(r)  == replicaState[r].svc_msgs_recvd
dvcMsgs(r)  == replicaState[r].dvc_msgs_recvd
lastNormalView(r) == replicaState[r].last_normal_view

PrimaryForView(v) == (v % replicaCount) + 1
IsStatusNormal(r) == status(r) = "normal"
IsPrimary(r, arg_view) == (*/\ status(r) = "normal" /\ *)(arg_view % replicaCount) + 1 = r
-----------------------------------------------------------------------------------------------------------------------------------------------------
Update(replica, field, value) == 
    replicaState' = [replicaState EXCEPT ![replica][field] = value ]

Update2(replica, f1, v1, f2, v2) == 
    replicaState' = [replicaState EXCEPT ![replica][f1] = v1,
                                         ![replica][f2] = v2 ]

Update3(replica, f1, v1, f2, v2, f3, v3) == 
    replicaState' = [replicaState EXCEPT ![replica][f1] = v1,
                                         ![replica][f2] = v2,
                                         ![replica][f3] = v3 ]

Update4(replica, f1, v1, f2, v2, f3, v3, f4, v4) == 
    replicaState' = [replicaState EXCEPT ![replica][f1] = v1,
                                         ![replica][f2] = v2,
                                         ![replica][f3] = v3, 
                                         ![replica][f4] = v4]

Update5(replica, f1, v1, f2, v2, f3, v3, f4, v4, f5, v5) == 
    replicaState' = [replicaState EXCEPT ![replica][f1] = v1,
                                         ![replica][f2] = v2,
                                         ![replica][f3] = v3, 
                                         ![replica][f4] = v4,
                                         ![replica][f5] = v5]

Update6(replica, f1, v1, f2, v2, f3, v3, f4, v4, f5, v5, f6, v6) == 
    replicaState' = [replicaState EXCEPT ![replica][f1] = v1,
                                         ![replica][f2] = v2,
                                         ![replica][f3] = v3, 
                                         ![replica][f4] = v4,
                                         ![replica][f5] = v5,
                                         ![replica][f6] = v6]                                                                                  
-----------------------------------------------------------------------------------------------------------------------------------------------------
getLogEntry(r, req) == [ epoch |-> epoch(r), view |-> view(r), op_no |-> opNo(r) + 1, req |-> req ]

AddEntryToPrimaryLog(r, req) == 
    replicaState' = [replicaState EXCEPT ![r].log = Append(@, getLogEntry(r, req)),
                                         ![r].op_no = @ + 1, 
                                         ![r].prepare_ok[r] = @ + 1]
AddEntryToBackupLog(r, msg) == 
    replicaState' = [replicaState EXCEPT ![r].log = Append(@, getLogEntry(r, msg.req)),
                                         ![r].op_no = @ + 1,
                                         ![r].commit_no = IF msg.cmt_no > @ THEN msg.cmt_no ELSE @]
 
LastLogEntry(r) == LET replicaLog == state(r).log
                       len == Len(replicaLog)
                   IN  IF len > 0 THEN replicaLog[len] ELSE NIL
                            
PreviousLogEntryExists(r, msg_op_no) == LET last_entry == LastLogEntry(r)  
                                        IN  IF last_entry = NIL
                                            THEN msg_op_no = 1 
                                            ELSE last_entry.op_no = (msg_op_no - 1)
                                            
UpdatePrepareOkField(r, msg) == [prepareOk(r) EXCEPT ![msg.from] = IF msg.op_no > @ THEN msg.op_no ELSE @] 

GetQuorumValue(prepare_ok, from, msg_op_no) == LET updated_prep_ok == [prepare_ok EXCEPT ![from] = Max(prepare_ok[from], msg_op_no)]
                                                   \* prepare_ok would get updated in next state, 
                                                   \* so consider op_no received in prep_ok msg for commit advancement
                                                   sorted_prep_ok == SortSeq(updated_prep_ok, <)
                                               IN  sorted_prep_ok[quorumCount]
                                               
UpdatePrepareOkReply(r, msg) == 
    replicaState' = [replicaState EXCEPT ![r].prepare_ok = UpdatePrepareOkField(r, msg),
                                         ![r].commit_no  = GetQuorumValue(prepareOk(r), msg.from, msg.op_no) ]    
                                         
UpdateCommitNo(r, cmt_no) == replicaState' = [replicaState EXCEPT ![r].commit_no = IF cmt_no > @ THEN cmt_no ELSE @ ]
-----------------------------------------------------------------------------------------------------------------------------------------------------
AddMsg(msg, buf_msgs) ==    IF msg \in DOMAIN buf_msgs 
                            THEN [buf_msgs EXCEPT ![msg] = @ + 1]
                            ELSE buf_msgs @@ (msg :> 1) 

RemoveMsg(msg, buf_msgs) == IF msg \in DOMAIN buf_msgs 
                            THEN [buf_msgs EXCEPT ![msg] = @ - 1]
                            ELSE buf_msgs
                             
IsMsgDeliverable(msg) == messages[msg] > 0 
Duplicate(msg)  == messages' = AddMsg(msg, messages)
Drop(msg)       == messages' = RemoveMsg(msg, messages)

Send(msg)       == messages' = AddMsg(msg, messages)
SendAndDrop(send_msg, drop_msg)  == messages' = AddMsg(send_msg, RemoveMsg(drop_msg, messages))

\* Unlike Send & SendAndDrop Broadcast resets msg count to 1, this is done to keep implementation simple
Broadcast(bcast_msgs) == messages'= messages @@ [m \in bcast_msgs |-> 1]
BroadcastAndDrop(bcast_msgs, drop_msg) == messages' = [messages EXCEPT ![drop_msg] = @-1] @@ [m \in bcast_msgs |-> 1 ]
-----------------------------------------------------------------------------------------------------------------------------------------------------
(* Normal operation *)
commitMsgs(r) == { 
                     [
                        type    |-> "commit",
                        epoch   |-> epoch(r), 
                        view    |-> view(r),
                        cmt_no  |-> commitNo(r),
                        from    |-> r,
                        to      |-> i
                     ] : i \in replicas \ {r} 
                 }
                                 
PrepareOkMsg(r, msg) == [
                            type    |-> "prepare-ok",  
                            epoch   |-> msg.epoch,
                            view    |-> msg.view,
                            op_no   |-> msg.op_no,
                            from    |-> msg.to,
                            to      |-> msg.from
                        ]
                        
BackupRecvCommitMsg(r, msg) == \/ /\ epoch(r) = msg.epoch
                                  /\ view(r) = msg.view
                                  /\ status(r) = "normal"
                                  /\ UpdateCommitNo(r, msg.cmt_no) \* if commit_no in msg is greater than op_no in log then do get-state(TODO)
                                  /\ Drop(msg)
                                  /\ UNCHANGED << replicas, aux_req, aux_vc_limit >> 
                               \* replica is lagging, TODO: implement get-state
                                                         
BackupRecvPrepareMsg(r, msg) == \/ /\ epoch(r) = msg.epoch                
                                   /\ view(r) = msg.view
                                   /\ status(r) = "normal"
                                   /\ PreviousLogEntryExists(r, msg.op_no)
                                   /\ AddEntryToBackupLog(r, msg)
                                   /\ SendAndDrop(PrepareOkMsg(r, msg), msg)
                                   /\ UNCHANGED << replicas, aux_req, aux_vc_limit >>
                                \* replica is lagging, TODO: implement get-state
                                    
PrimaryRecvPrepareOkMsg(r, msg) == \/ /\ epoch(r) = msg.epoch     
                                      /\ view(r) = msg.view
                                      /\ IsPrimary(r, view(r))
                                      /\ IsStatusNormal(r)
                                      /\ UpdatePrepareOkReply(r, msg)
                                      /\ BroadcastAndDrop(commitMsgs(r), msg)
                                      /\ UNCHANGED << replicas, aux_req, aux_vc_limit >>  
-----------------------------------------------------------------------------------------------------------------------------------------------------
SVCMsgs(r, msg) == {
                        [
                            type    |-> "svc",
                            epoch   |-> msg.epoch,
                            view    |-> msg.view,
                            from    |-> r,
                            to      |-> i 
                        ]: i \in replicas \ {r, PrimaryForView(msg.view-1)}
                  }

DVCMsg(r) == [
                type    |-> "dvc",
                epoch   |-> epoch(r),
                view    |-> view(r), 
                from    |-> r,
                to      |-> PrimaryForView(view(r)), \* new primary
                replica_state |-> [ l     |-> log(r), 
                                    v     |-> view(r),
                                    lnv   |-> lastNormalView(r),
                                    n     |-> opNo(r),
                                    k     |-> commitNo(r)]
            ]
            
SVMsgs(r, log_details) == {
                                [
                                    type    |-> "sv",
                                    epoch   |-> epoch(r),
                                    view    |-> log_details["v"],
                                    log     |-> log_details["l"],
                                    op_no   |-> log_details["n"],
                                    cmt_no  |-> log_details["k"],
                                    from    |-> r,
                                    to      |-> i
                                ]: i \in replicas \ {r}
                           }
-----------------------------------------------------------------------------------------------------------------------------------------------------
(* View change operation *)
ReplicaRecvSVCMsg(r, msg) == \/ /\ view(r) < msg.view
                                /\ Update5(r,
                                    "view", msg.view,
                                    "status", "view-change",
                                    "svc_msgs_recvd", {r, msg.from}, \* reset for new view, add self 
                                    "last_normal_view", IF status(r) = "normal" THEN view(r) ELSE lastNormalView(r),
                                    "dvc_msgs_recvd", << >>) \* fixes crucial concurrency issue
                                /\ BroadcastAndDrop(SVCMsgs(r, msg) , msg)
                                /\ UNCHANGED << replicas, aux_req, aux_vc_limit >>  
                             \/ /\ view(r) = msg.view 
                                /\ Update(r, "svc_msgs_recvd", (rcvdSvcMsgs(r) \cup {msg.from}))
                                /\ Drop(msg)
                                /\ UNCHANGED << replicas, aux_req, aux_vc_limit >> 

StoreDVCMsg(r, msg) == 
    replicaState' = [ replicaState EXCEPT ![r]["dvc_msgs_recvd"] = @ @@ msg.from :> msg.replica_state]

(* Cases: 
    - replica is not part of SVC messaging i.e replica receives DVC message without receiving any prior SVC msg(view-no is not updated view(r) < msg.view)
    - replica has received prior svc messages
    - replica receives multiple dvc messages for the same view-no 
*) 
ReplicaRecvDVCMsg(r, msg) == \/ /\ view(r) < msg.view \* new DVC msg without being part of prior SVC messaging
                                /\ status(r) = "normal"
                                /\ Update4(r, 
                                        "view", msg.view,
                                        "status", "view-change",
                                        "last_normal_view", view(r), 
                                        "dvc_msgs_recvd", msg.from :> msg.replica_state) \*resetDVC(r, msg))
                                /\ Drop(msg)
                                /\ UNCHANGED << replicas, aux_req, aux_vc_limit >>        
                             \/ /\ view(r) = msg.view
                                /\ status(r) = "view-change" 
                                /\ StoreDVCMsg(r, msg)
                                /\ Drop(msg)          
                                /\ UNCHANGED << replicas, aux_req, aux_vc_limit >>
                                
ReplicaRecvSVMsg(r, msg) == \/ /\ view(r) <= msg.view \* replica might not be part of svc/dvc messaging, hence < condition 
                               /\ Update6(r, 
                                    "status", "normal",
                                    "view", msg.view, \* some replicas might not be part of svc messaging
                                    "log",  msg.log,
                                    "op_no", msg.op_no,
                                    "commit_no", IF msg.cmt_no > commitNo(r) THEN msg.cmt_no ELSE commitNo(r),
                                    "dvc_msgs_recvd", << >>) \* fixes crucial concurrency issue
                               /\ SendAndDrop(PrepareOkMsg(r, msg), msg)     
                               /\ UNCHANGED << replicas, aux_req, aux_vc_limit >>

-----------------------------------------------------------------------------------------------------------------------------------------------------
ReplicaSendDVCMsg(r) == /\ Size(rcvdSvcMsgs(r)) >= quorumCount 
                        /\ Send(DVCMsg(r))
                        /\ Update(r, "svc_msgs_recvd", {}) \* reset
                        /\ UNCHANGED << replicas, aux_req, aux_vc_limit >>
                        
ConsolidateLogs(r) == LET dvc_msgs == dvcMsgs(r)
                          cmd_idx == CHOOSE i \in DOMAIN dvc_msgs: 
                                         \A j \in DOMAIN dvc_msgs: dvc_msgs[i]["k"] >= dvc_msgs[j]["k"]
                          
                          latest_log_idx == CHOOSE i \in DOMAIN dvc_msgs: 
                                                \A j \in DOMAIN dvc_msgs: \/ dvc_msgs[i]["lnv"] > dvc_msgs[j]["lnv"]
                                                                             \/ /\ dvc_msgs[i]["lnv"] = dvc_msgs[j]["lnv"]    
                                                                                /\ dvc_msgs[i]["n"] >= dvc_msgs[j]["n"]                                                    
                      IN  [ l |-> dvc_msgs[latest_log_idx]["l"],  
                            n |-> dvc_msgs[latest_log_idx]["n"],
                            v |-> dvc_msgs[latest_log_idx]["v"], 
                            k |-> dvc_msgs[cmd_idx]["k"] ]

ReplicaSendSVMsg(r) == /\ Size(DOMAIN dvcMsgs(r)) >= quorumCount  
                       /\ LET log_details == ConsolidateLogs(r)
                          IN /\ Update6(r,
                                    "status", "normal",
                                    "log", log_details.l,
                                    "op_no", log_details.n,
                                    "commit_no", log_details.k,
                                    "dvc_msgs_recvd", << >>, \* reset to empty function
                                    "prepare_ok", [ i \in replicas |-> IF i = r THEN log_details.n ELSE 0]) 
                             /\ Broadcast(SVMsgs(r, log_details))                                           
                             /\ UNCHANGED << replicas, aux_req, aux_vc_limit >>
-----------------------------------------------------------------------------------------------------------------------------------------------------
ProcessMsg(msg) == CASE msg.type = "prepare"    -> BackupRecvPrepareMsg(msg.to, msg)
                     [] msg.type = "prepare-ok" -> PrimaryRecvPrepareOkMsg(msg.to, msg)
                     [] msg.type = "commit"     -> BackupRecvCommitMsg(msg.to, msg)
                     [] msg.type = "svc"        -> ReplicaRecvSVCMsg(msg.to, msg)
                     [] msg.type = "dvc"        -> ReplicaRecvDVCMsg(msg.to, msg)
                     [] msg.type = "sv"         -> ReplicaRecvSVMsg(msg.to, msg)
                     [] OTHER -> /\ Drop(msg)
                                 /\ PrintT("@@@ ALERT! UNKOWN MESSAGE @@@")   
                                 /\ UNCHANGED << replicas, replicaState, aux_req, aux_vc_limit >>
-----------------------------------------------------------------------------------------------------------------------------------------------------
PrimarySendPrepareMsgs(r, op) == LET prepare_msgs ==  { 
                                                         [
                                                            type    |-> "prepare",
                                                            epoch   |-> epoch(r), 
                                                            view    |-> view(r),
                                                            op_no   |-> opNo(r) + 1,
                                                            req     |-> op,
                                                            cmt_no  |-> commitNo(r),
                                                            from    |-> r,
                                                            to      |-> i
                                                         ] : i \in replicas \ {r} 
                                                    }
                                 IN /\ Broadcast(prepare_msgs)

ClientRequest(r, op) == /\ IsPrimary(r, view(r))
                        /\ IsStatusNormal(r)
                        /\ AddEntryToPrimaryLog(r, op) 
                        /\ PrimarySendPrepareMsgs(r, op)
                        /\ aux_req' = aux_req \ {op}
                        /\ UNCHANGED << replicas, aux_vc_limit >>

NewViewSVCMsg(r) == 
    {
                [   
                    type    |-> "svc",
                    epoch   |-> epoch(r),
                    view    |-> view(r) + 1,
                    from    |-> r,
                    to      |-> i
                ]: i \in replicas \ {r, PrimaryForView(view(r))}
    }

TriggerViewChange(r) == /\ aux_vc_limit < viewChangeTriggerLimit
                        /\ Update5(r, 
                            "view", view(r) + 1,
                            "status", "view-change",
                            "last_normal_view", IF status(r) = "normal" THEN view(r) ELSE lastNormalView(r),
                            "svc_msgs_recvd", {r},
                            "dvc_msgs_recvd", << >>)
                        /\ Broadcast(NewViewSVCMsg(r))
                        /\ aux_vc_limit' = aux_vc_limit + 1
                        /\ UNCHANGED << replicas, aux_req >> 

-----------------------------------------------------------------------------------------------------------------------------------------------------   
InitReplicaState == 
    replicaState =
        [ 
            r \in 1..replicaCount |-> 
                               [ 
                                    old_config          |-> {},
                                    config              |-> {},
                                    status              |-> "normal",
                                    epoch               |-> 0,
                                    view                |-> 0,
                                    op_no               |-> 0,
                                    commit_no           |-> 0,
                                    last_normal_view    |-> 0,                                                
                                    log                 |-> << >>, 
                                    prepare_ok          |-> [ i \in 1..replicaCount |-> 0],
                                    svc_msgs_recvd      |-> {},
                                    dvc_msgs_recvd      |-> << >> (* empty function *) 
                               ]
        ]
        
Init == /\ InitReplicaState
        /\ replicas = {i: i \in 1..replicaCount}
        /\ messages = << >>
        /\ aux_req = request
        /\ aux_vc_limit = 0  

Next == \/ \E r \in replicas:\E op \in aux_req: ClientRequest(r, op) 
        \/ \E msg \in DOMAIN messages: /\ IsMsgDeliverable(msg)  
                                       /\ ProcessMsg(msg)
        \/ \E r \in replicas:          /\ ~IsPrimary(r, view(r))
                                       /\ TriggerViewChange(r)
                                       
        \/ \E r \in replicas:          /\ ReplicaSendDVCMsg(r)
        \/ \E r \in replicas:          /\ ReplicaSendSVMsg(r)
        
Spec == Init /\ [][Next]_<< replicas, replicaState, messages, aux_req, aux_vc_limit>> 
             /\ WF_<< replicas, replicaState, messages, aux_req, aux_vc_limit>>(Next) 

-----------------------------------------------------------------------------------------------------------------------------------------------------
(* Normal Operation: Safety & Liveness properties *)

(* safety: no log divergence 
    - during normal operation replica trails primary log(prefix match only)
    - during view-change(svc-dvc phase) logs can diverge, then get reconciled with a new SV message *)
ReplicatedLogPrefixMatch == \A r1,r2 \in replicas: LET min_len == Min(Len(log(r1)), Len(log(r2)))
                                                   IN \A i \in 1..min_len: (/\ status(r1)="normal" 
                                                                            /\ status(r2)="normal"
                                                                            /\ view(r1) = view(r2)) => log(r1)[i] = log(r2)[i]  
ReplicatedLogPrefixMatchProperty == []ReplicatedLogPrefixMatch

(* liveness: logs & commit-no match *)
ReplicatedLogsAndCommitNoAreSame == \A r1,r2 \in replicas: /\ log(r1) = log(r2)
                                                           /\ commitNo(r1) = commitNo(r2)
ReplicatedLogsAndCommitNoAreSameProperty == []<>ReplicatedLogsAndCommitNoAreSame
-----------------------------------------------------------------------------------------------------------------------------------------------------
(* View change Operation: Safety & Liveness properties *)

(* safety: committed entries are not lost during view-change
    - quorum of replicas contain log entries till the largest commit-no
    - some replicas can have commit_no > op_no(get-state is not yet implemented) *)
LargestCmtNo == LET largest_cmt_no_replica == 
                        CHOOSE r1 \in replicas: \A r2 \in replicas: commitNo(r1) >= commitNo(r2)
                IN commitNo(largest_cmt_no_replica)        

QuorumContainsLogEntries == \E q \in Quorum:
                                \A i \in 1..LargestCmtNo:
                                    \A r1,r2 \in q: /\ opNo(r1) >= LargestCmtNo \* log replication might not have happened for some replica
                                                    /\ opNo(r2) >= LargestCmtNo  
                                                    /\ log(r1)[i] = log(r2)[i]                
QuorumContainsLogEntriesProperty == []QuorumContainsLogEntries

(* safety:
    - commit-no increase monotonically implies 
        - log entries are applied to the state machine exactly once 
        - otherwise dedupe mechanism is required between VSR & SM *)
CommitNoMonotonicallyIncreases == \A r \in replicas: replicaState[r]'.commit_no >= replicaState[r].commit_no        
CommitNoMonotonicallyIncreasesProperty == [][CommitNoMonotonicallyIncreases]_<<replicaState>>

(* liveness:
    - eventually all replicas are in normal state *)
ReplicasAreInNormalState == \A r \in replicas: status(r) = "normal"
ReplicasAreInNormalStateProperty == []<>ReplicasAreInNormalState
-----------------------------------------------------------------------------------------------------------------------------------------------------
(* Invariance and Liveness properties for debugging purpose *)
AllMsgsEventuallyDelivered == \A msg \in DOMAIN messages: messages[msg] = 0 
AllMsgsEventuallyDeliveredProperty == []<>AllMsgsEventuallyDelivered

ViewMonotonicallyIncreases == \A r \in replicas: replicaState[r]'.view >= replicaState[r].view    
ViewMonotonicallyIncreasesProperty == [][ViewMonotonicallyIncreases]_<< replicaState>>

AllReqsAreCommitted == \A r \in replicas: state(r).commit_no = Cardinality(request)
AllReqsAreCommittedProperty == []<>AllReqsAreCommitted
=====================================================================================================================================================
\* Modification History
\* Last modified Mon Jul 03 13:28:46 IST 2023 by Dell
\* Created Tue Mar 14 13:17:10 IST 2023 by Dell