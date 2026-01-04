------------------------------ MODULE transaction_lifecycle ------------------------------
EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS Stores, Connections, Transactions, Versions
VARIABLES transactions, stores, pending_stores, connections, dbVersion, connection_queue
\* TLA+ model of the transaction lifecycle and scheduling rules from:
\* - <https://w3c.github.io/IndexedDB/#transaction-lifecycle>
\* - <https://w3c.github.io/IndexedDB/#transaction-scheduling>

\* Note: by using only a single dbVersion, we do not model multiple databases. 
Vars == << transactions, stores, pending_stores, connections, dbVersion, connection_queue >>

Modes == {"readonly", "readwrite", "versionchange"}
TxStates == {"None", "Active", "Inactive", "Committing", "Finished"}

TypeOK ==
    /\ stores \in [Stores -> BOOLEAN]
    /\ pending_stores \in [Stores -> BOOLEAN]
    /\ dbVersion \in Versions
    /\ connections \in [Connections ->
        [open: BOOLEAN,
         pendingUpgrade: BOOLEAN,
         requestedVersion: Versions,
         closed: BOOLEAN ]]
    /\ connection_queue \in Seq(Connections)
    /\ transactions \in [Transactions ->
        [conn: Connections,
         mode: Modes,
         stores: SUBSET Stores,
         \* We model requests as a simple boolean flag indicating pending work.
         \* We abstract away the actual list of requests and their side effects on stores
         \* because the goal of this spec is to model the concurrency of the transaction lifecycle only.
         requests  : BOOLEAN,
         \* A flag indicating if any requests have been processed.
         \* Used to verify the invariant that a transaction must satisfy CanStart
         \* before it processes any requests.
         processed_requests: BOOLEAN,
         state: TxStates ]]

IsCreated(tx) == transactions[tx].state # "None"

Live(tx) == IsCreated(tx) /\ transactions[tx].state # "Finished"

Overlaps(tx1, tx2) == (transactions[tx1].stores \cap transactions[tx2].stores) # {}

\* Since we allocate transaction IDs in increasing order (using Min),
\* the ID itself serves as a logical clock for creation time.
CreatedBefore(tx1, tx2) == tx1 < tx2

Min(S) == CHOOSE x \in S : \A y \in S : x <= y

Symmetry == Permutations(Stores) \cup Permutations(Connections)

ConnOpen(c) == connections[c].open

ConnPendingUpgrade(c) == connections[c].pendingUpgrade

TxForConn(c) == { tx \in Transactions : Live(tx) /\ transactions[tx].conn = c }

AllTxFinishedForConn(c) ==
    \A tx \in Transactions:
        (transactions[tx].conn = c) => (transactions[tx].state = "Finished")

HasLiveUpgradeTx(c) ==
    \E tx \in Transactions:
        /\ Live(tx)
        /\ transactions[tx].conn = c
        /\ transactions[tx].mode = "versionchange"

\* Safety property: A versionchange transaction being live excludes any other live transaction.
UpgradeTxExcludesOtherLiveTxs ==
    \A tx1 \in Transactions:
        (Live(tx1) /\ transactions[tx1].mode = "versionchange")
            => \A tx2 \in Transactions: Live(tx2) => (tx1 = tx2)

\* Inductive invariant that implies UpgradeTxExcludesOtherLiveTxs.
\*
\* If a versionchange transaction is live, then:
\* 1. Its connection is open and is at the head of the connection queue.
\* 2. All other connections are closed.
ActiveUpgradeTxImpliesExclusiveConn ==
    \A tx \in Transactions:
        (Live(tx) /\ transactions[tx].mode = "versionchange")
            =>
                /\ ConnOpen(transactions[tx].conn)
                /\ Len(connection_queue) > 0
                /\ Head(connection_queue) = transactions[tx].conn
                /\ \A c \in Connections: ConnOpen(c) => c = transactions[tx].conn

\* <https://w3c.github.io/IndexedDB/#transaction-scheduling>.
CanStart(tx) ==
    LET m == transactions[tx].mode IN
        IF m = "readonly" THEN
            ~\E other \in (Transactions \ {tx}):
                /\ Live(other)
                /\ transactions[other].mode = "readwrite"
                /\ CreatedBefore(other, tx)
                /\ Overlaps(other, tx)
        ELSE IF m = "readwrite" THEN
            ~\E other \in (Transactions \ {tx}):
                /\ Live(other)
                /\ CreatedBefore(other, tx)
                /\ Overlaps(other, tx)
        ELSE \* versionchange transactions can always start.
            TRUE

\* Invariant: If a transaction has processed requests, it must have been able to start.
ProcessedRequestsImpliesStarted ==
    \A tx \in Transactions:
        (transactions[tx].processed_requests) => CanStart(tx)
-----------------------------------------------------------------------------------------

DefaultTx ==
    [ conn     |-> CHOOSE c \in Connections : TRUE,
        mode      |-> "readonly",
        stores    |-> {},
        requests  |-> FALSE,
        processed_requests |-> FALSE,
        state     |-> "None" ]

DefaultConn ==
    [ open            |-> FALSE,
        pendingUpgrade  |-> FALSE,
        requestedVersion|-> 0,
        closed          |-> FALSE ]

Init ==
    /\ transactions = [tx \in Transactions |-> DefaultTx]
    /\ stores = [s \in Stores |-> FALSE]
    /\ pending_stores = [s \in Stores |-> FALSE]
    /\ connections = [c \in Connections |-> DefaultConn]
    /\ dbVersion = 0
    /\ connection_queue = <<>>

\* <https://w3c.github.io/IndexedDB/#open-a-database-connection>
\* Wait until all previous requests in queue have been processed.
StartOpenConnection(c, requestedVersion) ==
    /\ dbVersion <= requestedVersion
    /\ connections[c] = DefaultConn
    /\ ~connections[c].closed
    /\ connections' = [connections EXCEPT
            ![c] = [open            |-> FALSE,
                    pendingUpgrade  |-> (requestedVersion > dbVersion),
                    requestedVersion|-> requestedVersion,
                    closed          |-> FALSE]
        ]
    /\ connection_queue' = Append(connection_queue, c)
    /\ UNCHANGED <<transactions, stores, pending_stores, dbVersion>>

\* <https://w3c.github.io/IndexedDB/#open-a-database-connection>
FinishOpenConnection(c) ==
    /\ Len(connection_queue) > 0
    /\ c = Head(connection_queue)
    /\ connections[c].requestedVersion = dbVersion
	\* <https://w3c.github.io/IndexedDB/#upgrade-a-database>
	\* Wait for transaction to finish.
    /\ ~HasLiveUpgradeTx(c)
    /\ connections' = [connections EXCEPT ![c].open = TRUE, ![c].pendingUpgrade = FALSE]
    /\ connection_queue' = Tail(connection_queue)
    /\ UNCHANGED <<transactions, stores, pending_stores, dbVersion>>

\* <https://w3c.github.io/IndexedDB/#open-a-database-connection>
\* Wait until all connections in openConnections are closed.
\* Run upgrade a database using connection, version and request.
CreateUpgradeTransaction(c) ==
    LET 
	    freeTxs == { t \in Transactions : ~IsCreated(t) }
		tx == Min(freeTxs)
	IN
    /\ Len(connection_queue) > 0
	/\ ~ConnOpen(c)
    /\ c = Head(connection_queue)
    /\ ConnPendingUpgrade(c)
    /\ \A other \in (Connections \ {c}): ~ConnOpen(other)
    /\ freeTxs # {}
    /\ transactions' = [transactions EXCEPT
                ![tx] = [conn     |-> c,
                        mode      |-> "versionchange",
                        stores    |-> { s \in Stores : stores[s] },
                        requests  |-> FALSE,
                        processed_requests |-> FALSE,
                        state     |-> "Active"]
            ]
    /\ connections' = [connections EXCEPT
                ![c].open = TRUE
            ]
    /\ dbVersion' = connections[c].requestedVersion
    /\ pending_stores' = stores
    /\ UNCHANGED <<stores, connection_queue>>

\* <https://w3c.github.io/IndexedDB/#close-a-database-connection>
\*
\* "Wait for all transactions created using connection to complete.
\* Once they are complete, connection is closed."
CloseConnection(c) ==
    /\ ConnOpen(c)
    /\ AllTxFinishedForConn(c)
    /\ connections' = [connections EXCEPT 
            ![c].open = FALSE,
            ![c].closed = TRUE]
    /\ transactions' = [tx \in Transactions |-> 
            IF transactions[tx].conn = c 
            THEN DefaultTx 
            ELSE transactions[tx]]
    /\ UNCHANGED <<stores, pending_stores, dbVersion, connection_queue>>

\* <https://w3c.github.io/IndexedDB/#dom-idbdatabase-transaction>
\* If a live upgrade transaction is associated with the connection, throw 
\* If this’s close pending flag is true, then throw.
CreateTransaction(c, mode, scope) ==
    LET freeTxs == { t \in Transactions : ~IsCreated(t) } IN
    /\ freeTxs # {}
    /\ ConnOpen(c)
    /\ ~HasLiveUpgradeTx(c)
    /\ \A s \in scope: stores[s]
    /\ LET tx == Min(freeTxs) IN
       /\ transactions' = [transactions EXCEPT
                ![tx] = [conn     |-> c,
                        mode      |-> mode,
                            stores    |-> scope,
                                requests  |-> FALSE,
                                processed_requests |-> FALSE,
                                state     |-> "Active"]
            ]
    /\ UNCHANGED <<stores, pending_stores, connections, dbVersion, connection_queue>>

\* <https://w3c.github.io/IndexedDB/#asynchronously-execute-a-request>
\* Assert: transaction’s state is active.
AddRequest(tx) ==
    /\ transactions[tx].state = "Active"
    /\ ~transactions[tx].requests
    /\ transactions' = [transactions EXCEPT ![tx].requests = TRUE]
    /\ UNCHANGED <<stores, pending_stores, connections, dbVersion, connection_queue>>

\* <https://w3c.github.io/IndexedDB/#asynchronously-execute-a-request>
\*
\* Set request’s processed flag to true.
\*
\* Note: just modelling the presence of pending requests
\* and the fact that at least one was processed
\* so that we can check the "can start" invariant.
ProcessRequest(tx) ==
    /\ CanStart(tx)
    /\ ConnOpen(transactions[tx].conn)
    /\ transactions[tx].state \in {"Active", "Inactive"}
    /\ transactions[tx].requests
    /\ transactions' = [transactions EXCEPT
                ![tx].requests = FALSE,
                ![tx].processed_requests = TRUE,
                ![tx].state = "Active"
            ]
    /\ UNCHANGED <<stores, pending_stores, connections, dbVersion, connection_queue>>

\* <https://w3c.github.io/IndexedDB/#transaction-lifecycle>
\*
\* "Once the event dispatch is complete, the transaction's state
\* is set to inactive again".
\* 
\* Note: the event is dispatched and the transaction de-activated
\* from within the same task, but we still model these as separate
\* steps to make it easier to model adding any number of requests
\* while the transaction is active.
Deactivate(tx) ==
    /\ transactions[tx].state = "Active"
    /\ transactions' = [transactions EXCEPT ![tx].state = "Inactive"]
    /\ UNCHANGED <<stores, pending_stores, connections, dbVersion, connection_queue>>

\* <https://w3c.github.io/IndexedDB/#transaction-lifecycle>
\*
\* "The implementation must attempt to commit an inactive transaction
\* when all requests placed against the transaction have completed...
\* and no new requests have been placed against the transaction".
AutoCommit(tx) ==
    /\ transactions[tx].state = "Inactive"
    /\ ~transactions[tx].requests
    /\ transactions' = [transactions EXCEPT ![tx].state = "Committing"]
    /\ UNCHANGED <<stores, pending_stores, connections, dbVersion, connection_queue>>

\* <https://w3c.github.io/IndexedDB/#transaction-lifecycle>
\*
\* "An explicit call to commit() will initiate a
\* transaction/commit" and "When committing, the transaction state is set to
\* committing".
Commit(tx) ==
    /\ transactions[tx].state \notin {"None", "Committing", "Finished"}
    /\ transactions' = [transactions EXCEPT ![tx].state = "Committing"]
    /\ UNCHANGED <<stores, pending_stores, connections, dbVersion, connection_queue>>

\* <https://w3c.github.io/IndexedDB/#transaction-lifecycle>
\* "When a transaction is committed or aborted, its state is
\* set to finished".
\*
\* Note: The commit/abort logic is only applied to store operations (CreateStore/DeleteStore)
\* for now. We do not model data operations or their side effects/rollback, as it would
\* make the spec significantly more complicated without adding much value to the
\* transaction lifecycle concurrency model.
CommitDone(tx) ==
    /\ transactions[tx].state = "Committing"
    /\ transactions' = [transactions EXCEPT ![tx].state = "Finished"]
    /\ IF transactions[tx].mode = "versionchange"
            THEN
                /\ stores' = pending_stores
                /\ UNCHANGED pending_stores
            ELSE
                /\ UNCHANGED <<stores, pending_stores>>
    /\ UNCHANGED <<connections, dbVersion, connection_queue>>

\* <https://w3c.github.io/IndexedDB/#transaction-lifecycle>
\*
\* "A transaction can be aborted at any time before it is
\* finished".
Abort(tx) ==
    /\ transactions[tx].state \notin {"None", "Finished"}
    /\ transactions' = [transactions EXCEPT ![tx].state = "Finished"]
    /\ IF transactions[tx].mode = "versionchange"
            THEN
                /\ pending_stores' = stores
                /\ UNCHANGED stores
            ELSE
                /\ UNCHANGED <<stores, pending_stores>>
    /\ UNCHANGED <<connections, dbVersion, connection_queue>>

\* <https://w3c.github.io/IndexedDB/#upgrade-transaction-construct>
\* <https://w3c.github.io/IndexedDB/#dom-idbdatabase-createobjectstore>
\*
\* createObjectStore/deleteObjectStore "Throws
\* InvalidStateError if not called within an upgrade transaction" and require
\* the upgrade transaction to be active.
CreateStore(tx, s) ==
    /\ CanStart(tx)
    /\ transactions[tx].mode = "versionchange"
    /\ transactions[tx].state = "Active"
    /\ ~pending_stores[s]
    /\ pending_stores' = [pending_stores EXCEPT ![s] = TRUE]
    /\ UNCHANGED <<transactions, stores, connections, dbVersion, connection_queue>>

\* <https://w3c.github.io/IndexedDB/#upgrade-transaction-construct>
\* <https://w3c.github.io/IndexedDB/#dom-idbdatabase-deleteobjectstore>
\*
\* deleteObjectStore "Throws InvalidStateError if not called within an upgrade
\* transaction" and requires the upgrade transaction to be active.
DeleteStore(tx, s) ==
    /\ CanStart(tx)
    /\ transactions[tx].mode = "versionchange"
    /\ transactions[tx].state = "Active"
    /\ pending_stores[s]
    /\ pending_stores' = [pending_stores EXCEPT ![s] = FALSE]
    /\ UNCHANGED <<transactions, stores, connections, dbVersion, connection_queue>>

\* When all connections went through their open and close cyle: infinite stuttering.
AllClosed ==
    /\ \A c \in Connections: connections[c].closed
    /\ UNCHANGED Vars

Next ==
    \/ \E c \in Connections, v \in Versions: StartOpenConnection(c, v)
    \/ \E c \in Connections: FinishOpenConnection(c)
    \/ \E c \in Connections: CloseConnection(c)
    \/ \E c \in Connections: CreateUpgradeTransaction(c)
    \/ \E c \in Connections, m \in {"readonly", "readwrite"}, scope \in SUBSET Stores:
            CreateTransaction(c, m, scope)
    \/ \E tx \in Transactions:
            (\/ AddRequest(tx)
             \/ ProcessRequest(tx)
             \/ Deactivate(tx)
             \/ AutoCommit(tx)
             \/ Commit(tx)
             \/ CommitDone(tx)
             \/ Abort(tx)
             \/ \E s \in Stores: (CreateStore(tx, s) \/ DeleteStore(tx, s)))
    \/ AllClosed

Spec == Init /\ [][Next]_Vars

====
