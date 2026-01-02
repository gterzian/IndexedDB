------------------------------ MODULE transaction_lifecycle ------------------------------
EXTENDS Naturals, Sequences, FiniteSets

CONSTANT N
VARIABLES transactions, clock, stores, connections, dbVersion, connection_queue
\* TLA+ model of the transaction lifecycle and scheduling rules from:
\* - <https://w3c.github.io/IndexedDB/#transaction-lifecycle>
\* - <https://w3c.github.io/IndexedDB/#transaction-scheduling>

Stores == 0..N
Transactions == 0..N
Requests == 0..N
Connections == 0..N
Versions == 0..N

\* Note: by using only a single dbVersion, we do not model multiple databases. 
Vars == << transactions, clock, stores, connections, dbVersion, connection_queue >>

Modes == {"readonly", "readwrite", "versionchange"}
TxStates == {"None", "Active", "Inactive", "Committing", "Finished"}

TypeOK ==
	/\ clock \in Nat
	/\ stores \in [Stores -> BOOLEAN]
	/\ dbVersion \in Versions
	/\ connections \in [Connections ->
				[ open           : BOOLEAN,
					pendingUpgrade  : BOOLEAN,
					requestedVersion: Versions ]]
	/\ connection_queue \in Seq(Connections)
	/\ transactions \in [Transactions ->
				[ conn     : Connections,
					mode      : Modes,
					stores    : SUBSET Stores,
					requests  : Seq(Requests),
					state     : TxStates,
					createdAt : Nat ]]

IsCreated(tx) == transactions[tx].state # "None"

Live(tx) == IsCreated(tx) /\ transactions[tx].state # "Finished"

Overlaps(tx1, tx2) == (transactions[tx1].stores \cap transactions[tx2].stores) # {}

CreatedBefore(tx1, tx2) == transactions[tx1].createdAt < transactions[tx2].createdAt

ConnOpen(c) == connections[c].open

ConnPendingUpgrade(c) == connections[c].pendingUpgrade

TxForConn(c) == { tx \in Transactions : Live(tx) /\ transactions[tx].conn = c }

AllTxFinishedForConn(c) ==
	\A tx \in Transactions:
		(transactions[tx].conn = c) => (transactions[tx].state \in {"None", "Finished"})

HasLiveUpgradeTx(c) ==
	\E tx \in Transactions:
		/\ Live(tx)
		/\ transactions[tx].conn = c
		/\ transactions[tx].mode = "versionchange"

\* Safety property: at most one upgrade transaction is live at a time.
NoTwoLiveUpgradeTxs ==
	Cardinality({ tx \in Transactions : Live(tx) /\ transactions[tx].mode = "versionchange" }) <= 1

\* Inductive invariants that implies NoTwoLiveUpgradeTxs.
\*
\* If a versionchange transaction is live, then its connection is open and
\* is at the head of the connection queue.
ActiveUpgradeTxImpliesConnOpenAndHead ==
	\A tx \in Transactions:
		(Live(tx) /\ transactions[tx].mode = "versionchange")
			=>
				/\ ConnOpen(transactions[tx].conn)
				/\ Len(connection_queue) > 0
				/\ Head(connection_queue) = transactions[tx].conn

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
-----------------------------------------------------------------------------------------

DefaultTx ==
	[ conn     |-> 0,
		mode      |-> "readonly",
		stores    |-> {},
		requests  |-> <<>>,
		state     |-> "None",
		createdAt |-> 0 ]

DefaultConn ==
	[ open            |-> FALSE,
		pendingUpgrade  |-> FALSE,
		requestedVersion|-> 0 ]

Init ==
	/\ transactions = [tx \in Transactions |-> DefaultTx]
	/\ clock = 0
	/\ stores = [s \in Stores |-> FALSE]
	/\ connections = [c \in Connections |-> DefaultConn]
	/\ dbVersion = 0
	/\ connection_queue = <<>>

\* <https://w3c.github.io/IndexedDB/#open-a-database-connection>
OpenConnection(c, requestedVersion) ==
	/\ dbVersion <= requestedVersion
	/\ connections[c] = DefaultConn
	/\ connections' = [connections EXCEPT
			![c] = [open            |-> FALSE,
					pendingUpgrade  |-> (requestedVersion > dbVersion),
					requestedVersion|-> requestedVersion]
		]
	/\ connection_queue' = Append(connection_queue, c)
	/\ UNCHANGED <<transactions, stores, dbVersion, clock>>

\* <https://w3c.github.io/IndexedDB/#open-a-database-connection>
\*
\* Note: A non-upgrade open request can be processed once it reaches the head
\* of the queue.
FinishOpenConnection(c) ==
	/\ Len(connection_queue) > 0
	/\ c = Head(connection_queue)
	/\ ~ConnPendingUpgrade(c)
	/\ ~ConnOpen(c)
	/\ connections[c].requestedVersion = dbVersion
	/\ connections' = [connections EXCEPT ![c].open = TRUE]
	/\ connection_queue' = Tail(connection_queue)
	/\ UNCHANGED <<transactions, stores, dbVersion, clock>>

\* <https://w3c.github.io/IndexedDB/#upgrade-transaction-construct>
\* When all other connections are closed, and this connection is at the head of queue,
\* create and start the ugrade transaction.
\* The connection is removed from the queue when the transaction is finished.
\* See `Abort` and `CommitDone`.
CreateUpgradeTransaction(tx, c) ==
	/\ Len(connection_queue) > 0
	/\ c = Head(connection_queue)
	/\ ConnPendingUpgrade(c)
	/\ ~ConnOpen(c)
	/\ \A other \in (Connections \ {c}): ~ConnOpen(other)
	/\ ~IsCreated(tx)
	/\ transactions' = [transactions EXCEPT
				![tx] = [conn     |-> c,
						mode      |-> "versionchange",
						stores    |-> { s \in Stores : stores[s] },
						requests  |-> <<>>,
						state     |-> "Active",
						createdAt |-> clock]
			]
	/\ connections' = [connections EXCEPT
				![c].open = TRUE
			]
	/\ dbVersion' = connections[c].requestedVersion
	/\ clock' = clock + 1
	/\ UNCHANGED <<stores, connection_queue>>

\* <https://w3c.github.io/IndexedDB/#close-a-database-connection>
\*
\* "Wait for all transactions created using connection to complete.
\* Once they are complete, connection is closed."
\*
\* Note: forced close is not modeled right now.
CloseConnection(c) ==
	/\ ConnOpen(c)
	/\ AllTxFinishedForConn(c)
	/\ connections' = [connections EXCEPT ![c].open = FALSE]
	/\ UNCHANGED <<transactions, stores, dbVersion, clock, connection_queue>>

\* <https://w3c.github.io/IndexedDB/#dom-idbdatabase-transaction>
CreateTransaction(tx, c, mode, scope) ==
	/\ ~IsCreated(tx)
	/\ ConnOpen(c)
    \* If a live upgrade transaction is associated with the connection, throw 
	/\ ~HasLiveUpgradeTx(c)
	/\ \A s \in scope: stores[s]
	/\ transactions' = [transactions EXCEPT
				![tx] = [conn     |-> c,
						mode      |-> mode,
							stores    |-> scope,
								requests  |-> <<>>,
								state     |-> "Active",
								createdAt |-> clock]
			]
	/\ clock' = clock + 1
	/\ UNCHANGED <<stores, connections, dbVersion, connection_queue>>

\* <https://w3c.github.io/IndexedDB/#transaction-lifecycle>
\*
\* "New requests can be made against the transaction when it is
\* in [active]" and "The implementation must allow requests to be placed
\* against the transaction whenever it is active".
AddRequest(tx, r) ==
	/\ Live(tx)
	/\ ConnOpen(transactions[tx].conn)
	/\ transactions[tx].state = "Active"
	/\ Len(transactions[tx].requests) < N
	/\ transactions' = [transactions EXCEPT ![tx].requests = Append(@, r)]
	/\ UNCHANGED <<clock, stores, connections, dbVersion, connection_queue>>

\* <https://w3c.github.io/IndexedDB/#transaction-lifecycle>
\*
\* "Requests must be executed in the order in which
\* they were made" and "While the event is being dispatched, the transaction
\* state is set to active".
ProcessRequest(tx) ==
	/\ Live(tx)
	/\ CanStart(tx)
	/\ ConnOpen(transactions[tx].conn)
	/\ transactions[tx].state \in {"Active", "Inactive", "Committing"}
	/\ Len(transactions[tx].requests) > 0
	/\ transactions' = [transactions EXCEPT
				![tx].requests = Tail(@),
				![tx].state = "Active"
			]
	/\ UNCHANGED <<clock, stores, connections, dbVersion, connection_queue>>

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
	/\ Live(tx)
	/\ transactions[tx].state = "Active"
	/\ IF Len(transactions[tx].requests) = 0
	  THEN transactions' = [transactions EXCEPT ![tx].state = "Finished"]
	  ELSE transactions' = [transactions EXCEPT ![tx].state = "Inactive"]
	/\ UNCHANGED <<clock, stores, connections, dbVersion, connection_queue>>

\* <https://w3c.github.io/IndexedDB/#transaction-lifecycle>
\*
\* "An explicit call to commit() will initiate a
\* transaction/commit" and "When committing, the transaction state is set to
\* committing".
Commit(tx) ==
	/\ IsCreated(tx)
	/\ transactions[tx].state \notin {"None", "Committing", "Finished"}
	/\ transactions' = [transactions EXCEPT ![tx].state = "Committing"]
	/\ UNCHANGED <<clock, stores, connections, dbVersion, connection_queue>>

CommitDone(tx) ==
	\* Spec: Transaction lifecycle.
	\* <https://w3c.github.io/IndexedDB/#transaction-lifecycle>
	\*
	\* "When a transaction is committed or aborted, its state is
	\* set to finished".
	/\ transactions[tx].state = "Committing"
	/\ transactions' = [transactions EXCEPT ![tx].state = "Finished"]
	/\ IF transactions[tx].mode = "versionchange"
			THEN
				/\ connections' = [connections EXCEPT ![transactions[tx].conn].pendingUpgrade = FALSE]
				\* Dequeue the corresponding open request once the upgrade tx finishes.
				\* This models "Wait for transaction to finish" in the upgrade algorithm:
				\* <https://w3c.github.io/IndexedDB/#upgrade-a-database>
				/\ connection_queue' = Tail(connection_queue)
			ELSE
				/\ connections' = connections
				/\ connection_queue' = connection_queue
	/\ UNCHANGED <<clock, stores, dbVersion>>

\* <https://w3c.github.io/IndexedDB/#transaction-lifecycle>
\*
\* "A transaction can be aborted at any time before it is
\* finished".
Abort(tx) ==
	/\ IsCreated(tx)
	/\ transactions[tx].state \notin {"None", "Finished"}
	/\ transactions' = [transactions EXCEPT
				![tx].state = "Finished",
				![tx].requests = <<>>
			]
	/\ IF transactions[tx].mode = "versionchange"
			THEN
				/\ connections' = [connections EXCEPT ![transactions[tx].conn].pendingUpgrade = FALSE]
				\* Dequeue the corresponding open request once the upgrade tx finishes.
				\* This models "Wait for transaction to finish" in the upgrade algorithm:
				\* <https://w3c.github.io/IndexedDB/#upgrade-a-database>
				/\ connection_queue' = Tail(connection_queue)
			ELSE
				/\ connections' = connections
				/\ connection_queue' = connection_queue
	/\ UNCHANGED <<clock, stores, dbVersion>>

\* <https://w3c.github.io/IndexedDB/#upgrade-transaction-construct>
\* <https://w3c.github.io/IndexedDB/#dom-idbdatabase-createobjectstore>
\*
\* createObjectStore/deleteObjectStore "Throws
\* InvalidStateError if not called within an upgrade transaction" and require
\* the upgrade transaction to be active.
CreateStore(tx, s) ==
	/\ Live(tx)
	/\ CanStart(tx)
	/\ ConnOpen(transactions[tx].conn)
	/\ transactions[tx].mode = "versionchange"
	/\ transactions[tx].state = "Active"
	/\ ~stores[s]
	/\ stores' = [stores EXCEPT ![s] = TRUE]
	/\ UNCHANGED <<transactions, clock, connections, dbVersion, connection_queue>>

\* <https://w3c.github.io/IndexedDB/#upgrade-transaction-construct>
\* <https://w3c.github.io/IndexedDB/#dom-idbdatabase-deleteobjectstore>
\*
\* deleteObjectStore "Throws InvalidStateError if not called within an upgrade
\* transaction" and requires the upgrade transaction to be active.
DeleteStore(tx, s) ==
	/\ Live(tx)
	/\ CanStart(tx)
	/\ ConnOpen(transactions[tx].conn)
	/\ transactions[tx].mode = "versionchange"
	/\ transactions[tx].state = "Active"
	/\ stores[s]
	/\ stores' = [stores EXCEPT ![s] = FALSE]
	/\ UNCHANGED <<transactions, clock, connections, dbVersion, connection_queue>>

\* When everything is done, allow infinite stuttering.
AllDone ==
	/\ \A tx \in Transactions: transactions[tx].state \in {"None", "Finished"}
	/\ UNCHANGED Vars

Next ==
	\/ \E c \in Connections, v \in Versions: OpenConnection(c, v)
	\/ \E c \in Connections: FinishOpenConnection(c)
	\/ \E c \in Connections: CloseConnection(c)
	\/ \E tx \in Transactions:
			(\/ \E c \in Connections: CreateUpgradeTransaction(tx, c)
			 \/ \E c \in Connections, m \in {"readonly", "readwrite"}, scope \in SUBSET Stores:
					CreateTransaction(tx, c, m, scope)
			 \/ \E r \in Requests: AddRequest(tx, r)
			 \/ ProcessRequest(tx)
			 \/ Deactivate(tx)
			 \/ Commit(tx)
			 \/ CommitDone(tx)
			 \/ Abort(tx)
			 \/ \E s \in Stores: (CreateStore(tx, s) \/ DeleteStore(tx, s)))
	\/ AllDone

Spec == Init /\ [][Next]_Vars

====
