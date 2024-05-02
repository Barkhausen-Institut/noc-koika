# Basics

## Network on chips

* Traditionally a bus was used to communicate across multiple cores, but a bus interface is not scalable and can only be used upto dozens of cores. NOCs provide a solution to this problem.
* In NOCs, it is difficult to ensure that message sent from one core will rach its destination. Situations such as deadlock, livelocks, misrouting, and starvation may arise.
*  In the reference the communication model is defined using three layers
    
    * **Application Layer** - Layer between applications.
        * Dictates which types of messages are injected into the network and also where, when and which messages are consumed.

    * **Network Layer** - Processing nodes, channels, routers
        * Each core is connected to a *processing node* which injects the messages into the network (TCU?)
        * All messages from the processing node are sent through a *switch*. (Switch is inside the processing node)
        * Switches are connected via *channels*. Channels are the only components in the network that can buffer messages. 
        * Switch applies arbitration to determine which ingoing channel is served.
        * The set of possible channels to which a message can be routed in one step is called the next hops of the message.
        * Routing can be deterministic (fixed no. of hops) or adaptive (variable no. of hops).
        * Processing nodes decides the next hop at the end of the channel.
    
    * **Network Layer** - Contains transfer protocol between two nodes.

## Formal Verification

* Formal verification is a methodology to assess the correctness of a system. The system should meet its specification when formalized in some mathematical language.
* **Analytical Formal Verification** - The analysis of the system is done statically; the dynamic and runtime behavior behavior of the system is not taken into consideration.
* Flavours of Analytical Formal Verification
    * **Model Checking** - Model checking is a technique whether some model of a system satisfies a certain specification.
    * The model is described in a state machine with specification as temporal logic. 
    * The model checker explores the state space and if it arrives at a state that doesnt satisfy the specification the system is proven to be incorrect.
    * State space explosion is a major downside.

    * **Theorem Proving** - A mathematical proof is formalized in such a way such that its correctness can be ensured by a computer program.
    * A theorem prover can be used to break large proofs into smaller ones.
    * One major advantage is the ability to verify parametric systems. 

    * **SAT solvers** - SAT solvers are automated algorithms that decide whether some formula is satisfiable. 
    * The problem or theory that needs to be proven needs to be formulated as a SAT instance.


## WIP

Isolated network model - Assumptions are made to simplify the application and link layer. Cores are homogeneous, same message type, messages move as long as there is capacity. Focuses on routing and topology.

Integrated network model - Incorporates all details concerning the three layers.

Network can be deadlock free in isolation but prone to it in integration and vice versa.

Isolated - very abstract, doesnt take into context every possible combination
Integrated - Complex, results not parametric.


The GeNoC framework (for Generic Network-on-Chip) provides a methodology to
do parametric proofs over NoCs.  The definition of
the model relies on three independent groups of constrained functions:
routing and topology, scheduling, interface

xMAS

Channels can be either queue-based (FIFO) or central buffer (any message can be chosen)

## Quotes
* The contribution of this thesis consists of easy and scalable mechanical verific-
ation methods for communication networks. We formalize a notion of correctness,
stating that a network is always eventually able to inject messages and that any
injected message will always eventually arrive at its destination. We show that
in order to establish this emergent correctness property for some NoC, it suffices
to prove several smaller properties on isolated constituents. With a realistic ex-
ample we conclude that many of these properties can easily be verified. Deadlock
freedom, however, remains difficult to prove due to the interactions between the
different constituents of the network. Therefore we provide formally proven correct
tools and algorithms to hunt for deadlocks in communication networks [^1]


## References

[^1] Verbeek, Freek. Formal verification of on-chip communication fabrics. Sl: sn, 2013.

[^2] K. Richter, M. Jersak and R. Ernst, "A formal approach to MpSoC performance verification," in Computer, vol. 36, no. 4, pp. 60-67, April 2003, doi: 10.1109/MC.2003.1193230.
keywords: {Control systems;System-on-a-chip;Hardware;Operating systems;Software systems;Resource management;Digital signal processing;Memory management;Network-on-a-chip;Intellectual property},

