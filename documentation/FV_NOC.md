# Formal Verification of NOCs

## Correctness

* A communication network is deemed correct if any message will be eventually injected into it and if any injected message is eventually consumed correctly.
* Messages arrive at the correct destination without any modifications.
* Unlike commmunication protocols for Internet, on chip communications have to be deterministic; reordering, loss, and resending of messages are not an option.
* NOC Function argument - List of messages originated at source nodes. Returns the results received at destination node. 

## A General Model of NOC

* Consists of an arbitrary but finite number of nodes.
* Topologies, Routing algorithm, and Scheduling policies are its essential aspects, but these elements can also be arbitrary.
* Each node can be divided into two components: Application and interface. 
    * Application refer to the cores that are the computational and functional aspects. 
    * Interface refers to the communication components.
* Defined using the following three functions
    * Interfaces - represented by send and receive, responsible for encpsulating flits into a packet and extracting flits from a packet.
    "send encapsulates a message into a frame and injects the frame on the network; recv decodes the frame to recover the emitted message."
    * Routing  - Computes the route for a pair of source and destination. Consists of the routing algorithm.
    * Scheduling - An invariant must be preserved at all times in any admissable state of the network. The scheduling function manages conflicts,
    and generates a list of possible communications that satisfy the invariant. The invariant is assumed but not explicitly represented.
   
## GeNOC
    Input = List of transactions t=(id source msg dest)
    

## Proofs

### Interface 
    *  recieve(send(message))=message

### Routing
    * Routing Termination
    * Routing Correctness - route r, begins with origin of m, ends with destination of m, and has at least two nodes

### Scheduling 

## Misc.

* Missives = whole messages (standard_flit type)

## References

[^1] title={A functional formalization of on chip communications},year={2008},author={Julien Schmaltz and Julien Schmaltz and D. Borrione and Dominique Borrione
