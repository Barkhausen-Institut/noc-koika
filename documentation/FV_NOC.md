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


## Properties 

### Router level
* Messages arrive at correct destination without modification
    * Router input = Router output
* For all xm>xr message will be routed to xr+1, similar for xm < xr
* If xm> xlength then message is invalid. all xm < xlength (xm is destination)
* Priority
### Network level

* Messages recieved are equivalent to the ones sent into the network.
* Routing Correctness - route r, begins with origin of m, ends with destination of m, and has at least two nodes

* Deadlock freedom - In a deadlock free network there is no state in which a set of messages is permanently blocked. 
* Livelock Freedom - No livelocks should occur. A livelock is a scenario in which the moves infinitely in a network.
* Starvation Freedom - When a message wants to acquire some resource but is never given access to.
* Liveness of injection - A message that needs to be injected is eventually injected into the network.
* Functional Correctness - Message follows a correct path, contents are not modified​, If it is consumed, it is consumed at the correct destination
* Evacuation - Injected message is always consumed (Correctness doesnt matter)
* Local liveness - Any message will eventually move from its current resource to next resource
* Productivity - The net of all the above properties. That messages can always be injected and will be correctly consumed. 


Functional Correctness:

1. When a message is consumed its current location is its destination.
2. All messages traverse a correct route through the network.
3. The content of messages does not change.

Correct Route - path of valid resources, first element is source last is destination

Timimg Atack Resilient - In order to avoid timing attacks, the communication delay should be independent of the amount of traffic requesting the communication service to the router.

Router Level

* No packet loss inside the router
* No packet duplication insdie the router
* No packet modification inside the router
* Packet that enters the router will eventually leave the router at some point of time
* Packet is routed to the correct port according to its destination
* Minimum and maximum age of packet?
* Valid address of router
* Min two connections, Max four connections

Bufferlevel

* Whatever applies to a queue
* Read and write pointers are incremented when read and writes enables are set
* Read and write pointers are not incremented when buffers are full or empty
* The same number of packets that were written into the buffer can be read
* Data that was read from buffer was written into it at some point
## References

[^1] title={A functional formalization of on chip communications},year={2008},author={Julien Schmaltz and Julien Schmaltz and D. Borrione and Dominique Borrione
