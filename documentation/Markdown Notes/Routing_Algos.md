# Routing Algorithms

* Dimension ordered (X-Y routing)- Deterministic
* West First - Adaptive routes 
* North Last
* Negative First 
* Odd Even 

Algorithms such as west first are adaptive, and provide multiple routes to avoid blocking.

# On Chip Network Interference

* When multiple applications share the same resource, the performance (throughput and latency) of one appplication can be affected by the other.

* "The network interference creates a potential timing channel where sensitive information can be leaked intentionally or unintentionally even when legitimate communication channels are disallowed. For example, a program with a high security clearance may covertly leak confidential informa- tion to a low-security program by controlling the amount of network traffic to reflect the secret (say, high demand for 1 and low demand for 0). The low-security program can obtain the secret by measuring the throughput or latency of its own flow through the shared network. This covert channel allows the two programs to communicate covertly even when they are not allowed to explicitly send messages to each other or access the same memory locations."
## Solutions

* Random arbitration - If the router recieves inputs from multiple sides it randomly prioritises between the available options

* Adaptive Routing - Using alternate routes depending on the condition of output router.

## Router Configuration

* Round Robin - Input ports are served in circular order and without priority
* Starvation Free - Recently served port gets the lowest priority (advancements to starvation freeGatecrasher and Trickster)
* Priority - Requests are priortised according to the order in which they are received
* Time division multiplexing - Each port is given a time slot during which its communication request can be granted
