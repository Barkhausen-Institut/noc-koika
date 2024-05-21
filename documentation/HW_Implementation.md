# NoC Hardware Implementation

## Packet Switched Network
    * Packet consists of header (address) and payload (data). Each packet can move autonomously.
    * At each router in the network the next step is decided. No reservation of channel like wormhole switching.
    * Channel can be built using queues (only head can be popped) or central buffers (any packet can be popped).

## Algorithm
    * Each router is assigned a x,y coordinate. A third dimension z specifies tile (module) address.
    * Numbering is done from North in clockwise direction. Links to tiles are numbered first then inter-router links are numbered.
    * First routed along x direction then y direction. If diagonal is possible it is given priority over x and y.
    * 