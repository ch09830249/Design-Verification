/*
A module is the fundamental construct used for building designs. 
Each module can contain hierarchies of other modules, nets, variables and other procedural blocks to describe any hardware functionality. 
The testbench on the other hand is a complete environment to verify the design and hence 
an emphasis is placed on the way it is modeled to make it more re-usable and effective. 
It must be properly initialized and synchronized avoiding race conditions between the design and the testbench.

What is the need for the program block?
SystemVerilog program block was introduced for the following reasons.

- To provide an entry point to the execution of testbenches
- To create a container to hold all other testbench data such as tasks, class objects and functions
- Avoid race conditions with the design by getting executed during the reactive region of a simulation cycle
The reactive region is one of the last few phases before simulation time advances, and by then all design element statements would have been executed and testbench will see the updated value. It is important to have this demarcation between the execution of design and testbench statements because it will give a more deterministic output between simulators.
*/