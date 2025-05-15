# What is a UVM RAL model ? Why is it required ?
RAL is short for Register Abstraction Layer. It is a set of base classes that can be used to create register models to mimic the register contents in a design. It is much easier to write and read from the design using a register model than sending a bus transaction for every read and write. Also the register model stores the current state of the design in a local copy called as a mirrored value. Read more in Register Layer.
# What is p_sequencer, and where is it used ?
p_sequencer is a handle to the sequencer on which the current sequence should be executed and is made available in a sequence by the macro `uvm_declare_p_sequencer. It is typically accessed within sequences to start other sequences.
# What is an analysis port ?
An analysis port is a TLM mechanism to allow a component to broadcast a class object to multiple listeners so that they can implement different methods to perform different operations on the data it receives. Read more in TLM Analysis Port
# What is the difference between new() and create() ?
The new() method is the classical way of how SV creates an object instance. The create() is an addition in UVM that allows the factory to return an object of the type that we want. Read more in Using factory overrides.
# Is UVM independent of SystemVerilog ?
No. UVM is built on SystemVerilog and hence you cannot run UVM with any tool that does not support SystemVerilog.
# Why do we need to register a class with a factory ?
You don't necessarily need to. It is registered with a factory simply to make the testbench more re-usable and have the capability to override it with some other derivative component later on. Read more in Using factory overrides.
# What are Active and Passive modes in an agent ?
An agent typically consists of a driver, sequencer and a monitor. At times, we don't want the agent to drive anything to the DUT but simply monitor the signals on the interface. This is a passive agent where sequencer and driver are not instantiated at all. An active agent is when it can run sequences on its sequencer, drive signals and monitor the interface.
# What is a TLM Fifo ?
When two components at different clocks need to be operating independently, you have to insert a TLM FIFO in between. One component can send data at a faster rate while the other component can receive at a slower rate. Read more in TLM Fifo
# What are the advantages of `uvm_component_utils and `uvm_object_utils ?
These macros are used to register a class with the factory. `uvm_component_utils is used when the class is a component derived from uvm_component, and `uvm_object_utils is used if it's an object derived from uvm_object. There are no advantages from one over the other but are separate ways to register with the factory. Read more in Using factory overrides.
# How does a sequence start ?
A sequence can be started by calling its start() method or by using the macro `uvm_do. Read more in Executing sequences via start() and Executing sequences via macros
