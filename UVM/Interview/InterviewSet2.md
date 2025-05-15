# What are the different phases in UVM ?
The main phases in UVM are :

build_phase
connect_phase
end_of_elaboration_phase
start_of_simulation_phase
run_phase
extract_phase
check_phase
report_phase
final_phase
# What is a virtual sequence and a virtual sequencer ?
A virtual sequence is a container to hold and execute multiple other smaller sequences. A virtual sequencer is a container to hold the handles to other sequencers in an environment so that each sequence in a virtual sequence can be executed on the appropriate sequencer. Read more in Virtual Sequence and Virtual Sequencer
# What is the difference between `uvm_do and `uvm_send ?
`uvm_do macro will automatically create a new object, randomize it and send to the the sequencer. `uvm_send is used when the object is already created and randomized but needs to be executed on a sequencer. Read more in How to execute sequences via `uvm_do macros ? and Sequence action macros for pre-existing items
# What is the difference between uvm_transaction and uvm_sequence_item ?
The uvm_transaction class is the root base class for UVM transactions and has a timing and recording interface as well. Use of this class as a base for user-defined transactions is deprecated, and instead its sub-class uvm_sequence_item should be used. The intended use of transaction API is to call accept_tr, begin_tr and end_tr during the course of sequence item execution in order to record the events to a vendor-specific transaction database. uvm_sequence_item is primarily used to define data objects and related methods.
# What are the benefits of using UVM ?
Some of the major and immediate benefits are :

Testbench prototyping becomes faster because of all the base classes for drivers, monitors, sequencers
There's a well defined reporting system which supports various levels of verbosities like LOW, DEBUG, etc
Supports register model creation and maintainence which simplifies the way DUT registers are accessed
Well structured plug and play style components like agents that can be plugged into any environment to support a particular protocol
Factory helps to override certain components without having to modify existing connections in the testbench
Configuration databases that allow components to share objects and data between each other
Make use of TLM features that enable different components that receive transactions to perform different operations on it.
Promotes re-usability, flexibility, uniformity and robustness to every testbench built on UVM
# Is it possible to have a user defined phase in UVM ?
Yes, you can define your own phase and insert it between any of the existing phases. For this, you have to first define a new phase class inherited from uvm_task_phase, implement the exec_task or exec_func method and insert the phase into existing schedule or domain object.
# What is the difference between RAL backdoor and frontdoor accesses ?
A backdoor access in RAL is a way to dump values directly onto the DUT registers via a hard coded RTL signal path and does not consume simulation time. A frontdoor access in RAL is usually done by sending the data as a transaction through an associated peripheral bus interface and hence consumes simulation time.
# What is a phase objection ?
In UVM, all components synchronize with each other through a set of phases. Every component has to finish its processes in a particular phase until it can proceed to the next. So, objection is a mechanism to allow a component to stall other components from proceeding to the next phase until it gets the chance to finish its own tasks. This is normally done using raise_objection() and drop_objection() methods from the uvm_phase class.
# What is the difference between set_config_* and uvm_config_db ?
The basic set_config_* methods are mapped to corresponding uvm_config_db as :
```
set_config_int(...) => uvm_config_db#(uvm_bitstream_t)::set(cntxt,...)
set_config_string(...) => uvm_config_db#(string)::set(cntxt,...)
set_config_object(...) => uvm_config_db#(uvm_object)::set(cntxt,...)
```
# What are the different factory override types ?
Factory overrides can be done in four different ways:

Instance override by type of the component/object
Instance override by name of the component/object
Type override by type of the component/object
Name override by type of the component/object
