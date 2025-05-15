# How can we access a DUT signal in a component or sequence ?
Interface signals can be accessed via a virtual interface handle that points to the actual physical interface. Signals within the DUT can be accessed directly by providing a hierarchical RTL path to uvm_hdl_* functions such as.
```
uvm_hdl_force("top.eatable.fruits.apple.slice", 2);
uvm_hdl_deposit("top.eatable.fruits.apple.slice", 3);
uvm_hdl_read("top.eatable.fruits.apple.slice", rdata);
```
# What is RALGEN and how do you use it ?
RALGEN is a Synopsys tool to generate RAL model from an IPXACT specification file. You simply have to specify a few options and select the block for which you need to generate class structure for and provide them to the tool.
# What are desired and mirrored values in RAL ?
Desired values are those that we want the design to have, and can later update the design with. Mirrored values are those that reflect the latest known values in the DUT.
# What are reg2bus and bus2reg functions for ?
They are RAL functions that enable conversion from generic register contents to actual bus transactions and vice-versa. You have to define them based on the protocol you are dealing with by assigning the data object of the protocol with values from rw internal variable and vice-versa.
# How would you debug a config db name or path mismatch problem ?
You can use the command-line define +UVM_CONFIG_DB_TRACE to dump information related to all SET and GET calls done on the configuration DB. It also shows you the path, and instance that makes the call.
# What are the different TB components in UVM ?
Some of the major components are driver, monitor, scoreboard, sequencer, agent, environment, test and sequences.
# Which UVM phase takes more time and why ?
Run time phases take more time because they are the major phases that consume simulation time. The times taken for each test can be different because they all test different aspects of a design.
# How do you connect a monitor with a scoreboard ?
You can declare the implementation of an analysis port within a scoreboard and connect the monitor's analysis port with it in the environment's connect method.
# How do you connect driver and sequencer ?
Driver has a TLM port called seq_item_port that can be connected with the sequencer's seq_item_export in an agent's connect method.
# What is uvm_config_db and uvm_resource_db ?
Both are mechanisms that allow a component to place an object in a central look-up table under a specified name and path, so that they can be retrieved by another component using the same name and path. The uvm_config_db class provides a convenience interface on top of the uvm_resource_db to simplify the basic interface that is used for configuring uvm_component instances.
