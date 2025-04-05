# UVM Sequence
![image](https://github.com/user-attachments/assets/3db6645d-a859-4f38-8dbe-eeaa01cf2e6b)
* UVM sequences are made up of several data items which can be put together in different ways to create interesting scenarios. They are executed by an assigned sequencer which then sends data items to the driver. Hence, sequences make up the core stimuli of any verification plan.
# Class Hierarchy
![image](https://github.com/user-attachments/assets/1e59aff5-38d4-4bf0-afbc-cc9f78c48958)
# 建立 UVM Sequence 的步驟
* Create a user-defined class inherited from **uvm_sequence**, register with factory and call new
```
// my_sequence is user-given name for this class that has been derived from "uvm_sequence"
class my_sequence extends uvm_sequence;

	// [Recommended] Makes this sequence reusable. Note that we are calling
	// `uvm_object_utils instead of `uvm_component_utils because sequence is a uvm_transaction object
	`uvm_object_utils (my_sequence)      // 注意這邊是 uvm_object_utils

	// This is standard code for all components
    function new (string name = "my_sequence");
    	super.new (name);
    endfunction
endclass
```
* Declare the default sequencer to execute this sequence
```
// [Optional] my_sequencer is a pre-defined custom sequencer before this sequence definition
`uvm_declare_p_sequencer (my_sequencer)
```
* Define the body method
```
// [Recommended] Make this task "virtual" so that child classes can override this task definition
virtual task body ();
	// Stimulus for this sequence comes here
endtask
```
# UVM Sequence Example
* `uvm_do macro will **allocate an object of type my_data to pkt**, **randomize it** and **send it to the default sequencer** associated to execute this sequence. Use of this macro simply reduces the code required to achieve the objectives mentioned before.
```
class my_sequence extends uvm_sequence;
	`uvm_object_utils (my_sequence)

	function new (string name = "my_sequence");
		super.new (name);
	endfunction

	// Called before the body() task
	task pre_body ();
		...
	endtask

	task body ();
		my_data pkt;
		`uvm_do (pkt);   // 這 macro 就是直接產生 transaction 和送出去
	endtask

	// Called after the body() task
	task post_body();
		...
	endtask
endclass
```
