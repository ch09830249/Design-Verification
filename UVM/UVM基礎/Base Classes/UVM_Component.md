# UVM Component
## What is UVM Component?
uvm_component is a fundamental base class that serves as the foundation for all UVM components like drivers, monitors and scoreboards in a verification environment. It has the following features:
* **Hierarchy**: Supports a **hierarchical structure**, where each component can have child components, **forming a tree-like structure** and provides methods for searching and traversing the tree.
* **Phasing**: Components can participate in the UVM phasing mechanism, which organizes the simulation into different phases like build, connect, run, and cleanup. Components can perform specific tasks during each phase.
* **Reporting**: Components can use the UVM messaging infrastructure to report events, warnings, and errors during simulation.
* **Factory**: Components can be registered with the UVM factory mechanism, enabling dynamic object creation and lookup.
## Class Hierarchy
![image](https://github.com/user-attachments/assets/1d23f787-a9eb-4a36-bc3e-6d0773ed5038)  
All major verification testbench components like drivers, monitors, and scoreboards are derivatives of the uvm_component class and inherit standard phasing and reporting mechanisms of the UVM framework.

UVM components **use the phasing mechanism** to perform **initialization** and **configuration** tasks in a specific order. Phases allow components to **construct their internal hierarchy**, **connect to other components**, and **finalize their configurations** before the actual test starts. This ensures a well-structured setup and configuration process.  
![image](https://github.com/user-attachments/assets/26275d2c-ef37-4680-b5db-c7b115e48cd8)
## Class Declaration
```
virtual class uvm_component extends uvm_report_object;
```
uvm_component class definition provides many functions and tasks that are used to **find**, **build**, **connect**, and **configure sub-components**. They are broadly categorized into those which support **navigating the component hierarchy**, controlling the **phases that govern how a testbench should be built and run**, and **allowing reusability of testbench using a factory**.
## Hierarchy Methods
```
// Get handle to parent uvm component that instantiated current component
        extern virtual function uvm_component get_parent ();

// Get full hierarchical name of the current component
        extern virtual function string get_full_name ();

// Get queue of all children instantiated under current component, not nested
 	extern function void get_children(ref uvm_component children[$]);

// Get handle to a child by the given name
 	extern function uvm_component get_child (string name);

// Used in an iterable to get the next child component handle
  	extern function int get_next_child (ref string name);

// Get the first child handle under current component
  	extern function int get_first_child (ref string name);

// Get total number of child components, not nested
  	extern function int get_num_children ();

// Returns 1 if there is atleast one component instantiated
  	extern function int has_child (string name);

// Get nested child component handle by hierarchical path
  	extern function uvm_component lookup (string name);

// Depth of the current component from uvm_top=0, uvm_test=1, etc
  	extern function int unsigned get_depth();
```
以下有個 apb example
![image](https://github.com/user-attachments/assets/763d44b1-010b-469e-add6-653eb175edba)
```
class apb_monitor extends uvm_component;

class apb_agent extends uvm_component;		// class apb_agent 內有個 apb_monitor member
	apb_monitor	 	m_apb_monitor;
endclass

class child_comp extends uvm_component;

class top_comp extends uvm_component;

	// Child component instantiations
	child_comp 		m_child_comp_sa [5];
	apb_agent 		m_apb_agent;


  	virtual function void end_of_elaboration_phase(uvm_phase phase);

		// Local variables to hold temporary results
    		uvm_component 	l_comp_h;
    		uvm_component 	l_comp_q [$];

		// Get parent and print it
    		l_comp_h = get_parent();
    		`uvm_info ("tag", $sformatf("get_parent=%s", l_comp_h.get_name()), UVM_LOW)

		// Get all children and print them
    		get_children(l_comp_q);
    		foreach (l_comp_q[i])
      			`uvm_info ("tag", $sformatf("child_%0d = %s", i, l_comp_q[i].get_name()), UVM_LOW)

    		// Get a specific child component and print name
    		l_comp_h = get_child("m_child_comp_2");
    		`uvm_info ("tag", $sformatf("Found %s", l_comp_h.get_name()), UVM_LOW)

		// Other function calls
    		`uvm_info ("tag", $sformatf("number of children = %0d", get_num_children()), UVM_LOW)
	    	`uvm_info ("tag", $sformatf("has_child('abc') = %0d", has_child("abc")), UVM_LOW)
    		`uvm_info ("tag", $sformatf("has_child('m_apb_agent') = %0d", has_child("m_apb_agent")), UVM_LOW)
    		`uvm_info ("tag", $sformatf("get_depth = %0d", get_depth()), UVM_LOW)

		// Lookup failure will result in a warning
    		l_comp_h = lookup("m_apb_monitor");
    		if (l_comp_h)
      			`uvm_info ("tag", $sformatf("Found %s", l_comp_h.get_full_name()), UVM_LOW)

		// Lookup requires full hierarchical path to the component
      		l_comp_h = lookup("m_apb_agent.m_apb_monitor");
    		if (l_comp_h)
      			`uvm_info ("tag", $sformatf("Found %s", l_comp_h.get_full_name()), UVM_LOW)

  	endfunction
endclass
```
輸出
```
UVM_INFO @ 0: reporter [RNTST] Running test my_test...
UVM_INFO testbench.sv(67) @ 0: uvm_test_top.m_top_comp [tag] get_parent=uvm_test_top
UVM_INFO testbench.sv(71) @ 0: uvm_test_top.m_top_comp [tag] child_0 = m_apb_agent
UVM_INFO testbench.sv(71) @ 0: uvm_test_top.m_top_comp [tag] child_1 = m_child_comp_0
UVM_INFO testbench.sv(71) @ 0: uvm_test_top.m_top_comp [tag] child_2 = m_child_comp_1
UVM_INFO testbench.sv(71) @ 0: uvm_test_top.m_top_comp [tag] child_3 = m_child_comp_2
UVM_INFO testbench.sv(71) @ 0: uvm_test_top.m_top_comp [tag] child_4 = m_child_comp_3
UVM_INFO testbench.sv(71) @ 0: uvm_test_top.m_top_comp [tag] child_5 = m_child_comp_4
UVM_INFO testbench.sv(75) @ 0: uvm_test_top.m_top_comp [tag] Found m_child_comp_2
UVM_INFO testbench.sv(77) @ 0: uvm_test_top.m_top_comp [tag] number of children = 6
UVM_INFO testbench.sv(79) @ 0: uvm_test_top.m_top_comp [tag] has_child('abc') = 0
UVM_INFO testbench.sv(80) @ 0: uvm_test_top.m_top_comp [tag] has_child('m_apb_agent') = 1
UVM_INFO testbench.sv(81) @ 0: uvm_test_top.m_top_comp [tag] get_depth = 2
UVM_WARNING /xcelium20.09/tools//methodology/UVM/CDNS-1.2/sv/src/base/uvm_component.svh(2017) @ 0: uvm_test_top.m_top_comp [Lookup Error] Cannot find child m_apb_monitor
UVM_INFO testbench.sv(89) @ 0: uvm_test_top.m_top_comp [tag] Found uvm_test_top.m_top_comp.m_apb_agent.m_apb_monitor
```
## Phasing Methods
Components provide virtual methods for each UVM phase that can be overridden by child classes to implement functionality. For example, all testbench components are instantiated in their respective build_phase, connected in connect_phase and simulated in run_phase. There are a lot more pre-defined UVM phases that can be used to implement functionality.
```
// This child class implements only build_phase and connect_phase methods
// of uvm_component, while rest of the phase methods are left untouched and
// depends on their definitions inside uvm_component

class apb_agent extends uvm_component;

	...
	apb_monitor 	m_monitor;
	apb_driver 		m_driver;
	apb_sequencer 	m_seqr;

	// All children of this component are instantiated in build_phase
	virtual function void build_phase(uvm_phase phase);
		super.build_phase(phase);

		// obj_type::type_id::create is a way to get an object of
		// the type "obj_type" from the factory

		m_monitor 	= apb_monitor::type_id::create("m_monitor", this);
		m_driver 	= apb_driver::type_id::create("m_driver", this);
		m_seqr 		= apb_sequencer::type_id::create("m_seqr", this);
	endfunction

	// Child components can be connected together in connect_phase
	virtual function void connect_phase(uvm_phase phase);
		super.connect_phase(phase);

		// Connect sequencer with driver
		m_driver.seq_item_port.connect(m_seqr.seq_item_export);
	endfunction

endclass
```
## Factory Methods
Components are registered with the factory using a specific macro intended to be used only by components. Note that UVM object class definitions use the macro `uvm_object_utils.
```
class my_comp extends uvm_component;

	// Register with factory
	`uvm_component_utils (my_comp)

	function new(string name = "my_comp", uvm_component parent = null);
		super.new(name, parent);
	endfunction

	...

endclass
```
Factory is a singleton object and there is only one instance of the factory in a UVM environment. uvm_component provide a set of convenience functions that call the uvm_factory member functions with a simplified interface.
```
// For example, "set_type_override_by_type" is actually a function defined in the class uvm_factory
// A wrapper function with the same name is defined in uvm_component class and arguments are passed
// to the uvm_factory function call

function void uvm_component::set_type_override_by_type (uvm_object_wrapper original_type,
                                                        uvm_object_wrapper override_type,
                                                        bit    replace=1);

	// Get handle to the factory instance in UVM environment
	uvm_coreservice_t cs = uvm_coreservice_t::get();
  	uvm_factory factory = cs.get_factory();

	// Pass the same arguments to the factory function call
   	factory.set_type_override_by_type(original_type, override_type, replace);
endfunction

// Usage : "m_comp" is a uvm_component class handle
m_comp.set_type_override_by_type(apb_driver::get_type(), apb_driver_2::get_type());
```
