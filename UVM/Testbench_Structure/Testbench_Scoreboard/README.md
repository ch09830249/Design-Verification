# UVM Scoreboard
![image](https://github.com/user-attachments/assets/e0de14ff-2270-4605-b429-9c10e7e9c06b)
* UVM scoreboard is a verification component that contains checkers and verifies the functionality of a design. It usually receives transaction level objects captured from the interfaces of a DUT via TLM Analysis Ports. (Monitor)
* Reference Model:
   * After receiving data objects, it can either perform calculations and predict the expected value or send it to a reference model to get expected values. The reference model is also called a predictor and would mimic the functionality of the design. The final task is to compare expected results with the actual output data from DUT.

**PS**: It is recommended to inherit from **uvm_scoreboard** than **uvm_component** so that any additions to uvm_scoreboard class in a future release of UVM will automatically be included in the custom UVM scoreboard when you switch to the newer version.
# 建立 UVM Scoreboard 的步驟
* Create a custom class inherited from uvm_scoreboard, register with factory and call function new
```
// my_scoreboard is user-given name for this class that has been derived from "uvm_scoreboard"
class my_scoreboard extends uvm_scoreboard;   // 新版 UVM 未來會有 uvm_scoreboard

    // [Recommended] Makes this scoreboard more re-usable
    `uvm_component_utils (my_scoreboard)

    // This is standard code for all components
    function new (string name = "my_scoreboard", uvm_component parent = null);
      super.new (name, parent);
    endfunction

    // Code for rest of the steps come here
endclass
```
* Add necessary TLM exports to receive transactions from other components and instantiat them in build_phase
```
// Step2: Declare and create a TLM Analysis Port to receive data objects from other TB components
uvm_analysis_imp #(apb_pkt, my_scoreboard) ap_imp;   // 宣告一個 import handle, 以接收來自其他 components 傳來的資料

// Instantiate the analysis port, because afterall, its a class object
function void build_phase (uvm_phase phase);   // 並在 build phase 實例化
	ap_imp = new ("ap_imp", this);
endfunction
```
* Define the action to be taken when data is received from the analysis port
```
// Step3: Define action to be taken when a packet is received via the declared analysis port
virtual function void write (apb_pkt data);
	// What should be done with the data packet received comes here - let's display it
	`uvm_info ("write", $sformatf("Data received = 0x%0h", data), UVM_MEDIUM)
endfunction
```
* Perform checks
```
// Step4: [Optional] Perform any remaining comparisons or checks before end of simulation
virtual function void check_phase (uvm_phase phase);
	...
endfunction
```
* Connect Analysis ports of scoreboard with other components in the environment
```
class my_env extends uvm_env;
	...

	// Step5: Connect the analysis port of the scoreboard with the monitor so that
	// the scoreboard gets data whenever monitor broadcasts the data.
	virtual function void connect_phase (uvm_phase phase);
		super.connect_phase (phase);
		m_apb_agent.m_apb_mon.analysis_port.connect (m_scbd.ap_imp);
	endfunction
endclass
```
# UVM Scoreboard Example
```
// Step1 : Create a new class that extends from uvm_scoreboard
class my_scoreboard extends uvm_scoreboard;
	`uvm_component_utils (my_scoreboard)

	function new (string name = "my_scoreboard", uvm_component parent);
		super.new (name, parent);
	endfunction

	// Step2a: Declare and create a TLM Analysis Port to receive data objects from other TB components
	uvm_analysis_imp #(apb_pkt, my_scoreboard) ap_imp;

	// Step2b: Instantiate the analysis port, because afterall, its a class object
	function void build_phase (uvm_phase phase);
		ap_imp = new ("ap_imp", this);
	endfunction

	// Step3: Define action to be taken when a packet is received via the declared analysis port
	virtual function void write (apb_pkt data);
		// What should be done with the data packet received comes here - let's display it
		`uvm_info ("write", $sformatf("Data received = 0x%0h", data), UVM_MEDIUM)
	endfunction

	// Step3: Define other functions and tasks that operate on the data and call them
	// Remember, this is the main task that consumes simulation time in UVM
	virtual task run_phase (uvm_phase phase);
		...
	endtask

	// Step4: [Optional] Perform any remaining comparisons or checks before end of simulation
	virtual function void check_phase (uvm_phase phase);
		...
	endfunction
endclass
```
