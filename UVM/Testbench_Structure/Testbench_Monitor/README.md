# UVM Monitor
![image](https://github.com/user-attachments/assets/88e603dc-e4b2-4c70-9494-750b3c87f78d)
*  
# Class Hierarchy
![image](https://github.com/user-attachments/assets/90b72adf-b51b-48b1-8e1d-8df66bd50969)
# 建立 UVM Monitor 的步驟
* Create custom class inherited from **uvm_monitor**, register with factory and call new
```
// my_monitor is user-given name for this class that has been derived from "uvm_monitor"
class my_monitor extends uvm_monitor;

	// [Recommended] Makes this monitor more re-usable
	`uvm_component_utils (my_monitor)

	// This is standard code for all components
	function new (string name = "my_monitor", uvm_component parent = null);
		super.new (name, parent);
	endfunction

	// Rest of the steps come here
endclass
```
* Declare analysis ports and virtual interface handles
```
// Actual interface object is later obtained by doing a get() call on uvm_config_db
virtual if_name vif;   // 用 virtual interface 去接

// my_data is a custom class object used to encapsulate signal information
// and can be sent to other components
uvm_analysis_port  #(my_data) mon_analysis_port;   // 宣告 analysis ports 將接收到的資料 broadcast 出去
```
* Build the UVM monitor
```
virtual function void build_phase (uvm_phase phase);
   super.build_phase (phase);

   // Create an instance of the declared analysis port
   mon_analysis_port = new ("mon_analysis_port", this);      // 實例化 analysis port

   // Get virtual interface handle from the configuration DB
   if (! uvm_config_db #(virtual if_name) :: get (this, "", "vif", vif)) begin      // 去接 DUT 的 interface
      `uvm_error (get_type_name (), "DUT interface not found")
   end
endfunction
```
* Code the run_phase
```
// This is the main piece of monitor code which decides how it has to decode
// signal information. For example, AXI monitors need to follow AXI protocol
virtual task run_phase (uvm_phase phase);

	// Fork off multiple threads "if" required to monitor the interface,  for example:
	fork
		// Thread 1: Monitor address channel
		// Thread 2: Monitor data channel, populate "obj" data object
		// Thread 3: Monitor control channel, decide if transaction is over

		// Thread 4: When data transfer is complete, send captured information
	 	// through the declared analysis port
		mon_analysis_port.write(obj);
	join_none
endtask
```
# UVM Monitor Example
* Virtual interface handle is declared as vif and assigned from UVM database via uvm_config_db::get()
* Additional knobs are provided for enabling/disabling protocol checker (enable_check) and coverage (enable_coverage)
* Coverage group defined as cg_trans and will be sampled during run phase (該 cover group 定義在 class my_data 中)
* During run_phase(), data from interface is captured into local class object, protocol check is performed when enabled, and coverage group is sampled when enabled
* Data object class is broadcast to other verification components via the analysis port (廣播給 refernce model 去計算 Expected value)
* The knobs can be disabled from the test by using UVM database. (在 Test 層, 設置 configuration 可以決定是否檢查 protocol 或是 functional coverage 計算)
```
uvm_config_db #(bit) :: set (this, "*.agt0.monitor", "enable_check", 0);
uvm_config_db #(bit) :: set (this, "*.agt0.monitor", "enable_coverage", 0);
```
```
class my_monitor extends uvm_monitor;
   `uvm_component_utils (my_monitor)

   virtual dut_if   vif;
   bit              enable_check = 1;

   uvm_analysis_port #(my_data)   mon_analysis_port;

   function new (string name, uvm_component parent= null);
      super.new (name, parent);
   endfunction

   virtual function void build_phase (uvm_phase phase);
      super.build_phase (phase);

      // Create an instance of the analysis port
      mon_analysis_port = new ("mon_analysis_port", this);

      // Get virtual interface handle from the configuration DB
      if (! uvm_config_db #(virtual dut_if) :: get (this, "", "vif", vif)) begin
         `uvm_error (get_type_name (), "DUT interface not found")
      end
   endfunction

   virtual task run_phase (uvm_phase phase);
      my_data  data_obj = my_data::type_id::create ("data_obj", this);      // 建立一個暫存收到 data 的物件
      forever begin                                                         // Infinite loop 去監聽
         @ ([Some event when data at DUT port is valid]);                   // 等到某些 event 發生才去取 DUT output
         data_obj.data = vif.data;
         data_obj.addr = vif.addr;

         // 這裡有兩個開關
         // If protocol checker is enabled, perform checks
         if (enable_check)
            check_protocol ();

         // Sample functional coverage if required. Data packet class is assumed
         // to have functional covergroups and bins
         if (enable_coverage)
           data_obj.cg_trans.sample();   // sample 該值去計算 funtional coverage

         // Send data object through the analysis port
         mon_analysis_port.write (data_obj);   // 將收到的 data 傳給 reference model 去計算
      end
   endtask

   virtual function void check_protocol ();
      // Function to check basic protocol specs
   endfunction
endclass
```
