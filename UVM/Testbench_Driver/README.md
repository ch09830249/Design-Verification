# UVM Driver
* UVM Driver 知道如何將訊號透過 interface 來驅動 design。所有 Driver 程式類別都應該從 uvm_driver 擴展，無論是直接還是間接。
交易級物件從序列器獲得，UVM 驅動程式透過介面句柄將它們驅動到設計中。
# Class Hierarchy  
![image](https://github.com/user-attachments/assets/9715f947-fdff-45c9-ab61-adcf041694e2)
# 建立 UVM Driver 的步驟
* Create custom class inherited from **uvm_driver**, register with factory and call new   (跟前面組件的都相同)
```
// my_driver is user-given name for this class that has been derived from "uvm_driver"
class my_driver extends uvm_driver;

  	// [Recommended] Makes this driver more re-usable
  	`uvm_component_utils (my_driver)

  	// This is standard code for all components
  	function new (string name = "my_driver", uvm_component parent = null);
    	super.new (name, parent);
  	endfunction

  	// Code for rest of the steps come here
endclass
```
* Declare virtual interface handle and get them in build phase
```
// Actual interface object is later obtained by doing a get() call on uvm_config_db
  	virtual if_name vif;

  	virtual function void build_phase (uvm_phase phase);
  		super.build_phase (phase);
     	if (! uvm_config_db #(virtual if_name) :: get (this, "", "vif", vif)) begin
        	`uvm_fatal (get_type_name (), "Didn't get handle to virtual interface if_name")
     	end
endfunction
```
* Code the run_phase
```
// This is the main piece of driver code which decides how it has to translate
// transaction level objects into pin wiggles at the DUT interface
virtual task run_phase (uvm_phase phase);
	// Loop the following steps
	// 1. Get next item from the sequencer				// 從 sequencer 取出下一筆 transaction
	// 2. Assign data from the received item into DUT interface	// 從 transaction 取出 data 並指定給 DUT interface
	// 3. Finish driving transaction
endtask
```
![image](https://github.com/user-attachments/assets/831d28f9-2160-4fbb-a330-93c5206b4b24)
# Driver-Sequencer Handshaking
* UVM Driver 是一個參數化的類別，可以驅動特定類型的事務物件。Driver 有一個 TLM port 叫 uvm_seq_item_pull_port，可以接受來自 uvm_sequencer 的參數化請求物件。它還可以向 sequencer 傳回一個回應對象，並且通常請求和回應項的類別類型是相同的。但是，如果明確指定，它們可以不同。
| Method Name | Description |
| :-----| :---- |
| get_next_item | Blocks until a request item is available from the sequencer. This should be followed by item_done call to complete the handshake. |
| try_next_item | Non-blocking method which will return null if a request object is not available from the sequencer. Else it returns a pointer to the object. |
| item_done | Non-blocking method which completes the driver-sequencer handshake. This should be called after get_next_item or a successful try_next_item call. |
