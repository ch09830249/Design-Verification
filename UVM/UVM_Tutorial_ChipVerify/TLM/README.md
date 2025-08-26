# TLM (Transaction Level Modeling)
## Blocking Put Port 
A uvm_blocking_put_port TLM port was blocking in nature where the sender gets **stalled until the receiver finishes with the put task.**
![image](https://github.com/user-attachments/assets/2b67328b-a7c7-4c27-9718-623a622f1edd)
* Transaction
```
// Create a class data object that can be sent from one
// component to another
class Packet extends uvm_object;
  rand bit[7:0] addr;
  rand bit[7:0] data;

  `uvm_object_utils_begin(Packet)
  	`uvm_field_int(addr, UVM_ALL_ON)
  	`uvm_field_int(data, UVM_ALL_ON)
  `uvm_object_utils_end

  function new(string name = "Packet");
    super.new(name);
  endfunction
endclass
```
* Create **sender** class with a port of type uvm_blocking_put_port
```
class componentA extends uvm_component;
   `uvm_component_utils (componentA)

   // Create a blocking TLM put port which can send an object
   // of type 'Packet'
   uvm_blocking_put_port #(Packet) m_put_port;		// blocking 就是要送完才能結束, 這裡建立端口的 handle, 用於傳輸 Packet
   int m_num_tx;

   function new (string name = "componentA", uvm_component parent= null);
      super.new (name, parent);
   endfunction

   // Remember that TLM put_port is a class object and it will have to be
   // created with new ()
   virtual function void build_phase (uvm_phase phase);
      super.build_phase (phase);
      m_put_port = new ("m_put_port", this);		// 實例化該端口
   endfunction

   // Create a packet, randomize it and send it through the port
   // Note that put() is a method defined by the receiving component
   // Repeat these steps N times to send N packets
   virtual task run_phase (uvm_phase phase);
     phase.raise_objection(this);
     repeat (m_num_tx) begin
         Packet pkt = Packet::type_id::create ("pkt");		// 建立欲傳輸的 Packet 並隨機其變數
         assert(pkt.randomize ());

       	 // Print the packet to be displayed in log
         `uvm_info ("COMPA", "Packet sent to CompB", UVM_LOW)
         pkt.print (uvm_default_line_printer);

         // Call the TLM put() method of put_port class and pass packet as argument
         m_put_port.put (pkt);					// 這裡透過端口傳輸 Packet
      end
      phase.drop_objection(this);
   endtask
endclass
```
* Create **receiver** class that implements the put method
```
class componentB extends uvm_component;
   `uvm_component_utils (componentB)

   // Declare a put implementation port to accept transactions
   uvm_blocking_put_imp #(Packet, componentB) m_put_imp;	// 宣告 import, 參數1: 欲傳輸類型, 參數2: 接收的組件

   function new (string name = "componentB", uvm_component parent = null);
      super.new (name, parent);
   endfunction

   virtual function void build_phase (uvm_phase phase);
      super.build_phase (phase);
      m_put_imp = new ("m_put_imp", this);			// 實例化
   endfunction

    // Implementation of the 'put()' method in this case simply prints it.
   virtual task put (Packet pkt);				// 需實作 put task
      `uvm_info ("COMPB", "Packet received from CompA", UVM_LOW)
      pkt.print(uvm_default_line_printer);
   endtask
endclass
```
* Connect port and its implementation at a higher level (需要在 high level 連接的原因是該組件會在 high level 被實例化)
```
class my_test extends uvm_test;
  `uvm_component_utils (my_test)

   componentA compA;
   componentB compB;

   function new (string name = "my_test", uvm_component parent = null);
      super.new (name, parent);
   endfunction

   // Create objects of both components, set number of transfers
   virtual function void build_phase (uvm_phase phase);
      super.build_phase (phase);
      compA = componentA::type_id::create ("compA", this);
      compB = componentB::type_id::create ("compB", this);
      compA.m_num_tx = 2;
   endfunction

   // Connection between componentA and componentB is done here
   // Note that the "put_port" is connected to its implementation "put_imp"
   virtual function void connect_phase (uvm_phase phase);
     compA.m_put_port.connect (compB.m_put_imp);		// 在 test case 層, 連接兩個端口
   endfunction
endclass
```
## Nonblocking Put Port 
* **try_put** to see if the put was successful
* **can_put** method to see if the receiver is ready to accept a transfer.
* Create sender class with a port of type uvm_nonblocking_put_port
```
class componentA extends uvm_component;
   `uvm_component_utils (componentA)

   // Create a nonblocking TLM put port which can send an object
   // of type 'Packet'
   uvm_nonblocking_put_port #(Packet) m_put_port;	// 建立端口 handle
   int m_num_tx;

   function new (string name = "componentA", uvm_component parent= null);
      super.new (name, parent);
   endfunction

   // Remember that TLM put_port is a class object and it will have to be
   // created with new ()
   virtual function void build_phase (uvm_phase phase);
      super.build_phase (phase);
      m_put_port = new ("m_put_port", this);		// 實例化該端口
   endfunction

  // Create a packet, randomize it and send it through the port
  // Note that put() is a method defined by the receiving component
  // Repeat these steps N times to send N packets
   virtual task run_phase (uvm_phase phase);
     phase.raise_objection(this);
     repeat (m_num_tx) begin
        bit success;
         Packet pkt = Packet::type_id::create ("pkt");
         assert(pkt.randomize ());

         // Print the packet to be displayed in log
         `uvm_info ("COMPA", "Packet sent to CompB", UVM_LOW)
         pkt.print (uvm_default_line_printer);

	// Try to put the packet through the put port
	success = m_put_port.try_put(pkt);		// 這裡用 try_put 來傳送
	if (success)
           `uvm_info("COMPA", $sformatf("COMPB was ready to accept and transfer is successful"), UVM_MEDIUM)
	else
           `uvm_info("COMPA", $sformatf("COMPB was NOT ready to accept and transfer failed"), UVM_MEDIUM)
      end
     phase.drop_objection(this);
   endtask
endclass
```
* Create receiver class that implements the put method
```
class componentB extends uvm_component;
   `uvm_component_utils (componentB)

   // Mention type of transaction, and type of class that implements the put ()
   uvm_nonblocking_put_imp #(Packet, componentB) m_put_imp;	// 建立端口的 handle

   function new (string name = "componentB", uvm_component parent = null);
      super.new (name, parent);
   endfunction

   virtual function void build_phase (uvm_phase phase);
      super.build_phase (phase);
      m_put_imp = new ("m_put_imp", this);			// 實例化該端口
   endfunction

   // 'try_put' method definition accepts the packet and prints it.
   // Note that it should return 1 if successful so that componentA
   // knows how to handle the transfer return code
   virtual function bit try_put (Packet pkt);			// 這裡要實作 try_put, 這邊只是把 packet 印出來, 然後 return 1
     `uvm_info ("COMPB", "Packet received", UVM_LOW)
      pkt.print(uvm_default_line_printer);
      return 1;
   endfunction

   virtual function bit can_put();				// can_put 不實作
   endfunction

endclass
```
* Connect port and its implementation at a higher level
```
class my_test extends uvm_test;
  `uvm_component_utils (my_test)

   componentA compA;
   componentB compB;

  function new (string name = "my_test", uvm_component parent = null);
      super.new (name, parent);
   endfunction

     // Create objects of both components, set number of transfers
   virtual function void build_phase (uvm_phase phase);
      super.build_phase (phase);
      compA = componentA::type_id::create ("compA", this);
      compB = componentB::type_id::create ("compB", this);
      compA.m_num_tx = 2;
   endfunction

   // Connection between componentA and componentB is done here
   // Note that the "put_port" is connected to its implementation "put_imp"
   virtual function void connect_phase (uvm_phase phase);
     compA.m_put_port.connect (compB.m_put_imp);
   endfunction

  virtual function void end_of_elaboration_phase(uvm_phase phase);
    super.end_of_elaboration_phase(phase);
    uvm_top.print_topology();
  endfunction
endclass
```
## Nonblock Behavior
## 可以透過 do while 和 try_put 來實作
* Sender
```
class componentA extends uvm_component;
   `uvm_component_utils (componentA)

   // Rest of the code remains same

   virtual task run_phase (uvm_phase phase);
     phase.raise_objection(this);
     repeat (m_num_tx) begin
        bit success;
         Packet pkt = Packet::type_id::create ("pkt");
         assert(pkt.randomize ());

        // Print the packet to be displayed in log
         `uvm_info ("COMPA", "Packet sent to CompB", UVM_LOW)
         pkt.print (uvm_default_line_printer);

       // do-while loop uses a "try_put" to keep the sender blocked until the receiver is ready. Return
       // type of the try_put indicates if the transfer was successful. So, lets just try putting
       // the same packet until the receiver returns a 1 indicating successful transfer.
       // Note that this is the same as using "put" but we are doing it with "try_put" and a loop
       do begin					// 這邊透過 do while 一直 try_put, 直到成功才跳出迴圈
         success = m_put_port.try_put(pkt);
         if (success)
           `uvm_info("COMPA", $sformatf("COMPB was ready to accept and transfer is successful"), UVM_MEDIUM)
         else
           `uvm_info("COMPA", $sformatf("COMPB was NOT ready to accept and transfer failed, try after 1ns"), UVM_MEDIUM)
         #1;
       end while (!success);
      end
     phase.drop_objection(this);
   endtask
endclass
```
* Receiver
```
class componentB extends uvm_component;
   `uvm_component_utils (componentB)

  // Rest of the code remains same

  // 'try_put' method definition accepts the packet and prints it.
  // Note that it should return 1 if successful so that componentA
  // knows how to handle the transfer return code
  // For purpose of example, lets randomize a variable
  // just to say that this component is ready or not
  virtual function bit try_put (Packet pkt);	這裡只是隨機產生接收或不接收的狀態
    bit ready;
    std::randomize(ready);

    if (ready) begin
      `uvm_info ("COMPB", "Packet received", UVM_LOW)
      pkt.print(uvm_default_line_printer);
      return 1;
    end else begin
    	return 0;
    end
  endfunction

  virtual function bit can_put();
  endfunction
endclass
```
## 也可以透過 do while, can_put, try_put 來實作
* **Sender**
```
class componentA extends uvm_component;
   `uvm_component_utils (componentA)

   // Rest of the code remains same

   virtual task run_phase (uvm_phase phase);
     phase.raise_objection(this);
     repeat (m_num_tx) begin
        bit success;
         Packet pkt = Packet::type_id::create ("pkt");
         assert(pkt.randomize ());

        // Print the packet to be displayed in log
         `uvm_info ("COMPA", "Packet sent to CompB", UVM_LOW)
         pkt.print (uvm_default_line_printer);

       	// Another way to do the same is to loop until can_put returns a 1. In this case, its is
       	// not even attempted to send a transaction using put, until the sender knows for sure
       	// that the receiver is ready to accept it
       	`uvm_info("COMPA", $sformatf("Waiting for receiver to be ready ..."), UVM_MEDIUM)
       	do begin
         	success = m_put_port.can_put();		// 看何時能 put, 可以 put 的時候跳出迴圈
       	end while (!success);
       	`uvm_info("COMPA", $sformatf("Receiver is now ready to accept transfers"), UVM_MEDIUM)
       	m_put_port.try_put(pkt);			// try_put Packet
      end
     phase.drop_objection(this);
   endtask
endclass
```
* **Receiver**
```
class componentB extends uvm_component;
   `uvm_component_utils (componentB)

  // Rest of the code remains same

  virtual function bit try_put (Packet pkt);
    `uvm_info ("COMPB", "Packet received", UVM_LOW)
    pkt.print(uvm_default_line_printer);
    return 1;
  endfunction

  // Return a random value to model readiness
  virtual function bit can_put();	// 隨機產生收或不收 data 的狀態
    return $urandom_range(0,1);
  endfunction
endclass
```
