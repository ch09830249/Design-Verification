# Driver Sequencer Handshake
* The **driver** class contains a TLM port called **uvm_seq_item_pull_port** which is connected to a **uvm_seq_item_pull_export** in the **sequencer** in the connect phase of a UVM agent. The driver can use TLM functions to get the next item from the sequencer when required.
* These API methods help the driver to **get a series of sequence_items from the sequencer's FIFO** that contains data for the driver to drive to the DUT. Also, there is a way for the driver to communicate back with the sequence that it has finished driving the given sequence item and can request for the next item.
![image](https://github.com/user-attachments/assets/2324d4bd-4459-4a06-bd12-c6c0a3b2d82a)
```
class my_agent extends uvm_agent;
	`uvm_component_utils (my_agent)

	my_driver  		#(my_sequence_item) 	m_drv;
	uvm_sequencer 	#(my_sequence_item)  	m_seqr;

	virtual function void connect_phase (uvm_phase phase);
		// Always the port is connected to an export
		m_drv.seq_item_port.connect(m_seqr.seq_item_export);   // 在 agent 中, driver 的 seq_item_port (本質上是 port) 和 sequencer 的 export (本質上是 import) 相連
	endfunction

endclass
```
The connect between a driver and sequencer is a **one-to-one connection**. Multiple drivers are not connected to a sequencer nor are multiple sequencers connected to a single driver. Once the connection is made, the driver can utilize API calls in the TLM port definitions to receive sequence items from the sequencer.
