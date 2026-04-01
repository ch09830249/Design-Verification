class axi_read_agent extends uvm_agent;
  `uvm_component_utils(axi_read_agent)

  axi_read_driver driver;
  axi_read_monitor monitor;
  uvm_sequencer #(axi_read_transaction) sequencer;

  function new(string name = "axi_read_agent", uvm_component parent = null);  
    super.new(name, parent);
  endfunction

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    sequencer = uvm_sequencer #(axi_read_transaction)::type_id::create("sequencer", this);
    driver    = axi_read_driver::type_id::create("driver", this);
    monitor   = axi_read_monitor::type_id::create("monitor", this);
  endfunction

  function void connect_phase(uvm_phase phase);
    driver.seq_item_port.connect(sequencer.seq_item_export);    
  endfunction
endclass
