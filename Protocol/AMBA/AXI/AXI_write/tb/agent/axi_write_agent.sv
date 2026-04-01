class axi_write_agent extends uvm_agent;
  `uvm_component_utils(axi_write_agent)

  axi_write_driver driver;
  uvm_sequencer #(axi_write_transaction) sequencer;

  function new(string name = "axi_write_agent", uvm_component parent = null);  
    super.new(name, parent);
  endfunction

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    sequencer = uvm_sequencer #(axi_write_transaction)::type_id::create("sequencer", this);
    driver    = axi_write_driver::type_id::create("driver", this);
  endfunction

  function void connect_phase(uvm_phase phase);
    driver.seq_item_port.connect(sequencer.seq_item_export);    // driver 和 sequencer port 連接 
  endfunction
endclass
