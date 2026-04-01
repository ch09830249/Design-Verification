class tlul_put_agent extends uvm_agent;
  `uvm_component_utils(tlul_put_agent)

  tlul_put_sequencer sequencer;
  tlul_put_driver    driver;
  tlul_put_monitor   monitor;

  function new(string name, uvm_component parent);
    super.new(name, parent);
  endfunction

  virtual function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    sequencer = tlul_put_sequencer::type_id::create("sequencer", this);
    driver    = tlul_put_driver   ::type_id::create("driver", this);
    monitor   = tlul_put_monitor  ::type_id::create("monitor", this);
  endfunction

  virtual function void connect_phase(uvm_phase phase);
    super.connect_phase(phase);
    driver.seq_item_port.connect(sequencer.seq_item_export);
  endfunction
endclass
