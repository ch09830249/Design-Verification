class ahb_read_agent extends uvm_agent;
  `uvm_component_utils(ahb_read_agent)

  ahb_read_driver   drv;
  ahb_read_monitor  mon;
  uvm_sequencer #(ahb_transaction) seqr;

  function new(string name, uvm_component parent);
    super.new(name, parent);
  endfunction

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    drv = ahb_read_driver::type_id::create("drv", this);
    mon = ahb_read_monitor::type_id::create("mon", this);
    seqr = uvm_sequencer #(ahb_transaction)::type_id::create("seqr", this);
  endfunction

  function void connect_phase(uvm_phase phase);
    drv.seq_item_port.connect(seqr.seq_item_export);
  endfunction
endclass
