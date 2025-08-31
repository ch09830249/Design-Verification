class ahb_agent extends uvm_agent;
  `uvm_component_utils(ahb_agent)

  ahb_driver driver;

  function new(string name, uvm_component parent);
    super.new(name, parent);
  endfunction

  function void build_phase(uvm_phase phase);
    driver = ahb_driver::type_id::create("driver", this);
  endfunction
endclass
