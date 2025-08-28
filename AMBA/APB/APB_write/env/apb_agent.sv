class apb_agent extends uvm_agent;
  `uvm_component_utils(apb_agent)

  apb_driver driver;

  function new(string name, uvm_component parent);
    super.new(name, parent);
  endfunction

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    driver = apb_driver::type_id::create("apb_driver", this);
  endfunction
endclass
