class ahb_write_env extends uvm_env;
  `uvm_component_utils(ahb_write_env)

  ahb_write_agent agent;

  function new(string name, uvm_component parent);
    super.new(name, parent);
  endfunction

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    agent = ahb_write_agent::type_id::create("agt", this);
  endfunction
endclass
