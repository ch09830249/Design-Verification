class ahb_read_env extends uvm_env;
  `uvm_component_utils(ahb_read_env)

  ahb_read_agent agent;

  function new(string name, uvm_component parent);
    super.new(name, parent);
  endfunction

  function void build_phase(uvm_phase phase);
    agent = ahb_read_agent::type_id::create("agent", this);
  endfunction
endclass
