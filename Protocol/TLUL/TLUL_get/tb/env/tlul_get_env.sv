class tlul_get_env extends uvm_env;
  `uvm_component_utils(tlul_get_env)

  tlul_get_agent agent;

  function new(string name, uvm_component parent);
    super.new(name, parent);
  endfunction

  virtual function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    agent = tlul_get_agent::type_id::create("agent", this);
  endfunction
endclass
